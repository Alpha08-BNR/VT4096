#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/ec.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/obj_mac.h>
#include <openssl/rand.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <signal.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Bytes = std::vector<unsigned char>;
using std::string;
using std::vector;
using std::runtime_error;

static const size_t DIM = 4096;
static const int COORD_BITS = 128;
static const size_t PAD = 256;

static Bytes B(const string& s) { return Bytes(s.begin(), s.end()); }
static Bytes cat(const Bytes& a, const Bytes& b) { Bytes r(a); r.insert(r.end(), b.begin(), b.end()); return r; }
static void wipe(Bytes& b) { if (!b.empty()) OPENSSL_cleanse(b.data(), b.size()); }
static long long nowMs() {
  return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
}

static string toHex(const unsigned char* p, size_t n) {
  static const char* d = "0123456789abcdef";
  string s(n * 2, '0');
  for (size_t i = 0; i < n; i++) { s[2 * i] = d[p[i] >> 4]; s[2 * i + 1] = d[p[i] & 15]; }
  return s;
}
static string toHex(const Bytes& b) { return toHex(b.data(), b.size()); }
static int hexVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  throw runtime_error("hex");
}
static Bytes fromHex(const string& s) {
  if (s.size() % 2) throw runtime_error("hex");
  Bytes o(s.size() / 2);
  for (size_t i = 0; i < o.size(); i++) o[i] = (unsigned char)(hexVal(s[2 * i]) << 4 | hexVal(s[2 * i + 1]));
  return o;
}

static string b64enc(const Bytes& b) {
  static const char* t = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  string o;
  size_t i = 0;
  for (; i + 2 < b.size(); i += 3) {
    unsigned v = b[i] << 16 | b[i + 1] << 8 | b[i + 2];
    o += t[v >> 18]; o += t[(v >> 12) & 63]; o += t[(v >> 6) & 63]; o += t[v & 63];
  }
  if (i + 1 == b.size()) {
    unsigned v = b[i] << 16;
    o += t[v >> 18]; o += t[(v >> 12) & 63]; o += "==";
  } else if (i + 2 == b.size()) {
    unsigned v = b[i] << 16 | b[i + 1] << 8;
    o += t[v >> 18]; o += t[(v >> 12) & 63]; o += t[(v >> 6) & 63]; o += '=';
  }
  return o;
}
static Bytes b64dec(const string& s) {
  Bytes o;
  unsigned v = 0;
  int bits = 0;
  for (char c : s) {
    int x;
    if (c >= 'A' && c <= 'Z') x = c - 'A';
    else if (c >= 'a' && c <= 'z') x = c - 'a' + 26;
    else if (c >= '0' && c <= '9') x = c - '0' + 52;
    else if (c == '+') x = 62;
    else if (c == '/') x = 63;
    else if (c == '=') break;
    else throw runtime_error("b64");
    v = v << 6 | x; bits += 6;
    if (bits >= 8) { bits -= 8; o.push_back((unsigned char)(v >> bits)); v &= (1u << bits) - 1; }
  }
  return o;
}

static BN_CTX* bnctx() { static thread_local BN_CTX* c = BN_CTX_new(); return c; }

struct Big {
  BIGNUM* p;
  Big() : p(BN_new()) {}
  Big(long long v) : p(BN_new()) {
    unsigned long long m = v < 0 ? 0ULL - (unsigned long long)v : (unsigned long long)v;
    BN_set_word(p, (BN_ULONG)(m >> 32));
    BN_lshift(p, p, 32);
    BN_add_word(p, (BN_ULONG)(m & 0xffffffffULL));
    if (v < 0) BN_set_negative(p, 1);
  }
  Big(const Big& o) : p(BN_dup(o.p)) {}
  Big(Big&& o) noexcept : p(o.p) { o.p = nullptr; }
  Big& operator=(const Big& o) { if (this != &o) BN_copy(p, o.p); return *this; }
  Big& operator=(Big&& o) noexcept { std::swap(p, o.p); return *this; }
  ~Big() { BN_free(p); }
};

static Big operator+(const Big& a, const Big& b) { Big r; BN_add(r.p, a.p, b.p); return r; }
static Big operator-(const Big& a, const Big& b) { Big r; BN_sub(r.p, a.p, b.p); return r; }
static Big operator*(const Big& a, const Big& b) { Big r; BN_mul(r.p, a.p, b.p, bnctx()); return r; }
static Big operator/(const Big& a, const Big& b) { Big q, m; BN_div(q.p, m.p, a.p, b.p, bnctx()); return q; }
static Big operator%(const Big& a, const Big& b) { Big q, m; BN_div(q.p, m.p, a.p, b.p, bnctx()); return m; }
static Big neg(const Big& a) { Big r(a); if (!BN_is_zero(r.p)) BN_set_negative(r.p, !BN_is_negative(r.p)); return r; }
static Big shl(const Big& a, int n) { Big r; BN_lshift(r.p, a.p, n); return r; }
static Big shr(const Big& a, int n) { Big r; BN_rshift(r.p, a.p, n); return r; }
static int cmp(const Big& a, const Big& b) { return BN_cmp(a.p, b.p); }
static bool isNeg(const Big& a) { return BN_is_negative(a.p) != 0; }
static bool isZero(const Big& a) { return BN_is_zero(a.p) != 0; }

static string toDec(const Big& a) {
  char* s = BN_bn2dec(a.p);
  string r(s);
  OPENSSL_free(s);
  return r;
}
static Big fromDec(const string& s) {
  Big r;
  BIGNUM* q = r.p;
  if (!BN_dec2bn(&q, s.c_str())) throw runtime_error("dec");
  return r;
}

static Big randBig(int bits) {
  size_t n = (bits + 7) / 8;
  Bytes b(n);
  RAND_bytes(b.data(), (int)n);
  b[0] &= (unsigned char)(0xFF >> (8 * n - bits));
  Big r;
  BN_bin2bn(b.data(), (int)n, r.p);
  return r;
}
static Big randSigned(int bits) {
  Big r = randBig(bits);
  unsigned char c;
  RAND_bytes(&c, 1);
  return (c & 1) ? neg(r) : r;
}

static Big dot(const vector<Big>& a, const vector<Big>& b) {
  Big s(0), t;
  for (size_t i = 0; i < a.size(); i++) { BN_mul(t.p, a[i].p, b[i].p, bnctx()); BN_add(s.p, s.p, t.p); }
  return s;
}
static vector<Big> subv(const vector<Big>& a, const vector<Big>& b) {
  vector<Big> r;
  r.reserve(a.size());
  for (size_t i = 0; i < a.size(); i++) r.push_back(a[i] - b[i]);
  return r;
}

static Big isqrt(const Big& n) {
  if (isNeg(n)) throw runtime_error("neg");
  if (cmp(n, Big(2)) < 0) return n;
  Big x = shl(Big(1), (BN_num_bits(n.p) >> 1) + 1);
  for (;;) {
    Big y = shr(x + n / x, 1);
    if (cmp(y, x) >= 0) return x;
    x = y;
  }
}

static string packVec(const vector<Big>& v) {
  static Big mod = shl(Big(1), COORD_BITS);
  string out;
  out.reserve(v.size() * (COORD_BITS / 4));
  unsigned char buf[COORD_BITS / 8];
  for (const Big& x : v) {
    Big y = isNeg(x) ? x + mod : x;
    BN_bn2binpad(y.p, buf, sizeof buf);
    out += toHex(buf, sizeof buf);
  }
  return out;
}
static vector<Big> unpackVec(const string& hex, size_t dim) {
  const size_t w = COORD_BITS / 4;
  if (hex.size() != dim * w) throw runtime_error("vec");
  for (char c : hex) if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) throw runtime_error("vec");
  Bytes raw = fromHex(hex);
  static Big mod = shl(Big(1), COORD_BITS);
  vector<Big> v;
  v.reserve(dim);
  const size_t bw = COORD_BITS / 8;
  for (size_t i = 0; i < dim; i++) {
    Big x;
    BN_bin2bn(&raw[i * bw], (int)bw, x.p);
    if (raw[i * bw] & 0x80) x = x - mod;
    v.push_back(std::move(x));
  }
  return v;
}

static Bytes shake(const Bytes& d, size_t len = 32) {
  EVP_MD_CTX* c = EVP_MD_CTX_new();
  Bytes o(len);
  EVP_DigestInit_ex(c, EVP_shake256(), nullptr);
  EVP_DigestUpdate(c, d.data(), d.size());
  EVP_DigestFinalXOF(c, o.data(), len);
  EVP_MD_CTX_free(c);
  return o;
}
static Bytes shake(const string& s, size_t len = 32) { return shake(B(s), len); }

static Bytes hmac(const EVP_MD* md, const Bytes& key, const Bytes& data) {
  unsigned int n = 0;
  Bytes o(EVP_MAX_MD_SIZE);
  HMAC(md, key.data(), (int)key.size(), data.data(), data.size(), o.data(), &n);
  o.resize(n);
  return o;
}
static Bytes hkdf(const Bytes& ikm, const Bytes& salt, const string& info) {
  Bytes prk = hmac(EVP_sha512(), salt, ikm);
  Bytes m = B(info);
  m.push_back(1);
  Bytes t = hmac(EVP_sha512(), prk, m);
  t.resize(32);
  wipe(prk);
  return t;
}

static vector<Big> deriveDir(const string& C0hex) {
  Bytes by = shake("DIR|" + C0hex, DIM * 4);
  vector<Big> u;
  u.reserve(DIM);
  for (size_t i = 0; i < DIM; i++) {
    uint32_t w = (uint32_t)by[4 * i] << 24 | (uint32_t)by[4 * i + 1] << 16 | (uint32_t)by[4 * i + 2] << 8 | (uint32_t)by[4 * i + 3];
    u.emplace_back((long long)(int32_t)w);
  }
  if (isZero(dot(u, u))) u[0] = Big(1);
  return u;
}
static Bytes vectorKey(const Big& L2, const vector<Big>& C1) {
  string s = "VEC-AES256|" + toDec(L2) + "|";
  for (size_t i = 0; i < C1.size(); i++) { if (i) s += ','; s += toDec(C1[i]); }
  return shake(s, 32);
}

struct Enc { string iv, tag, ct; };

static Enc aesEncrypt(const Bytes& key, const string& plain, const string& aad) {
  Bytes iv(12);
  RAND_bytes(iv.data(), 12);
  size_t total = (4 + plain.size() + PAD - 1) / PAD * PAD;
  Bytes buf(total, 0);
  uint32_t n = (uint32_t)plain.size();
  buf[0] = n >> 24; buf[1] = n >> 16; buf[2] = n >> 8; buf[3] = n;
  memcpy(&buf[4], plain.data(), plain.size());
  EVP_CIPHER_CTX* c = EVP_CIPHER_CTX_new();
  Bytes ct(total + 16), tag(16);
  int l = 0, f = 0;
  EVP_EncryptInit_ex(c, EVP_aes_256_gcm(), nullptr, nullptr, nullptr);
  EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr);
  EVP_EncryptInit_ex(c, nullptr, nullptr, key.data(), iv.data());
  EVP_EncryptUpdate(c, nullptr, &l, (const unsigned char*)aad.data(), (int)aad.size());
  EVP_EncryptUpdate(c, ct.data(), &l, buf.data(), (int)buf.size());
  EVP_EncryptFinal_ex(c, ct.data() + l, &f);
  EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_GET_TAG, 16, tag.data());
  EVP_CIPHER_CTX_free(c);
  ct.resize(l + f);
  return Enc{b64enc(iv), b64enc(tag), b64enc(ct)};
}
static string aesDecrypt(const Bytes& key, const Enc& e, const string& aad) {
  Bytes iv = b64dec(e.iv), tag = b64dec(e.tag), ct = b64dec(e.ct);
  if (iv.size() != 12 || tag.size() != 16 || ct.size() < 4) throw runtime_error("aes");
  EVP_CIPHER_CTX* c = EVP_CIPHER_CTX_new();
  Bytes buf(ct.size() + 16);
  int l = 0, f = 0;
  EVP_DecryptInit_ex(c, EVP_aes_256_gcm(), nullptr, nullptr, nullptr);
  EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr);
  EVP_DecryptInit_ex(c, nullptr, nullptr, key.data(), iv.data());
  EVP_DecryptUpdate(c, nullptr, &l, (const unsigned char*)aad.data(), (int)aad.size());
  EVP_DecryptUpdate(c, buf.data(), &l, ct.data(), (int)ct.size());
  EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_TAG, 16, tag.data());
  int ok = EVP_DecryptFinal_ex(c, buf.data() + l, &f);
  EVP_CIPHER_CTX_free(c);
  if (ok <= 0) throw runtime_error("tag");
  buf.resize(l + f);
  size_t n = (size_t)buf[0] << 24 | (size_t)buf[1] << 16 | (size_t)buf[2] << 8 | buf[3];
  if (n > buf.size() - 4) throw runtime_error("pad");
  return string(buf.begin() + 4, buf.begin() + 4 + n);
}
static string encJson(const Enc& e) {
  return "{\"iv\":\"" + e.iv + "\",\"tag\":\"" + e.tag + "\",\"ct\":\"" + e.ct + "\"}";
}

using EcPtr = std::shared_ptr<EC_KEY>;
static EcPtr ecGen() {
  EC_KEY* k = EC_KEY_new_by_curve_name(NID_secp521r1);
  if (!k || !EC_KEY_generate_key(k)) throw runtime_error("ec");
  return EcPtr(k, EC_KEY_free);
}
static Bytes ecPub(const EcPtr& k) {
  const EC_GROUP* g = EC_KEY_get0_group(k.get());
  const EC_POINT* P = EC_KEY_get0_public_key(k.get());
  size_t n = EC_POINT_point2oct(g, P, POINT_CONVERSION_UNCOMPRESSED, nullptr, 0, bnctx());
  Bytes o(n);
  EC_POINT_point2oct(g, P, POINT_CONVERSION_UNCOMPRESSED, o.data(), n, bnctx());
  return o;
}
static Bytes ecShared(const EcPtr& k, const Bytes& peer) {
  const EC_GROUP* g = EC_KEY_get0_group(k.get());
  std::unique_ptr<EC_POINT, void (*)(EC_POINT*)> P(EC_POINT_new(g), EC_POINT_free);
  if (!EC_POINT_oct2point(g, P.get(), peer.data(), peer.size(), bnctx())) throw runtime_error("peer");
  Bytes o(66);
  if (ECDH_compute_key(o.data(), o.size(), P.get(), k.get(), nullptr) != 66) throw runtime_error("ecdh");
  return o;
}

struct J {
  string s;
  std::map<string, J> o;
};
struct JP {
  const string& t;
  size_t i;
  explicit JP(const string& s) : t(s), i(0) {}
  char cur() { if (i >= t.size()) throw runtime_error("json"); return t[i]; }
  void ws() { while (i < t.size() && (t[i] == ' ' || t[i] == '\t' || t[i] == '\r' || t[i] == '\n')) i++; }
  string str() {
    if (cur() != '"') throw runtime_error("json");
    i++;
    string r;
    while (cur() != '"') {
      char c = t[i++];
      if (c != '\\') { r += c; continue; }
      char e = cur(); i++;
      switch (e) {
        case 'n': r += '\n'; break;
        case 't': r += '\t'; break;
        case 'r': r += '\r'; break;
        case 'b': r += '\b'; break;
        case 'f': r += '\f'; break;
        case 'u': {
          if (i + 4 > t.size()) throw runtime_error("json");
          unsigned cp = 0;
          for (int k = 0; k < 4; k++) cp = cp << 4 | (unsigned)hexVal(t[i + k]);
          i += 4;
          if (cp < 0x80) r += (char)cp;
          else if (cp < 0x800) { r += (char)(0xC0 | cp >> 6); r += (char)(0x80 | (cp & 63)); }
          else { r += (char)(0xE0 | cp >> 12); r += (char)(0x80 | ((cp >> 6) & 63)); r += (char)(0x80 | (cp & 63)); }
          break;
        }
        default: r += e;
      }
    }
    i++;
    return r;
  }
  J val(int depth) {
    if (depth > 8) throw runtime_error("json");
    ws();
    J j;
    char c = cur();
    if (c == '{') {
      i++; ws();
      if (cur() == '}') { i++; return j; }
      for (;;) {
        ws();
        string k = str();
        ws();
        if (cur() != ':') throw runtime_error("json");
        i++;
        j.o[k] = val(depth + 1);
        ws();
        char d = cur(); i++;
        if (d == ',') continue;
        if (d == '}') break;
        throw runtime_error("json");
      }
    } else if (c == '"') {
      j.s = str();
    } else {
      size_t st = i;
      while (i < t.size() && !strchr(",} \t\r\n", t[i])) i++;
      j.s = t.substr(st, i - st);
    }
    return j;
  }
};
static J parseJson(const string& s) { JP p(s); return p.val(0); }
static const J& get(const J& j, const string& k) {
  auto it = j.o.find(k);
  if (it == j.o.end()) throw runtime_error("json");
  return it->second;
}
static Enc encOf(const J& j) { return Enc{get(j, "iv").s, get(j, "tag").s, get(j, "ct").s}; }

static const char* KEYFILE = "vt4096-server.json";
static const long long SESSION_TTL_MS = 60000;
static const size_t MAX_SESSIONS = 2000;

static vector<Big> S0, S1;
static string S0hex, S0hash;
static Bytes sidKey;

struct Session { EcPtr ec; string ecdhPub; long long expiry; };
static std::map<string, Session> sessions;
static std::map<string, std::pair<int, long long>> rate;

static bool limited(const string& ip) {
  long long now = nowMs();
  auto& r = rate[ip];
  if (r.second < now) { r.first = 0; r.second = now + 60000; }
  return ++r.first > 60;
}

static void loadOrCreateKeys() {
  std::ifstream f(KEYFILE);
  if (f) {
    std::stringstream ss;
    ss << f.rdbuf();
    J k = parseJson(ss.str());
    if (std::stoi(get(k, "dim").s) != (int)DIM) throw runtime_error("Tệp khoá không phải vector 4096 trục");
    S0 = unpackVec(get(k, "S0").s, DIM);
    S1 = unpackVec(get(k, "S1").s, DIM);
    return;
  }
  for (size_t i = 0; i < DIM; i++) S0.push_back(randSigned(COORD_BITS - 1));
  for (size_t i = 0; i < DIM; i++) S1.push_back(randSigned(COORD_BITS - 1));
  string out = "{\"dim\":4096,\"S0\":\"" + packVec(S0) + "\",\"S1\":\"" + packVec(S1) + "\"}";
  int fd = open(KEYFILE, O_WRONLY | O_CREAT | O_TRUNC, 0600);
  if (fd < 0 || write(fd, out.data(), out.size()) != (ssize_t)out.size()) throw runtime_error("Không ghi được tệp khoá");
  close(fd);
  std::cout << "Đã tạo vector server mới -> " << KEYFILE << std::endl;
}

static string makeHello() {
  if (sessions.size() >= MAX_SESSIONS) throw runtime_error("busy");
  Bytes rnd(16);
  RAND_bytes(rnd.data(), 16);
  Bytes tg = hmac(EVP_sha256(), sidKey, rnd);
  tg.resize(8);
  string sid = toHex(rnd) + toHex(tg);
  EcPtr ec = ecGen();
  string pub = b64enc(ecPub(ec));
  long long expiry = nowMs() + SESSION_TTL_MS;
  sessions[sid] = Session{ec, pub, expiry};
  return "{\"sid\":\"" + sid + "\",\"dim\":4096,\"S0\":\"" + S0hex + "\",\"ecdhPub\":\"" + pub +
         "\",\"expiry\":" + std::to_string(expiry) + "}";
}

static string handleExchange(const J& b) {
  string sid = get(b, "sid").s;
  auto it = sessions.find(sid);
  if (it == sessions.end()) throw runtime_error("session");
  Session s = it->second;
  sessions.erase(it);
  if (s.expiry < nowMs()) throw runtime_error("session");
  if (sid.size() != 48) throw runtime_error("sid");
  Bytes tg = hmac(EVP_sha256(), sidKey, fromHex(sid.substr(0, 32)));
  tg.resize(8);
  if (sid.substr(32) != toHex(tg)) throw runtime_error("sid");

  const string& C0hex = get(b, "C0").s;
  vector<Big> C0 = unpackVec(C0hex, DIM);
  const string& epk = get(b, "epk").s;

  Bytes ecdhSS = ecShared(s.ec, b64dec(epk));
  Bytes transcript = shake("TR|" + sid + "|" + S0hash + "|" + s.ecdhPub + "|" + epk + "|" + C0hex + "|" + std::to_string(s.expiry), 32);
  string tr = toHex(transcript);
  Bytes wrapKey = hkdf(ecdhSS, transcript, "len-wrap");

  string L2str = aesDecrypt(wrapKey, encOf(get(b, "lenEnc")), "len|" + tr);
  if (L2str.empty() || L2str.size() > 6001 || L2str[0] < '1' || L2str[0] > '9') throw runtime_error("L2");
  for (char c : L2str) if (c < '0' || c > '9') throw runtime_error("L2");
  Big L2 = fromDec(L2str);

  vector<Big> u = deriveDir(C0hex);
  vector<Big> d = subv(C0, S0);
  Big a = dot(u, u), bb = dot(u, d), c = dot(d, d);
  Big D = bb * bb - a * (c - L2);
  if (isNeg(D)) throw runtime_error("D");
  Big r = isqrt(D);
  if (cmp(r * r, D) != 0 || !isZero((r - bb) % a)) throw runtime_error("root");
  Big t = (r - bb) / a;
  vector<Big> C1;
  C1.reserve(DIM);
  for (size_t i = 0; i < DIM; i++) C1.push_back(C0[i] + t * u[i]);

  Bytes vKey = vectorKey(L2, C1);
  Bytes dataKey = hkdf(cat(vKey, ecdhSS), transcript, "data");
  string message = aesDecrypt(dataKey, encOf(get(b, "data")), "data|" + tr);

  std::cout << "[server] Nhận: " << message << std::endl;
  Bytes replyKey = hkdf(dataKey, transcript, "reply");
  Enc reply = aesEncrypt(replyKey, "Server đã nhận: " + message, "reply|" + tr);
  wipe(ecdhSS); wipe(wrapKey); wipe(vKey); wipe(dataKey); wipe(replyKey);
  return "{\"reply\":" + encJson(reply) + "}";
}

static void sendAll(int fd, const string& s) {
  size_t o = 0;
  while (o < s.size()) {
    ssize_t n = send(fd, s.data() + o, s.size() - o, MSG_NOSIGNAL);
    if (n <= 0) return;
    o += (size_t)n;
  }
}
static void reply(int fd, int code, const string& body) {
  const char* msg = code == 200 ? "OK" : code == 400 ? "Bad Request" : code == 404 ? "Not Found" : code == 429 ? "Too Many Requests" : "Service Unavailable";
  sendAll(fd, "HTTP/1.1 " + std::to_string(code) + " " + msg + "\r\nContent-Type: application/json\r\nContent-Length: " +
                  std::to_string(body.size()) + "\r\nConnection: close\r\n\r\n" + body);
}

static bool readRequest(int fd, string& method, string& path, string& body) {
  string buf;
  char tmp[65536];
  size_t he;
  while ((he = buf.find("\r\n\r\n")) == string::npos) {
    if (buf.size() > 16384) return false;
    ssize_t n = recv(fd, tmp, sizeof tmp, 0);
    if (n <= 0) return false;
    buf.append(tmp, (size_t)n);
  }
  string head = buf.substr(0, he);
  size_t sp1 = head.find(' '), sp2 = head.find(' ', sp1 + 1);
  if (sp1 == string::npos || sp2 == string::npos) return false;
  method = head.substr(0, sp1);
  path = head.substr(sp1 + 1, sp2 - sp1 - 1);
  string low = head;
  for (char& c : low) c = (char)tolower((unsigned char)c);
  size_t len = 0;
  size_t cl = low.find("\r\ncontent-length:");
  if (cl != string::npos) len = std::strtoul(low.c_str() + cl + 17, nullptr, 10);
  if (len > 2000000) return false;
  body = buf.substr(he + 4);
  while (body.size() < len) {
    ssize_t n = recv(fd, tmp, sizeof tmp, 0);
    if (n <= 0) return false;
    body.append(tmp, (size_t)n);
  }
  body.resize(len);
  return true;
}

static string peerIp(const sockaddr_storage& ss) {
  char ip[INET6_ADDRSTRLEN] = "?";
  if (ss.ss_family == AF_INET6) inet_ntop(AF_INET6, &((const sockaddr_in6*)&ss)->sin6_addr, ip, sizeof ip);
  else if (ss.ss_family == AF_INET) inet_ntop(AF_INET, &((const sockaddr_in*)&ss)->sin_addr, ip, sizeof ip);
  return ip;
}

int main() {
  signal(SIGPIPE, SIG_IGN);
  try {
    loadOrCreateKeys();
    S0hex = packVec(S0);
    S0hash = toHex(shake(S0hex, 32));
    sidKey = shake("SID|" + packVec(S1), 32);

    int port = getenv("PORT") ? atoi(getenv("PORT")) : 3000;
    int ls = socket(AF_INET6, SOCK_STREAM, 0);
    int one = 1, zero = 0;
    if (ls >= 0) {
      setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
      setsockopt(ls, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof zero);
      sockaddr_in6 a6{};
      a6.sin6_family = AF_INET6; a6.sin6_addr = in6addr_any; a6.sin6_port = htons((uint16_t)port);
      if (bind(ls, (sockaddr*)&a6, sizeof a6) < 0) throw runtime_error("Không mở được cổng");
    } else {
      ls = socket(AF_INET, SOCK_STREAM, 0);
      setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
      sockaddr_in a4{};
      a4.sin_family = AF_INET; a4.sin_addr.s_addr = INADDR_ANY; a4.sin_port = htons((uint16_t)port);
      if (bind(ls, (sockaddr*)&a4, sizeof a4) < 0) throw runtime_error("Không mở được cổng");
    }
    listen(ls, 128);
    std::cout << "Server chạy tại http://localhost:" << port << "  |  " << DIM << " trục" << std::endl;

    for (;;) {
      sockaddr_storage ss{};
      socklen_t sl = sizeof ss;
      int fd = accept(ls, (sockaddr*)&ss, &sl);
      if (fd < 0) continue;
      timeval tv{5, 0};
      setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
      long long now = nowMs();
      for (auto it = sessions.begin(); it != sessions.end();) it = it->second.expiry < now ? sessions.erase(it) : std::next(it);
      try {
        if (limited(peerIp(ss))) { reply(fd, 429, "{\"error\":\"rate\"}"); close(fd); continue; }
        string method, path, body;
        if (!readRequest(fd, method, path, body)) { close(fd); continue; }
        if (method == "GET" && path == "/hello") {
          try { reply(fd, 200, makeHello()); } catch (...) { reply(fd, 503, "{\"error\":\"busy\"}"); }
        } else if (method == "POST" && path == "/exchange") {
          try { reply(fd, 200, handleExchange(parseJson(body))); }
          catch (std::exception& e) {
            std::cout << "[server] Từ chối: " << e.what() << std::endl;
            reply(fd, 400, "{\"error\":\"bad request\"}");
          }
        } else {
          reply(fd, 404, "{\"error\":\"not found\"}");
        }
      } catch (...) {}
      close(fd);
    }
  } catch (std::exception& e) {
    std::cerr << "Lỗi: " << e.what() << std::endl;
    return 1;
  }
}
