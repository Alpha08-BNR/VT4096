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
static Big neg(const Big& a) { Big r(a); if (!BN_is_zero(r.p)) BN_set_negative(r.p, !BN_is_negative(r.p)); return r; }
static Big shl(const Big& a, int n) { Big r; BN_lshift(r.p, a.p, n); return r; }
static bool isNeg(const Big& a) { return BN_is_negative(a.p) != 0; }
static bool isZero(const Big& a) { return BN_is_zero(a.p) != 0; }

static string toDec(const Big& a) {
  char* s = BN_bn2dec(a.p);
  string r(s);
  OPENSSL_free(s);
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

static string httpCall(const string& host, const string& port, const string& method, const string& path, const string& body, int& status) {
  addrinfo hints{}, *res = nullptr;
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo(host.c_str(), port.c_str(), &hints, &res) != 0) throw runtime_error("Không phân giải được địa chỉ server");
  int fd = -1;
  for (addrinfo* a = res; a; a = a->ai_next) {
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) continue;
    if (connect(fd, a->ai_addr, a->ai_addrlen) == 0) break;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  if (fd < 0) throw runtime_error("Không kết nối được tới server");
  timeval tv{30, 0};
  setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);

  string req = method + " " + path + " HTTP/1.1\r\nHost: " + host + ":" + port + "\r\nConnection: close\r\n";
  if (method == "POST") req += "Content-Type: application/json\r\nContent-Length: " + std::to_string(body.size()) + "\r\n";
  req += "\r\n" + body;
  size_t o = 0;
  while (o < req.size()) {
    ssize_t n = send(fd, req.data() + o, req.size() - o, MSG_NOSIGNAL);
    if (n <= 0) { close(fd); throw runtime_error("Gửi dữ liệu thất bại"); }
    o += (size_t)n;
  }
  string raw;
  char tmp[65536];
  for (;;) {
    ssize_t n = recv(fd, tmp, sizeof tmp, 0);
    if (n <= 0) break;
    raw.append(tmp, (size_t)n);
  }
  close(fd);

  size_t he = raw.find("\r\n\r\n");
  if (he == string::npos || raw.size() < 12) throw runtime_error("Phản hồi HTTP không hợp lệ");
  status = atoi(raw.c_str() + 9);
  string head = raw.substr(0, he);
  for (char& c : head) c = (char)tolower((unsigned char)c);
  string data = raw.substr(he + 4);
  if (head.find("transfer-encoding: chunked") == string::npos) return data;
  string out;
  size_t i = 0;
  while (i < data.size()) {
    size_t e = data.find("\r\n", i);
    if (e == string::npos) break;
    size_t n = std::strtoul(data.substr(i, e - i).c_str(), nullptr, 16);
    i = e + 2;
    if (n == 0) break;
    out.append(data, i, n);
    i += n + 2;
  }
  return out;
}

int main(int argc, char** argv) {
  try {
    string message;
    for (int i = 1; i < argc; i++) { if (i > 1) message += ' '; message += argv[i]; }
    if (message.empty()) message = "Xin chào từ client C++ vector 4096 trục!";

    string server = getenv("SERVER") ? getenv("SERVER") : "http://localhost:3000";
    if (server.rfind("http://", 0) == 0) server = server.substr(7);
    size_t sl = server.find('/');
    if (sl != string::npos) server = server.substr(0, sl);
    string host = server, port = "80";
    size_t colon = server.rfind(':');
    if (colon != string::npos) { host = server.substr(0, colon); port = server.substr(colon + 1); }

    int status = 0;
    string hb = httpCall(host, port, "GET", "/hello", "", status);
    if (status != 200) throw runtime_error("Server không trả gói hello");
    J h = parseJson(hb);
    if (std::stoi(get(h, "dim").s) != (int)DIM) throw runtime_error("Server không dùng vector 4096 trục");
    long long expiry = std::stoll(get(h, "expiry").s);
    long long now = nowMs();
    if (expiry < now - 5000 || expiry > now + 120000) throw runtime_error("Gói hello hết hạn hoặc sai thời gian");
    const string& sid = get(h, "sid").s;
    const string& S0str = get(h, "S0").s;
    const string& ecdhPub = get(h, "ecdhPub").s;
    string S0hash = toHex(shake(S0str, 32));
    vector<Big> S0 = unpackVec(S0str, DIM);

    vector<Big> C0;
    C0.reserve(DIM);
    for (size_t i = 0; i < DIM; i++) C0.push_back(randSigned(COORD_BITS - 1));
    string C0hex = packVec(C0);
    vector<Big> u = deriveDir(C0hex);
    vector<Big> d = subv(C0, S0);
    Big a = dot(u, u), b = dot(u, d);
    Big t = (isNeg(b) ? neg(b) / a + Big(1) : Big(0)) + Big(1) + randBig(512);
    vector<Big> C1;
    C1.reserve(DIM);
    for (size_t i = 0; i < DIM; i++) C1.push_back(C0[i] + t * u[i]);

    vector<Big> NVT = subv(S0, C1);
    Big L2 = dot(NVT, NVT);

    EcPtr ec = ecGen();
    string epk = b64enc(ecPub(ec));
    Bytes ecdhSS = ecShared(ec, b64dec(ecdhPub));

    Bytes transcript = shake("TR|" + sid + "|" + S0hash + "|" + ecdhPub + "|" + epk + "|" + C0hex + "|" + std::to_string(expiry), 32);
    string tr = toHex(transcript);
    Bytes wrapKey = hkdf(ecdhSS, transcript, "len-wrap");
    Enc lenEnc = aesEncrypt(wrapKey, toDec(L2), "len|" + tr);

    Bytes vKey = vectorKey(L2, C1);
    Bytes dataKey = hkdf(cat(vKey, ecdhSS), transcript, "data");
    Enc data = aesEncrypt(dataKey, message, "data|" + tr);

    string post = "{\"sid\":\"" + sid + "\",\"C0\":\"" + C0hex + "\",\"epk\":\"" + epk + "\",\"lenEnc\":" + encJson(lenEnc) +
                  ",\"data\":" + encJson(data) + "}";
    string rb = httpCall(host, port, "POST", "/exchange", post, status);
    if (status != 200) { std::cerr << "Server từ chối: " << rb << std::endl; return 1; }
    J out = parseJson(rb);

    Bytes replyKey = hkdf(dataKey, transcript, "reply");
    std::cout << "[client] Phản hồi: " << aesDecrypt(replyKey, encOf(get(out, "reply")), "reply|" + tr) << std::endl;
    wipe(ecdhSS); wipe(wrapKey); wipe(vKey); wipe(dataKey); wipe(replyKey);
    return 0;
  } catch (std::exception& e) {
    std::cerr << "Lỗi: " << e.what() << std::endl;
    return 1;
  }
}
