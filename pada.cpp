/*
 * ============================================================================
 *  kangaroo.cpp  -  Pollard Kangaroo (secp256k1) avec points distingues "Tame"
 *                   precalcules, sauvegardables et reutilisables.
 * ============================================================================
 *  Intervalle de recherche : [1 , 2^B]   (B = 80 par defaut)
 *
 *  Mode 1 : creer un fichier tame_NNN.dp  (Ctrl+C = arret propre + sauvegarde)
 *  Mode 2 : continuer un fichier tame_NNN.dp
 *  Mode 3 : charger un fichier tame_NNN.dp et resoudre une/des cle(s) publique(s)
 *           avec des kangourous Wild (memes sauts => collisions valides)
 *
 *  Techniques :
 *   - symetrie +/- : chaque point est ramene a la classe {P,-P} (parite de y)
 *     => l'intervalle effectif est divise par 2  (gain ~ sqrt(2))
 *   - les kangourous Wild suivent aussi leur signe (s) : collisions Wild/Wild de
 *     signes opposes exploitables, en plus des collisions Tame/Wild
 *   - inversion modulaire par lots (Montgomery) : ~6 multiplications / saut
 *   - detection de cycles courts (inevitables avec la symetrie) + sortie
 *   - arithmetique 4x64 bits, reduction speciale secp256k1, multi-thread
 *
 *  Compilation (64 bits uniquement, GCC/Clang avec __int128) :
 *    Ubuntu  : g++ -O3 -march=native -std=c++17 -pthread kangaroo.cpp -o kangaroo
 *    Termux  : pkg install clang
 *              clang++ -O3 -std=c++17 -pthread kangaroo.cpp -o kangaroo
 *    Windows : (MSYS2 MinGW-w64) g++ -O3 -march=native -std=c++17 -pthread -static kangaroo.cpp -o kangaroo.exe
 *    (MSVC non supporte : pas de __int128)
 * ============================================================================
 */
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <algorithm>
#include <csignal>
#include <iostream>
#include <unordered_map>
#include <functional>
#ifdef _WIN32
#include <windows.h>
#endif

#ifndef __SIZEOF_INT128__
#error "Ce programme necessite un compilateur 64 bits avec __int128 (GCC/Clang)."
#endif

typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;
typedef __int128 s128;
typedef unsigned long long ull;
#define INL static inline __attribute__((always_inline))

// ============================================================================
//  Corps fini F_p  (p = 2^256 - 2^32 - 977), 4 limbs de 64 bits
// ============================================================================
struct fe { u64 d[4]; };
static const u64 FC = 0x1000003D1ULL;
static const u64 P0 = 0xFFFFFFFEFFFFFC2FULL;
static const fe ONE = {{1, 0, 0, 0}};
static const fe ZERO = {{0, 0, 0, 0}};

INL bool fe_ge_p(const fe& a) {
    return a.d[3] == ~0ULL && a.d[2] == ~0ULL && a.d[1] == ~0ULL && a.d[0] >= P0;
}
INL void fe_addC(fe& a) {  // a += FC (mod 2^256)  <=> a -= p si a >= p
    u128 c = (u128)a.d[0] + FC; a.d[0] = (u64)c; c >>= 64;
    c += a.d[1]; a.d[1] = (u64)c; c >>= 64;
    c += a.d[2]; a.d[2] = (u64)c; c >>= 64;
    c += a.d[3]; a.d[3] = (u64)c;
}
INL bool fe_is_zero(const fe& a) { return (a.d[0] | a.d[1] | a.d[2] | a.d[3]) == 0; }
INL bool fe_eq(const fe& a, const fe& b) {
    return ((a.d[0] ^ b.d[0]) | (a.d[1] ^ b.d[1]) | (a.d[2] ^ b.d[2]) | (a.d[3] ^ b.d[3])) == 0;
}
INL void fe_add(fe& r, const fe& a, const fe& b) {
    u128 c = (u128)a.d[0] + b.d[0]; u64 r0 = (u64)c; c >>= 64;
    c += (u128)a.d[1] + b.d[1]; u64 r1 = (u64)c; c >>= 64;
    c += (u128)a.d[2] + b.d[2]; u64 r2 = (u64)c; c >>= 64;
    c += (u128)a.d[3] + b.d[3]; u64 r3 = (u64)c; c >>= 64;
    u128 k = (u128)r0 + FC; u64 t0 = (u64)k; k >>= 64;
    k += r1; u64 t1 = (u64)k; k >>= 64;
    k += r2; u64 t2 = (u64)k; k >>= 64;
    k += r3; u64 t3 = (u64)k; k >>= 64;
    if ((u64)c | (u64)k) { r.d[0] = t0; r.d[1] = t1; r.d[2] = t2; r.d[3] = t3; }
    else { r.d[0] = r0; r.d[1] = r1; r.d[2] = r2; r.d[3] = r3; }
}
INL void fe_sub(fe& r, const fe& a, const fe& b) {
    u128 t = (u128)a.d[0] - b.d[0]; u64 r0 = (u64)t; u64 br = (u64)(t >> 64) & 1;
    t = (u128)a.d[1] - b.d[1] - br; u64 r1 = (u64)t; br = (u64)(t >> 64) & 1;
    t = (u128)a.d[2] - b.d[2] - br; u64 r2 = (u64)t; br = (u64)(t >> 64) & 1;
    t = (u128)a.d[3] - b.d[3] - br; u64 r3 = (u64)t; br = (u64)(t >> 64) & 1;
    if (br) {  // + p  ==  - FC (mod 2^256)
        t = (u128)r0 - FC; r0 = (u64)t; br = (u64)(t >> 64) & 1;
        t = (u128)r1 - br; r1 = (u64)t; br = (u64)(t >> 64) & 1;
        t = (u128)r2 - br; r2 = (u64)t; br = (u64)(t >> 64) & 1;
        t = (u128)r3 - br; r3 = (u64)t;
    }
    r.d[0] = r0; r.d[1] = r1; r.d[2] = r2; r.d[3] = r3;
}
INL void fe_neg(fe& r, const fe& a) { fe_sub(r, ZERO, a); }

INL void fe_reduce(fe& r, const u64 t[8]) {
    u128 c = 0; u64 s[5];
    for (int i = 0; i < 4; i++) { c += (u128)t[4 + i] * FC + t[i]; s[i] = (u64)c; c >>= 64; }
    s[4] = (u64)c;
    c = (u128)s[4] * FC + s[0]; r.d[0] = (u64)c; c >>= 64;
    c += s[1]; r.d[1] = (u64)c; c >>= 64;
    c += s[2]; r.d[2] = (u64)c; c >>= 64;
    c += s[3]; r.d[3] = (u64)c; c >>= 64;
    if (c) fe_addC(r);
    if (fe_ge_p(r)) fe_addC(r);
}
INL void fe_mul(fe& r, const fe& a, const fe& b) {
    u64 t[8];
    for (int i = 0; i < 4; i++) {
        u128 carry = 0;
        for (int j = 0; j < 4; j++) {
            u128 cur = (u128)a.d[i] * b.d[j] + (i ? t[i + j] : 0) + carry;
            t[i + j] = (u64)cur; carry = cur >> 64;
        }
        t[i + 4] = (u64)carry;
    }
    fe_reduce(r, t);
}
INL void fe_sqr(fe& r, const fe& a) {
    u64 t[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    for (int i = 0; i < 3; i++) {
        u128 carry = 0;
        for (int j = i + 1; j < 4; j++) {
            u128 cur = (u128)a.d[i] * a.d[j] + t[i + j] + carry;
            t[i + j] = (u64)cur; carry = cur >> 64;
        }
        t[i + 4] = (u64)carry;
    }
    u64 cy = 0;
    for (int k = 0; k < 8; k++) { u64 nc = t[k] >> 63; t[k] = (t[k] << 1) | cy; cy = nc; }
    u128 c = 0;
    for (int i = 0; i < 4; i++) {
        u128 sq = (u128)a.d[i] * a.d[i];
        c += (u128)t[2 * i] + (u64)sq; t[2 * i] = (u64)c; c >>= 64;
        c += (u128)t[2 * i + 1] + (u64)(sq >> 64); t[2 * i + 1] = (u64)c; c >>= 64;
    }
    fe_reduce(r, t);
}
static void fe_sqrn(fe& r, const fe& a, int n) { fe_sqr(r, a); for (int i = 1; i < n; i++) fe_sqr(r, r); }
// inverse par petit theoreme de Fermat (chaine d'additions pour p-2)
static void fe_inv(fe& r, const fe& a) {
    fe x2, x3, x6, x9, x11, x22, x44, x88, x176, x220, x223, t;
    fe_sqr(x2, a); fe_mul(x2, x2, a);
    fe_sqr(x3, x2); fe_mul(x3, x3, a);
    fe_sqrn(x6, x3, 3); fe_mul(x6, x6, x3);
    fe_sqrn(x9, x6, 3); fe_mul(x9, x9, x3);
    fe_sqrn(x11, x9, 2); fe_mul(x11, x11, x2);
    fe_sqrn(x22, x11, 11); fe_mul(x22, x22, x11);
    fe_sqrn(x44, x22, 22); fe_mul(x44, x44, x22);
    fe_sqrn(x88, x44, 44); fe_mul(x88, x88, x44);
    fe_sqrn(x176, x88, 88); fe_mul(x176, x176, x88);
    fe_sqrn(x220, x176, 44); fe_mul(x220, x220, x44);
    fe_sqrn(x223, x220, 3); fe_mul(x223, x223, x3);
    fe_sqrn(t, x223, 23); fe_mul(t, t, x22);
    fe_sqrn(t, t, 5); fe_mul(t, t, a);
    fe_sqrn(t, t, 3); fe_mul(t, t, x2);
    fe_sqrn(t, t, 2); fe_mul(r, t, a);
}
static void fe_pow(fe& r, const fe& a, const u64 e[4]) {
    fe res = ONE, b = a;
    for (int i = 0; i < 256; i++) {
        if ((e[i >> 6] >> (i & 63)) & 1) fe_mul(res, res, b);
        fe_sqr(b, b);
    }
    r = res;
}
static void fe_set_be(fe& r, const uint8_t* b) {
    for (int i = 0; i < 4; i++) {
        u64 v = 0;
        for (int j = 0; j < 8; j++) v = (v << 8) | b[(3 - i) * 8 + j];
        r.d[i] = v;
    }
}
static void fe_get_be(const fe& a, uint8_t* b) {
    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 8; j++) b[(3 - i) * 8 + j] = (uint8_t)(a.d[i] >> (56 - 8 * j));
}

// ============================================================================
//  Courbe y^2 = x^3 + 7  (coordonnees affines)
// ============================================================================
struct pt { fe x, y; bool inf; };
static pt PT_INF() { pt p; p.x = ZERO; p.y = ZERO; p.inf = true; return p; }
static pt ec_neg(const pt& P) { pt r = P; if (!P.inf) fe_neg(r.y, P.y); return r; }
static pt ec_dbl(const pt& P) {
    if (P.inf || fe_is_zero(P.y)) return PT_INF();
    fe n, d, lam, t, x3, y3;
    fe_sqr(n, P.x); fe_add(t, n, n); fe_add(n, t, n);      // 3x^2
    fe_add(d, P.y, P.y); fe_inv(d, d);
    fe_mul(lam, n, d);
    fe_sqr(x3, lam); fe_sub(x3, x3, P.x); fe_sub(x3, x3, P.x);
    fe_sub(t, P.x, x3); fe_mul(y3, lam, t); fe_sub(y3, y3, P.y);
    pt r; r.x = x3; r.y = y3; r.inf = false; return r;
}
static pt ec_add(const pt& P, const pt& Q) {
    if (P.inf) return Q;
    if (Q.inf) return P;
    if (fe_eq(P.x, Q.x)) return fe_eq(P.y, Q.y) ? ec_dbl(P) : PT_INF();
    fe dx, dy, lam, t, x3, y3;
    fe_sub(dx, Q.x, P.x); fe_inv(dx, dx);
    fe_sub(dy, Q.y, P.y); fe_mul(lam, dy, dx);
    fe_sqr(x3, lam); fe_sub(x3, x3, P.x); fe_sub(x3, x3, Q.x);
    fe_sub(t, P.x, x3); fe_mul(y3, lam, t); fe_sub(y3, y3, P.y);
    pt r; r.x = x3; r.y = y3; r.inf = false; return r;
}
static bool on_curve(const pt& P) {
    fe l, r, t; fe_sqr(l, P.y); fe_sqr(t, P.x); fe_mul(r, t, P.x);
    fe seven = {{7, 0, 0, 0}}; fe_add(r, r, seven); return fe_eq(l, r);
}

// ---- utilitaires hexa ----
static bool parse_hex(const std::string& s0, std::vector<uint8_t>& out) {
    std::string s;
    for (char c : s0) if (!isspace((unsigned char)c)) s += c;
    if (s.size() >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) s = s.substr(2);
    if (s.empty() || (s.size() & 1)) return false;
    out.clear();
    for (size_t i = 0; i < s.size(); i += 2) {
        int v = 0;
        for (int j = 0; j < 2; j++) {
            char c = s[i + j]; int h;
            if (c >= '0' && c <= '9') h = c - '0';
            else if (c >= 'a' && c <= 'f') h = c - 'a' + 10;
            else if (c >= 'A' && c <= 'F') h = c - 'A' + 10;
            else return false;
            v = v * 16 + h;
        }
        out.push_back((uint8_t)v);
    }
    return true;
}
static std::string to_hex(const uint8_t* b, size_t n) {
    static const char* H = "0123456789abcdef"; std::string s;
    for (size_t i = 0; i < n; i++) { s += H[b[i] >> 4]; s += H[b[i] & 15]; }
    return s;
}
static std::string u128_dec(u128 v) {
    if (!v) return "0"; std::string s;
    while (v) { s += (char)('0' + (int)(v % 10)); v /= 10; }
    std::reverse(s.begin(), s.end()); return s;
}
static void u128_be32(u128 v, uint8_t* b) {
    memset(b, 0, 32);
    for (int i = 0; i < 16; i++) b[31 - i] = (uint8_t)(v >> (8 * i));
}
static std::string u128_hex(u128 v) {
    uint8_t b[32]; u128_be32(v, b); std::string h = to_hex(b + 16, 16);
    size_t i = 0; while (i + 1 < h.size() && h[i] == '0') i++;
    return h.substr(i);
}
static bool parse_pubkey(const std::string& s, pt& Q) {
    std::vector<uint8_t> b;
    if (!parse_hex(s, b)) return false;
    fe_set_be(Q.x, b.size() >= 33 ? &b[1] : &b[0]);
    Q.inf = false;
    if (b.size() == 65 && b[0] == 4) {
        fe_set_be(Q.y, &b[33]);
        if (fe_ge_p(Q.x) || fe_ge_p(Q.y)) return false;
        return on_curve(Q);
    }
    if (b.size() == 33 && (b[0] == 2 || b[0] == 3)) {
        if (fe_ge_p(Q.x)) return false;
        fe t, r, y; fe_sqr(t, Q.x); fe_mul(r, t, Q.x);
        fe seven = {{7, 0, 0, 0}}; fe_add(r, r, seven);
        u64 pp[4] = {P0 + 1, ~0ULL, ~0ULL, ~0ULL}, e[4];   // e = (p+1)/4
        for (int i = 0; i < 4; i++) e[i] = (pp[i] >> 2) | (i < 3 ? (pp[i + 1] << 62) : 0);
        fe_pow(y, r, e);
        fe y2; fe_sqr(y2, y);
        if (!fe_eq(y2, r)) return false;
        if ((y.d[0] & 1) != (u64)(b[0] & 1)) fe_neg(y, y);
        Q.y = y; return true;
    }
    return false;
}
static std::string pub_hex(const pt& P) {
    uint8_t b[33]; b[0] = 2 + (P.y.d[0] & 1); fe_get_be(P.x, b + 1); return to_hex(b, 33);
}

// ============================================================================
//  Table de multiples de G : 16 fenetres de 8 bits (scalaires jusqu'a 128 bits)
// ============================================================================
static pt G_PT;
static pt (*GT)[256];
static void init_tables() {
    std::vector<uint8_t> b;
    fe gx, gy;
    parse_hex("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", b); fe_set_be(gx, &b[0]);
    parse_hex("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", b); fe_set_be(gy, &b[0]);
    G_PT.x = gx; G_PT.y = gy; G_PT.inf = false;
    GT = new pt[16][256];
    pt base = G_PT;
    for (int w = 0; w < 16; w++) {
        GT[w][1] = base;
        for (int j = 2; j < 256; j++) GT[w][j] = ec_add(GT[w][j - 1], base);
        base = ec_add(GT[w][255], base);
    }
}
static pt mulG(u128 k) {
    pt R = PT_INF();
    for (int w = 0; w < 16; w++) {
        unsigned b = (unsigned)((k >> (8 * w)) & 0xFF);
        if (b) R = ec_add(R, GT[w][b]);
    }
    return R;
}

// ============================================================================
//  SHA-256 / Base58 / WIF
// ============================================================================
struct Sha256 {
    static inline uint32_t rr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
    static void hash(const uint8_t* data, size_t len, uint8_t out[32]) {
        static const uint32_t K[64] = {
            0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
            0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
            0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
            0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
            0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
            0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
            0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
            0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
        uint32_t h[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
        std::vector<uint8_t> m(data, data + len);
        m.push_back(0x80);
        while (m.size() % 64 != 56) m.push_back(0);
        uint64_t bits = (uint64_t)len * 8;
        for (int i = 7; i >= 0; i--) m.push_back((uint8_t)(bits >> (8 * i)));
        for (size_t o = 0; o < m.size(); o += 64) {
            uint32_t w[64];
            for (int i = 0; i < 16; i++)
                w[i] = (uint32_t)m[o + 4 * i] << 24 | (uint32_t)m[o + 4 * i + 1] << 16 | (uint32_t)m[o + 4 * i + 2] << 8 | m[o + 4 * i + 3];
            for (int i = 16; i < 64; i++) {
                uint32_t s0 = rr(w[i - 15], 7) ^ rr(w[i - 15], 18) ^ (w[i - 15] >> 3);
                uint32_t s1 = rr(w[i - 2], 17) ^ rr(w[i - 2], 19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16] + s0 + w[i - 7] + s1;
            }
            uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
            for (int i = 0; i < 64; i++) {
                uint32_t S1 = rr(e, 6) ^ rr(e, 11) ^ rr(e, 25), ch = (e & f) ^ (~e & g);
                uint32_t t1 = hh + S1 + ch + K[i] + w[i];
                uint32_t S0 = rr(a, 2) ^ rr(a, 13) ^ rr(a, 22), mj = (a & b) ^ (a & c) ^ (b & c);
                uint32_t t2 = S0 + mj;
                hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
            }
            h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
        }
        for (int i = 0; i < 8; i++) for (int j = 0; j < 4; j++) out[4 * i + j] = (uint8_t)(h[i] >> (24 - 8 * j));
    }
};
static std::string base58(const std::vector<uint8_t>& in) {
    const char* A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    size_t zeros = 0; while (zeros < in.size() && in[zeros] == 0) zeros++;
    std::vector<uint8_t> b58((in.size() - zeros) * 138 / 100 + 1, 0);
    size_t length = 0;
    for (size_t i = zeros; i < in.size(); i++) {
        int carry = in[i]; size_t j = 0;
        for (auto it = b58.rbegin(); (carry != 0 || j < length) && it != b58.rend(); ++it, ++j) {
            carry += 256 * (*it); *it = (uint8_t)(carry % 58); carry /= 58;
        }
        length = j;
    }
    auto it = b58.begin() + (b58.size() - length);
    while (it != b58.end() && *it == 0) ++it;
    std::string s(zeros, '1');
    for (; it != b58.end(); ++it) s += A[*it];
    return s;
}
static std::string wif_compressed(u128 k) {
    std::vector<uint8_t> v; v.push_back(0x80);
    uint8_t kb[32]; u128_be32(k, kb); v.insert(v.end(), kb, kb + 32); v.push_back(0x01);
    uint8_t h1[32], h2[32]; Sha256::hash(v.data(), v.size(), h1); Sha256::hash(h1, 32, h2);
    v.insert(v.end(), h2, h2 + 4);
    return base58(v);
}

// ============================================================================
//  Generateur pseudo-aleatoire (xoshiro256**)
// ============================================================================
struct Rng {
    u64 s[4];
    static u64 splitmix(u64& x) {
        x += 0x9E3779B97F4A7C15ULL; u64 z = x;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }
    void seed(u64 v) { for (int i = 0; i < 4; i++) s[i] = splitmix(v); }
    static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
    u64 next() {
        u64 r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
        return r;
    }
    u128 next128() { return ((u128)next() << 64) | next(); }
};

// ============================================================================
//  Configuration globale de la session (lue depuis l'entete du fichier .dp)
// ============================================================================
#pragma pack(push, 1)
struct Header {
    char magic[8]; u32 version, B, dpBits, NJ, mb, res;
    u64 seed, nDP, tameOps, pad0, pad1;
};
struct FileDP { u64 x0, x1, dlo, dhi; };   // 32 octets / point distingue
#pragma pack(pop)

struct Cfg {
    int B = 80, dpBits = 20, NJ = 256, mb = 40; u64 seed = 1;
    u128 H = 0, TR = 0, WA = 0; u64 dpMask = 0, maxSteps = 0;
    double tameSpread = 1.0, wildSpread = 0.125;
};
static Cfg C;
static const int MAXNJ = 1024;
static fe JX[MAXNJ], JY[MAXNJ]; static u64 JD[MAXNJ];
static const double KAPPA = 1.0;   // facteur d'estimation (calibre par tests)

static int default_mb(int B, int d) {
    int a = (B + 1) / 2, b = (int)std::ceil(1.5 * d) + 6;
    int m = std::max(a, b); if (m > 62) m = 62; if (m > B - 2) m = B - 2; return m;
}
static void set_cfg(const Header& h) {
    C.B = h.B; C.dpBits = h.dpBits; C.NJ = h.NJ; C.mb = h.mb; C.seed = h.seed;
    C.H = (u128)1 << (C.B - 1);
    C.TR = (u128)((long double)C.H * C.tameSpread);
    C.WA = (u128)((long double)C.H * C.wildSpread); if (C.WA < 1000) C.WA = 1000;
    C.dpMask = C.dpBits == 0 ? 0 : (~0ULL << (64 - C.dpBits));
    double ms = 40.0 * std::pow(2.0, C.dpBits) + 2000.0;
    C.maxSteps = ms > 1e18 ? (u64)1e18 : (u64)ms;
}
static void build_jumps() {
    Rng r; r.seed(C.seed ^ 0xA5A5A5A55A5A5A5AULL);
    u64 m = (C.mb >= 64) ? ~0ULL : ((1ULL << C.mb) - 1);
    for (int i = 0; i < C.NJ; i++) {
        JD[i] = 1 + (r.next() & m);
        pt P = mulG(JD[i]); JX[i] = P.x; JY[i] = P.y;
    }
}

// ============================================================================
//  Divers : affichage, signaux
// ============================================================================
static volatile sig_atomic_t g_sigint = 0;
static std::atomic<bool> g_stop(false);
static void on_sig(int) { g_sigint = 1; }
typedef std::chrono::steady_clock Clock;
static double secs(Clock::time_point a, Clock::time_point b) { return std::chrono::duration<double>(b - a).count(); }

static std::string fmt_si(double v) {
    const char* u[] = {"", "k", "M", "G", "T", "P", "E"}; int i = 0;
    while (v >= 1000 && i < 6) { v /= 1000; i++; }
    char b[32]; snprintf(b, sizeof b, v >= 100 ? "%.0f%s" : (v >= 10 ? "%.1f%s" : "%.2f%s"), v, u[i]); return b;
}
static std::string fmt_time(double s) {
    if (!(s >= 0) || std::isinf(s)) return "--";
    char b[64];
    if (s < 60) snprintf(b, sizeof b, "%.0fs", s);
    else if (s < 3600) snprintf(b, sizeof b, "%dm%02ds", (int)(s / 60), (int)s % 60);
    else if (s < 86400) snprintf(b, sizeof b, "%dh%02dm%02ds", (int)(s / 3600), (int)(s / 60) % 60, (int)s % 60);
    else if (s < 86400.0 * 3650) snprintf(b, sizeof b, "%dj %02dh%02dm", (int)(s / 86400), (int)(s / 3600) % 24, (int)(s / 60) % 60);
    else snprintf(b, sizeof b, ">10 ans");
    return b;
}
static std::string fmt_bytes(double b) {
    char s[32];
    if (b >= 1073741824.0) snprintf(s, sizeof s, "%.2f Go", b / 1073741824.0);
    else snprintf(s, sizeof s, "%.1f Mo", b / 1048576.0);
    return s;
}
static double mem_available() {   // octets de RAM disponibles (-1 si inconnu)
#ifdef _WIN32
    MEMORYSTATUSEX m; m.dwLength = sizeof m;
    if (GlobalMemoryStatusEx(&m)) return (double)m.ullAvailPhys;
    return -1;
#else
    FILE* f = fopen("/proc/meminfo", "r"); if (!f) return -1;
    char line[256]; double r = -1;
    while (fgets(line, sizeof line, f)) {
        unsigned long long kb;
        if (sscanf(line, "MemAvailable: %llu kB", &kb) == 1) { r = (double)kb * 1024.0; break; }
    }
    fclose(f); return r;
#endif
}

// ============================================================================
//  Noyau : kangourous (Tame ou Wild) par lots, inversion de Montgomery
// ============================================================================
struct alignas(64) Counter { std::atomic<u64> v{0}; };
struct DPRec { u64 x0, x1; s128 dist; int sgn; };
typedef std::function<void(std::vector<DPRec>&)> Sink;
static std::function<void(s128)> g_candidate;     // utilise en mode Wild

static void worker(int tid, bool wild, pt Qp, Counter* cnt, Sink sink, int G, u64 seedv) {
    Rng rng; rng.seed(seedv ^ ((u64)(tid + 1) * 0x9E3779B97F4A7C15ULL));
    const unsigned mask = (unsigned)C.NJ - 1;
    std::vector<fe> X(G), Y(G), pref(G), dxs(G);
    std::vector<s128> dist(G);
    std::vector<int8_t> sgn(G); std::vector<uint8_t> bad(G, 0);
    std::vector<u64> steps(G), hist((size_t)G * 8);
    std::vector<uint32_t> esc(G, 0), jidx(G);
    std::vector<DPRec> buf; buf.reserve(256);

    auto restart = [&](int i) {
        pt P; s128 d; int s;
        for (;;) {
            if (!wild) {
                u128 a = rng.next128() % (C.TR + 1);
                if (a == 0) continue;
                P = mulG(a); d = (s128)a; s = 0;
            } else {
                s128 a0 = (s128)(rng.next128() % (2 * C.WA + 1)) - (s128)C.WA;
                pt T = a0 >= 0 ? mulG((u128)a0) : ec_neg(mulG((u128)(-a0)));
                P = ec_add(Qp, T);
                if (P.inf) { if (g_candidate) g_candidate(-a0); continue; }
                d = a0; s = 1;
            }
            break;
        }
        if (P.y.d[0] & 1) { fe_neg(P.y, P.y); d = -d; s = -s; }
        X[i] = P.x; Y[i] = P.y; dist[i] = d; sgn[i] = (int8_t)s; steps[i] = 0; esc[i] = 0; bad[i] = 0;
        for (int k = 0; k < 8; k++) hist[(size_t)i * 8 + k] = P.x.d[0];
    };
    for (int i = 0; i < G; i++) restart(i);

    const u64 dpMask = C.dpMask, maxSteps = C.maxSteps;
    while (!g_stop.load(std::memory_order_relaxed)) {
        for (int i = 0; i < G; i++) {
            unsigned idx = (unsigned)((X[i].d[0] + esc[i]) & mask); esc[i] = 0; jidx[i] = idx;
            fe dx; fe_sub(dx, X[i], JX[idx]);
            if (fe_is_zero(dx)) { bad[i] = 1; dx = ONE; }
            dxs[i] = dx;
            if (i == 0) pref[0] = dx; else fe_mul(pref[i], pref[i - 1], dx);
        }
        fe inv; fe_inv(inv, pref[G - 1]);
        for (int i = G - 1; i >= 0; i--) {
            fe iv;
            if (i > 0) { fe_mul(iv, inv, pref[i - 1]); fe_mul(inv, inv, dxs[i]); } else iv = inv;
            if (bad[i]) { restart(i); continue; }
            unsigned idx = jidx[i];
            fe dy, lam, l2, x3, y3, t;
            fe_sub(dy, Y[i], JY[idx]);
            fe_mul(lam, dy, iv);
            fe_sqr(l2, lam);
            fe_sub(x3, l2, X[i]); fe_sub(x3, x3, JX[idx]);
            fe_sub(t, X[i], x3); fe_mul(y3, lam, t); fe_sub(y3, y3, Y[i]);
            dist[i] += (s128)JD[idx];
            if (y3.d[0] & 1) { fe_neg(y3, y3); dist[i] = -dist[i]; sgn[i] = (int8_t)-sgn[i]; }  // classe canonique : y pair
            X[i] = x3; Y[i] = y3;
            u64 xl = x3.d[0]; u64* h = &hist[(size_t)i * 8];
            bool cyc = false;
            for (int k = 0; k < 8; k++) cyc |= (h[k] == xl);
            h[steps[i] & 7] = xl; steps[i]++;
            if (cyc) esc[i] = 1 + (uint32_t)(x3.d[1] % (u64)(C.NJ - 1));   // sortie de cycle deterministe
            if ((x3.d[3] & dpMask) == 0) {
                buf.push_back(DPRec{x3.d[0], x3.d[1], dist[i], sgn[i]});
                restart(i);
            } else if (steps[i] >= maxSteps) restart(i);
        }
        cnt->v.fetch_add((u64)G, std::memory_order_relaxed);
        if (buf.size() >= 64) { sink(buf); buf.clear(); }
    }
    if (!buf.empty()) sink(buf);
}

// ============================================================================
//  Fichiers .dp
// ============================================================================
static std::mutex g_mtx;
static std::vector<FileDP> g_dps;
static std::atomic<u64> g_dpCount(0);

static std::string tame_name(int n) { char b[64]; snprintf(b, sizeof b, "tame_%03d.dp", n); return b; }
static bool file_exists(const std::string& f) { FILE* p = fopen(f.c_str(), "rb"); if (p) { fclose(p); return true; } return false; }
static bool cmp_dp(const FileDP& a, const FileDP& b) { return a.x0 < b.x0 || (a.x0 == b.x0 && a.x1 < b.x1); }
static bool read_header(const std::string& f, Header& h) {
    FILE* p = fopen(f.c_str(), "rb"); if (!p) return false;
    bool ok = fread(&h, sizeof h, 1, p) == 1 && memcmp(h.magic, "KTAME1\0\0", 8) == 0;
    fclose(p); return ok;
}
static bool load_file(const std::string& f, Header& h, std::vector<FileDP>& v) {
    FILE* p = fopen(f.c_str(), "rb"); if (!p) return false;
    if (fread(&h, sizeof h, 1, p) != 1 || memcmp(h.magic, "KTAME1\0\0", 8) != 0) { fclose(p); return false; }
    v.resize(h.nDP);
    size_t n = h.nDP ? fread(v.data(), sizeof(FileDP), h.nDP, p) : 0;
    fclose(p);
    if (n != h.nDP) { v.resize(n); h.nDP = n; }
    return true;
}
static bool save_file(const std::string& fname, Header h) {   // dedoublonne g_dps, ecrit atomiquement
    std::lock_guard<std::mutex> lk(g_mtx);
    std::sort(g_dps.begin(), g_dps.end(), cmp_dp);
    g_dps.erase(std::unique(g_dps.begin(), g_dps.end(),
        [](const FileDP& a, const FileDP& b) { return a.x0 == b.x0 && a.x1 == b.x1; }), g_dps.end());
    g_dpCount = g_dps.size(); h.nDP = g_dps.size();
    std::string tmp = fname + ".tmp";
    FILE* p = fopen(tmp.c_str(), "wb"); if (!p) return false;
    bool ok = fwrite(&h, sizeof h, 1, p) == 1;
    if (ok && !g_dps.empty()) ok = fwrite(g_dps.data(), sizeof(FileDP), g_dps.size(), p) == g_dps.size();
    ok = (fclose(p) == 0) && ok;
    if (!ok) return false;
#ifdef _WIN32
    std::remove(fname.c_str());
#endif
    return std::rename(tmp.c_str(), fname.c_str()) == 0;
}

static u64 sum_ops(Counter* c, int n) { u64 s = 0; for (int i = 0; i < n; i++) s += c[i].v.load(std::memory_order_relaxed); return s; }

// ============================================================================
//  MODES 1 et 2 : generation des Tame
// ============================================================================
static int run_tame(Header h, const std::string& fname, std::vector<FileDP>&& existing, u64 targetDP, int threads, int G) {
    set_cfg(h); build_jumps();
    g_dps = std::move(existing); g_dpCount = g_dps.size();
    const u64 prevOps = h.tameOps;
    g_stop = false; g_sigint = 0;
    signal(SIGINT, on_sig); signal(SIGTERM, on_sig);
    Counter* cnt = new Counter[threads];
    Sink sink = [&](std::vector<DPRec>& v) {
        std::lock_guard<std::mutex> lk(g_mtx);
        for (auto& r : v) {
            u128 d = (u128)r.dist;
            g_dps.push_back(FileDP{r.x0, r.x1, (u64)d, (u64)(d >> 64)});
        }
        g_dpCount += v.size();
    };
    Rng sr; sr.seed((u64)Clock::now().time_since_epoch().count() ^ h.nDP ^ h.tameOps);
    u64 base = sr.next();
    std::vector<std::thread> th;
    for (int t = 0; t < threads; t++) th.emplace_back(worker, t, false, PT_INF(), &cnt[t], sink, G, base);
    printf("\n[Tame] Demarrage : %d threads x %d kangourous. Ctrl+C = arret + sauvegarde.\n\n", threads, G);

    auto t0 = Clock::now(), tLast = t0, tSave = t0;
    u64 lastOps = 0; double speed = 0;
    const double stepsPerDP = std::pow(2.0, h.dpBits);
    while (!g_stop) {
        std::this_thread::sleep_for(std::chrono::milliseconds(200));
        if (g_sigint) { g_stop = true; break; }
        auto now = Clock::now();
        if (secs(tLast, now) >= 1.0) {
            u64 ops = sum_ops(cnt, threads);
            double dt = secs(tLast, now);
            double inst = (double)(ops - lastOps) / dt;
            speed = speed == 0 ? inst : 0.8 * speed + 0.2 * inst;
            lastOps = ops; tLast = now;
            u64 cntDP = g_dpCount.load();
            double total = (double)(prevOps + ops);
            double el = secs(t0, now);
            char eta[64] = "--"; char pct[48] = "";
            if (targetDP) {
                double remaining = ((double)targetDP - (double)cntDP) * stepsPerDP;
                snprintf(eta, sizeof eta, "%s", fmt_time(remaining > 0 && speed > 0 ? remaining / speed : 0).c_str());
                snprintf(pct, sizeof pct, " (%.2f%%)", 100.0 * (double)cntDP / (double)targetDP);
            }
            printf("\r[Tame] ops: %s | vitesse: %s/s | ecoule: %s | reste: %s | DP: %llu%s | RAM: %s   ",
                   fmt_si(total).c_str(), fmt_si(speed).c_str(), fmt_time(el).c_str(), eta,
                   (ull)cntDP, pct, fmt_bytes((double)cntDP * 32).c_str());
            fflush(stdout);
            if (targetDP && cntDP >= targetDP) {
                Header hh = h; hh.tameOps = prevOps + ops; save_file(fname, hh);   // dedoublonne
                if (g_dpCount.load() >= targetDP) break;
            }
        }
        if (secs(tSave, now) >= 600) {   // sauvegarde automatique toutes les 10 min
            Header hh = h; hh.tameOps = prevOps + sum_ops(cnt, threads);
            save_file(fname, hh); tSave = Clock::now();
        }
    }
    g_stop = true;
    for (auto& t : th) t.join();
    Header hh = h; hh.tameOps = prevOps + sum_ops(cnt, threads);
    bool ok = save_file(fname, hh);
    printf("\n\n[Tame] %s : %llu points distingues, %s operations Tame au total (%s).\n",
           ok ? "Sauvegarde OK" : "ERREUR de sauvegarde", (ull)g_dpCount.load(), fmt_si((double)hh.tameOps).c_str(), fname.c_str());
    printf("       Pour continuer plus tard : mode 2 puis numero de fichier.\n");
    delete[] cnt;
    return ok ? 0 : 1;
}

// ============================================================================
//  MODE 3 : kangourous Wild contre la table Tame
// ============================================================================
struct WRec { u64 x1; s128 dist; int sgn; };
struct SolveResult { bool found = false; u128 key = 0; double ops = 0; };

static SolveResult solve_key(const pt& Q, const std::vector<FileDP>& tame, double expectedOps, int threads, int G, bool quiet) {
    SolveResult res;
    const u128 H = C.H, N = (u128)1 << C.B;
    pt cG = mulG(H);
    pt Qp = ec_add(Q, ec_neg(cG));     // Q' = Q - c*G  ->  x = k - c  dans (-H, H]
    auto verify = [&](u128 k) -> bool { pt P = mulG(k); return !P.inf && fe_eq(P.x, Q.x) && fe_eq(P.y, Q.y); };
    if (Qp.inf) { res.found = true; res.key = H; return res; }

    std::atomic<bool> solved(false); std::mutex rm;
    u128 solK = 0;
    auto cand = [&](s128 x) {
        s128 k = (s128)H + x;
        if (k < 1 || (u128)k > N) return;
        if (!verify((u128)k)) return;
        std::lock_guard<std::mutex> lk(rm);
        if (!solved.load()) { solK = (u128)k; solved = true; g_stop = true; }
    };
    g_candidate = cand;
    std::unordered_map<u64, WRec> wmap; std::mutex wm;
    std::atomic<u64> wildDP(0);
    Sink sink = [&](std::vector<DPRec>& v) {
        for (auto& r : v) {
            wildDP++;
            FileDP key{r.x0, r.x1, 0, 0};
            auto it = std::lower_bound(tame.begin(), tame.end(), key, cmp_dp);
            if (it != tame.end() && it->x0 == r.x0 && it->x1 == r.x1) {
                s128 at = (s128)(((u128)it->dhi << 64) | it->dlo);
                cand((s128)r.sgn * (at - r.dist));        // s*x + a_w = a_tame
                continue;
            }
            std::lock_guard<std::mutex> lk(wm);
            auto f = wmap.find(r.x0);
            if (f == wmap.end()) wmap[r.x0] = WRec{r.x1, r.dist, r.sgn};
            else if (f->second.x1 == r.x1 && f->second.sgn == -r.sgn) {   // Wild/Wild de signes opposes
                s128 df = f->second.dist - r.dist;
                if ((df & 1) == 0) cand((s128)r.sgn * (df / 2));
            }
        }
    };
    g_stop = false; g_sigint = 0;
    Counter* cnt = new Counter[threads];
    Rng sr; sr.seed((u64)Clock::now().time_since_epoch().count() ^ Q.x.d[0]);
    u64 base = sr.next();
    std::vector<std::thread> th;
    for (int t = 0; t < threads; t++) th.emplace_back(worker, t, true, Qp, &cnt[t], sink, G, base);

    auto t0 = Clock::now(), tLast = t0; u64 lastOps = 0; double speed = 0;
    while (!g_stop) {
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if (g_sigint) { g_stop = true; break; }
        auto now = Clock::now();
        if (!quiet && secs(tLast, now) >= 1.0) {
            u64 ops = sum_ops(cnt, threads); double dt = secs(tLast, now);
            double inst = (double)(ops - lastOps) / dt;
            speed = speed == 0 ? inst : 0.8 * speed + 0.2 * inst;
            lastOps = ops; tLast = now;
            double el = secs(t0, now);
            double prob = 1.0 - std::exp(-(double)ops / expectedOps);
            printf("\r[Wild] ops: %s | vitesse: %s/s | ecoule: %s | moyenne attendue: %s ops (~%s) | proba deja trouvee: %.1f%% | DP wild: %llu   ",
                   fmt_si((double)ops).c_str(), fmt_si(speed).c_str(), fmt_time(el).c_str(),
                   fmt_si(expectedOps).c_str(), fmt_time(speed > 0 ? expectedOps / speed : -1).c_str(),
                   100.0 * prob, (ull)wildDP.load());
            fflush(stdout);
        }
    }
    g_stop = true;
    for (auto& t : th) t.join();
    res.ops = (double)sum_ops(cnt, threads);
    delete[] cnt;
    g_candidate = nullptr;
    if (solved) { res.found = true; res.key = solK; }
    return res;
}

// ============================================================================
//  Interface (menu / arguments)
// ============================================================================
static std::string ask(const std::string& q, const std::string& def) {
    printf("%s", q.c_str()); if (!def.empty()) printf(" [%s]", def.c_str()); printf(" : "); fflush(stdout);
    std::string s; if (!std::getline(std::cin, s)) return def;
    size_t a = s.find_first_not_of(" \t\r\n"), b = s.find_last_not_of(" \t\r\n");
    s = a == std::string::npos ? "" : s.substr(a, b - a + 1);
    return s.empty() ? def : s;
}
static void default_dp(int B, int& d, u64& nDP) {
    double T = 2.0 * std::pow(2.0, B / 2.0), nd = std::pow(2.0, 22);
    d = (int)std::lround(std::log2(T / nd)); if (d < 4) d = 4; if (d > 40) d = 40;
    nDP = (u64)(T / std::pow(2.0, d)); if (nDP < 1) nDP = 1;
}
static void save_solution(const pt& Q, u128 k, const char* fname) {
    pt P = mulG(k);
    uint8_t kb[32]; u128_be32(k, kb);
    std::string txt = "=== CLE PRIVEE TROUVEE ===\n";
    txt += "Cle publique : " + pub_hex(Q) + "\n";
    txt += "Cle privee (hex)     : " + to_hex(kb, 32) + "\n";
    txt += "Cle privee (decimal) : " + u128_dec(k) + "\n";
    txt += "Cle privee (WIF compresse) : " + wif_compressed(k) + "\n";
    txt += std::string("Verification k*G == Q : ") + ((!P.inf && fe_eq(P.x, Q.x) && fe_eq(P.y, Q.y)) ? "OK" : "ECHEC") + "\n\n";
    printf("\n\n%s", txt.c_str());
    FILE* f = fopen(fname, "a"); if (f) { fputs(txt.c_str(), f); fclose(f); printf("(enregistre dans %s)\n", fname); }
}
static int resolve_file_arg(const std::string& s, std::string& fname) {
    char* e; long n = strtol(s.c_str(), &e, 10);
    if (*e == 0 && n > 0) fname = tame_name((int)n); else fname = s;
    return file_exists(fname) ? 0 : 1;
}
static void list_files() {
    bool any = false;
    for (int n = 1; n < 1000; n++) {
        Header h; std::string f = tame_name(n);
        if (!file_exists(f)) continue;
        if (!read_header(f, h)) continue;
        if (!any) printf("Fichiers Tame existants :\n"); any = true;
        printf("  %3d : %s  | intervalle 2^%u | DP bits %u | %llu DP | %s ops | %s\n", n, f.c_str(), h.B, h.dpBits,
               (ull)h.nDP, fmt_si((double)h.tameOps).c_str(), fmt_bytes(72.0 + 32.0 * (double)h.nDP).c_str());
    }
    if (!any) printf("Aucun fichier tame_NNN.dp dans le dossier courant.\n");
}

static void selftest() {
    init_tables();
    int bad = 0;
    auto chk = [&](bool c, const char* n) { printf("  [%s] %s\n", c ? "OK" : "ECHEC", n); if (!c) bad++; };
    pt P2 = mulG(2), P3 = mulG(3);
    uint8_t b[32]; fe_get_be(P2.x, b);
    chk(to_hex(b, 32) == "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5", "x(2G)");
    fe_get_be(P3.x, b);
    chk(to_hex(b, 32) == "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9", "x(3G)");
    chk(on_curve(mulG(((u128)1 << 79) + 12345)), "point sur la courbe");
    chk(wif_compressed(1) == "KwDiBf89QgGbjEhKnhXJuH7LrciVrZi3qYjgd9M7rFU73sVHnoWn", "WIF de la cle 1");
    chk(pub_hex(mulG(1)) == "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", "pubkey de la cle 1");
    Rng r; r.seed(7); bool okf = true;
    for (int i = 0; i < 2000; i++) {
        fe a, c, d, e, f2;
        for (int k = 0; k < 4; k++) { a.d[k] = r.next(); c.d[k] = r.next(); }
        if (r.next() & 1) a.d[3] = ~0ULL; if (fe_ge_p(a)) fe_addC(a); if (fe_ge_p(c)) fe_addC(c);
        fe_mul(d, a, c); fe_mul(e, c, a); if (!fe_eq(d, e)) okf = false;
        fe_sqr(e, a); fe_mul(f2, a, a); if (!fe_eq(e, f2)) okf = false;
        fe_add(d, a, c); fe_sub(e, d, c); if (!fe_eq(e, a)) okf = false;
        if (!fe_is_zero(a)) { fe_inv(d, a); fe_mul(e, d, a); if (!fe_eq(e, ONE)) okf = false; }
    }
    chk(okf, "arithmetique du corps (mul/sqr/add/sub/inv)");
    pt Q; chk(parse_pubkey(pub_hex(P3), Q) && fe_eq(Q.y, P3.y), "decompression de cle publique");
    printf(bad ? "ECHEC\n" : "Tous les tests sont OK\n");
}

int main(int argc, char** argv) {
#ifdef _WIN32
    SetConsoleOutputCP(CP_UTF8);
#endif
    int mode = 0, threads = (int)std::thread::hardware_concurrency(), G = 256, B = 80, dpBits = -1, bench = 0;
    long long nDPArg = -1; std::string fileArg, keyArg, pubOf;
    double ts = -1, ws = -1;
    if (threads < 1) threads = 1;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i]; auto nx = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
        if (a == "-m") mode = atoi(nx().c_str());
        else if (a == "-t") threads = std::max(1, atoi(nx().c_str()));
        else if (a == "-g") G = std::max(8, atoi(nx().c_str()));
        else if (a == "-r") B = atoi(nx().c_str());
        else if (a == "-d") dpBits = atoi(nx().c_str());
        else if (a == "-n") nDPArg = atoll(nx().c_str());
        else if (a == "-f") fileArg = nx();
        else if (a == "-k") keyArg = nx();
        else if (a == "--bench") bench = atoi(nx().c_str());
        else if (a == "--ts") ts = atof(nx().c_str());
        else if (a == "--ws") ws = atof(nx().c_str());
        else if (a == "--pub") pubOf = nx();
        else if (a == "--selftest") { selftest(); return 0; }
        else if (a == "-h" || a == "--help") {
            printf("Usage : %s [-m 1|2|3] [-r bits] [-d dpBits] [-n nbDP] [-t threads] [-g lot] [-f fichier|numero] [-k pubkey|fichier]\n"
                   "        %s --selftest | --pub <cle_privee_hex>\n", argv[0], argv[0]);
            return 0;
        }
    }
    if (ts > 0) C.tameSpread = ts;
    if (ws > 0) C.wildSpread = ws;
    printf("==============================================================\n");
    printf("  Kangaroo secp256k1 - Tame precalcules / Wild  (symetrie +/-)\n");
    printf("==============================================================\n");
    printf("Initialisation des tables...\n"); fflush(stdout);
    init_tables();
    if (!pubOf.empty()) {
        std::vector<uint8_t> b; u128 k = 0;
        if (pubOf.size() > 2 && pubOf[0] == '0' && pubOf[1] == 'x') { parse_hex(pubOf, b); for (uint8_t c : b) k = (k << 8) | c; }
        else { for (char c : pubOf) k = k * 10 + (u128)(c - '0'); }
        printf("%s\n", pub_hex(mulG(k)).c_str()); return 0;
    }
    if (G < 8) G = 8;

    if (mode == 0) {
        printf("\n  1) Creer un fichier de points distingues Tame\n"
               "  2) Continuer un fichier Tame inacheve\n"
               "  3) Charger un fichier Tame et resoudre une cle publique (Wild)\n\n");
        mode = atoi(ask("Mode", "1").c_str());
    }

    if (mode == 1) {
        int Bq = B;
        if (argc <= 1 || true) Bq = atoi(ask("Intervalle : 1 .. 2^B, B =", std::to_string(B)).c_str());
        if (Bq < 24 || Bq > 100) { printf("B doit etre entre 24 et 100.\n"); return 1; }
        int dd; u64 nn; default_dp(Bq, dd, nn);
        if (dpBits >= 0) dd = dpBits;
        if (nDPArg > 0) nn = (u64)nDPArg;
        dd = atoi(ask("Bits des points distingues (DP = x avec d zeros de tete)", std::to_string(dd)).c_str());
        if (dd < 0 || dd > 56) { printf("dpBits invalide.\n"); return 1; }
        // si l'utilisateur change dd, on recalcule le nombre de DP pour garder ~2*sqrt(N) operations
        if (dpBits < 0 && nDPArg <= 0) nn = std::max<u64>(1, (u64)(2.0 * std::pow(2.0, Bq / 2.0) / std::pow(2.0, dd)));
        nn = (u64)atoll(ask("Nombre de DP a generer (0 = jusqu'a Ctrl+C)", std::to_string(nn)).c_str());
        threads = std::max(1, atoi(ask("Threads", std::to_string(threads)).c_str()));
        double sqrtN = std::pow(2.0, Bq / 2.0), T = (double)nn * std::pow(2.0, dd);
        double fsize = 72.0 + 32.0 * (double)nn;
        printf("\n--- Estimation ---\n");
        if (nn) {
            printf("  Operations Tame prevues : %s  (= %.2f x sqrt(N))\n", fmt_si(T).c_str(), T / sqrtN);
            printf("  Taille fichier .dp      : %s   |   RAM pendant la generation : ~%s\n", fmt_bytes(fsize).c_str(), fmt_bytes(fsize * 1.5).c_str());
            printf("  Effort Wild moyen ensuite (1 cle) : ~%s operations (= %.2f x sqrt(N))\n",
                   fmt_si(KAPPA * std::pow(2.0, Bq) / 2.0 / T).c_str(), KAPPA * std::pow(2.0, Bq) / 2.0 / T / sqrtN);
        } else printf("  Sans limite : 32 octets par DP, soit ~%s par million de DP.\n", fmt_bytes(32e6).c_str());
        double av = mem_available();
        if (av > 0) { printf("  RAM disponible          : %s\n", fmt_bytes(av).c_str()); if (fsize * 1.5 > av * 0.9) printf("  ATTENTION : memoire probablement insuffisante -> augmentez les bits DP.\n"); }
        Header h; memset(&h, 0, sizeof h); memcpy(h.magic, "KTAME1\0\0", 8);
        h.version = 1; h.B = Bq; h.dpBits = dd; h.NJ = 256; h.mb = default_mb(Bq, dd);
        Rng r; r.seed((u64)Clock::now().time_since_epoch().count()); h.seed = r.next();
        int n = 1; while (file_exists(tame_name(n))) n++;
        std::string fn = tame_name(n);
        printf("  Fichier : %s  (dossier courant)\n\n", fn.c_str());
        ask("Appuyez sur Entree pour demarrer", "");
        std::vector<FileDP> empty;
        return run_tame(h, fn, std::move(empty), nn, threads, G);
    }

    if (mode == 2) {
        std::string fn = fileArg;
        if (fn.empty()) { list_files(); fn = ask("Numero (ou nom) du fichier a continuer", "1"); }
        std::string f2; if (resolve_file_arg(fn, f2)) { printf("Fichier introuvable : %s\n", f2.c_str()); return 1; }
        Header h; std::vector<FileDP> v;
        if (!load_file(f2, h, v)) { printf("Fichier invalide.\n"); return 1; }
        double sqrtN = std::pow(2.0, h.B / 2.0);
        printf("Fichier %s : intervalle 2^%u, DP bits %u, %llu DP, %s operations (%.2f x sqrt(N)).\n",
               f2.c_str(), h.B, h.dpBits, (ull)h.nDP, fmt_si((double)h.tameOps).c_str(), (double)h.tameOps / sqrtN);
        u64 cur = h.nDP, nn = nDPArg > 0 ? (u64)nDPArg : cur * 2;
        nn = (u64)atoll(ask("Nombre total de DP visé (0 = jusqu'a Ctrl+C)", std::to_string(nn)).c_str());
        threads = std::max(1, atoi(ask("Threads", std::to_string(threads)).c_str()));
        double fsize = 72.0 + 32.0 * (double)nn;
        if (nn) printf("  Taille finale estimee : %s | RAM ~%s | operations Tame ~ %.2f x sqrt(N)\n", fmt_bytes(fsize).c_str(), fmt_bytes(fsize * 1.5).c_str(),
                       (double)nn * std::pow(2.0, h.dpBits) / sqrtN);
        double av = mem_available();
        if (av > 0 && nn && fsize * 1.5 > av * 0.9) printf("  ATTENTION : memoire probablement insuffisante.\n");
        return run_tame(h, f2, std::move(v), nn, threads, G);
    }

    if (mode == 3) {
        std::string fn = fileArg;
        if (fn.empty()) { list_files(); fn = ask("Numero (ou nom) du fichier Tame a charger", "1"); }
        std::string f2; if (resolve_file_arg(fn, f2)) { printf("Fichier introuvable : %s\n", f2.c_str()); return 1; }
        Header h; std::vector<FileDP> tame;
        if (!load_file(f2, h, tame)) { printf("Fichier invalide.\n"); return 1; }
        set_cfg(h); build_jumps();
        std::sort(tame.begin(), tame.end(), cmp_dp);
        double sqrtN = std::pow(2.0, h.B / 2.0), Neff = (double)tame.size() * std::pow(2.0, h.dpBits);
        double expected = std::max(1.0, KAPPA * std::pow(2.0, h.B) / 2.0 / std::max(1.0, Neff));
        printf("Charge : %llu DP, intervalle [1, 2^%u], %s ops Tame (%.2f x sqrt(N)).\n", (ull)tame.size(), h.B, fmt_si((double)h.tameOps).c_str(), (double)h.tameOps / sqrtN);
        printf("Effort Wild moyen estime : ~%s operations (%.2f x sqrt(N)).\n", fmt_si(expected).c_str(), expected / sqrtN);
        std::vector<pt> keys;
        if (bench > 0) {
            Rng r; r.seed((u64)Clock::now().time_since_epoch().count());
            for (int i = 0; i < bench; i++) { u128 k = 1 + r.next128() % ((u128)1 << h.B); keys.push_back(mulG(k)); }
        } else {
            std::string in = keyArg;
            if (in.empty()) in = ask("Cle(s) publique(s) hex (compressee/non compressee) ou fichier texte", "");
            std::vector<std::string> toks;
            std::string content;
            if (FILE* f = fopen(in.c_str(), "r")) { char ln[1024]; while (fgets(ln, sizeof ln, f)) content += ln, content += ' '; fclose(f); } else content = in;
            for (char& c : content) if (c == ',' || c == ';' || c == '\n' || c == '\r' || c == '\t') c = ' ';
            size_t p = 0;
            while (p < content.size()) {
                while (p < content.size() && content[p] == ' ') p++;
                size_t q = p; while (q < content.size() && content[q] != ' ') q++;
                if (q > p) toks.push_back(content.substr(p, q - p));
                p = q;
            }
            for (auto& t : toks) { pt Q; if (parse_pubkey(t, Q)) keys.push_back(Q); else printf("Cle ignoree (invalide) : %s\n", t.c_str()); }
        }
        if (keys.empty()) { printf("Aucune cle valide.\n"); return 1; }
        if (bench <= 0) threads = std::max(1, atoi(ask("Threads", std::to_string(threads)).c_str()));
        signal(SIGINT, on_sig); signal(SIGTERM, on_sig);
        double totalOps = 0; int nfound = 0;
        for (size_t i = 0; i < keys.size(); i++) {
            if (bench <= 0) printf("\n[Wild] Cle %zu/%zu : %s\n", i + 1, keys.size(), pub_hex(keys[i]).c_str());
            auto t0 = Clock::now();
            SolveResult r = solve_key(keys[i], tame, expected, threads, G, bench > 0);
            totalOps += r.ops;
            if (r.found) {
                nfound++;
                if (bench > 0) printf("  cle %zu : %.3g ops wild (%.3f x sqrt(N)) en %.1fs\n", i + 1, r.ops, r.ops / sqrtN, secs(t0, Clock::now()));
                else { printf("\n[Wild] Trouvee apres %s operations (%s)\n", fmt_si(r.ops).c_str(), fmt_time(secs(t0, Clock::now())).c_str()); save_solution(keys[i], r.key, "solution.txt"); }
            } else { printf("\n[Wild] Arret avant solution.\n"); break; }
        }
        if (bench > 0) {
            double avgW = totalOps / std::max(1, nfound);
            double T = Neff;
            printf("\nBENCH : %d/%zu resolues | wild moyen = %.3g (%.3f x sqrtN) | tame (DP) = %.3g (%.3f x sqrtN) | K total = %.3f | kappa = %.3f\n",
                   nfound, keys.size(), avgW, avgW / sqrtN, T, T / sqrtN, (avgW + T) / sqrtN, avgW / (std::pow(2.0, h.B) / 2.0 / T));
        }
        return 0;
    }
    printf("Mode invalide.\n");
    return 1;
}
