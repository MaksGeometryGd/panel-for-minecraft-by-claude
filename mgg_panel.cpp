// MGG panel — поиск функций внутри процесса игры (libminecraftpe.so, 32-bit ARM / Thumb-2).
// Подгружается через System.loadLibrary("mggpanel"), поднимает панель на http://127.0.0.1:8765/?t=<токен>
//
// Возможности: поиск по сигнатуре байтов, поиск строк, xref строки -> код (Thumb literal pool),
// старт функции (эвристика), hex-просмотр, патч байтов с откатом, хуки (если собрано с Dobby).
// Все адреса в панели — смещения от базы библиотеки (как в radare2/Ghidra), в hex.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <string>
#include <vector>
#include <map>
#include <array>
#include <atomic>
#include <thread>
#include <mutex>
#include <utility>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <dirent.h>
#include <climits>
#include <algorithm>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>

#ifdef __ANDROID__
#include <android/log.h>
#define LOGI(...) __android_log_print(ANDROID_LOG_INFO, "MGG", __VA_ARGS__)
#else
#define LOGI(...) do { fprintf(stderr, "[MGG] "); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } while (0)
#endif

#ifndef MGG_PORT
#define MGG_PORT 8765
#endif
#ifndef MGG_TOKEN
#define MGG_TOKEN "mgg"            // поменяй при сборке: -DMGG_TOKEN=\"секрет\"
#endif
#ifndef MGG_TARGET_LIB
#define MGG_TARGET_LIB "libminecraftpe.so"
#endif

#ifdef MGG_HAS_DOBBY
#include "dobby.h"
// Если у твоей версии Dobby другие типы параметров — правь только эти две строки.
#define MGG_HOOK(addr, rep, orig) DobbyHook((void *)(addr), (dobby_dummy_func_t)(rep), (dobby_dummy_func_t *)(orig))
#define MGG_UNHOOK(addr) DobbyDestroy((void *)(addr))
#endif

typedef std::string Str;
typedef std::map<Str, Str> Params;

// ---------------------------------------------------------------- образ библиотеки
struct Seg { uintptr_t s, e; bool r, w, x; };
struct Img { uintptr_t base = 0; std::vector<Seg> segs; };

static bool loadImg(Img &im) {
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f) return false;
    char line[1024];
    uintptr_t lo = ~(uintptr_t)0;
    while (fgets(line, sizeof line, f)) {
        if (!strstr(line, MGG_TARGET_LIB)) continue;
        unsigned long s, e; char perms[8] = {0};
        if (sscanf(line, "%lx-%lx %7s", &s, &e, perms) != 3) continue;
        Seg g{(uintptr_t)s, (uintptr_t)e, perms[0] == 'r', perms[1] == 'w', perms[2] == 'x'};
        im.segs.push_back(g);
        if (g.s < lo) lo = g.s;
    }
    fclose(f);
    im.base = im.segs.empty() ? 0 : lo;
    return !im.segs.empty();
}

static const Seg *segAt(const Img &im, uintptr_t a, size_t n) {
    for (const Seg &g : im.segs) if (a >= g.s && a + n <= g.e && g.r) return &g;
    return nullptr;
}

static inline uint16_t rd16(uintptr_t a) { uint16_t v; memcpy(&v, (const void *)a, 2); return v; }
static inline uint32_t rd32(uintptr_t a) { uint32_t v; memcpy(&v, (const void *)a, 4); return v; }

static Str hx(uintptr_t v) { char b[32]; snprintf(b, sizeof b, "0x%lX", (unsigned long)v); return b; }

// ---------------------------------------------------------------- разбор параметров
static Str urlDecode(const Str &s) {
    Str o;
    for (size_t i = 0; i < s.size(); i++) {
        if (s[i] == '+') o += ' ';
        else if (s[i] == '%' && i + 2 < s.size() && isxdigit((unsigned char)s[i + 1]) && isxdigit((unsigned char)s[i + 2])) {
            o += (char)strtol(s.substr(i + 1, 2).c_str(), nullptr, 16);
            i += 2;
        } else o += s[i];
    }
    return o;
}

static Params parseQuery(const Str &qs) {
    Params p;
    size_t i = 0;
    while (i <= qs.size()) {
        size_t j = qs.find('&', i);
        if (j == Str::npos) j = qs.size();
        Str kv = qs.substr(i, j - i);
        if (!kv.empty()) {
            size_t eq = kv.find('=');
            if (eq == Str::npos) p[urlDecode(kv)] = "";
            else p[urlDecode(kv.substr(0, eq))] = urlDecode(kv.substr(eq + 1));
        }
        i = j + 1;
    }
    return p;
}

static Str P(const Params &q, const char *k, const char *d = "") {
    auto it = q.find(k);
    return it == q.end() ? Str(d) : it->second;
}

static bool hexNum(const Params &q, const char *k, uintptr_t &v) {   // всегда hex, "0x" необязателен
    auto it = q.find(k);
    if (it == q.end() || it->second.empty()) return false;
    char *e = nullptr;
    v = (uintptr_t)strtoull(it->second.c_str(), &e, 16);
    return e && *e == 0;
}

static size_t decNum(const Params &q, const char *k, size_t d) {
    auto it = q.find(k);
    if (it == q.end() || it->second.empty()) return d;
    return (size_t)strtoull(it->second.c_str(), nullptr, 10);
}

// "F0 B5 ?? 03AF" -> байты, -1 = маска
static bool parseSig(const Str &p, std::vector<int> &pat, Str &err) {
    size_t i = 0;
    while (i < p.size()) {
        while (i < p.size() && isspace((unsigned char)p[i])) i++;
        size_t j = i;
        while (j < p.size() && !isspace((unsigned char)p[j])) j++;
        Str t = p.substr(i, j - i);
        i = j;
        if (t.empty()) continue;
        if (t.find_first_not_of('?') == Str::npos) { for (size_t k = 0; k < (t.size() + 1) / 2; k++) pat.push_back(-1); continue; }
        if (t.size() % 2) { err = "нечётная длина токена: " + t; return false; }
        for (size_t k = 0; k < t.size(); k += 2) {
            if (!isxdigit((unsigned char)t[k]) || !isxdigit((unsigned char)t[k + 1])) { err = "не hex: " + t; return false; }
            pat.push_back((int)strtol(t.substr(k, 2).c_str(), nullptr, 16));
        }
    }
    if (pat.empty()) { err = "пустая сигнатура"; return false; }
    return true;
}

// ---------------------------------------------------------------- поиск
static Str scanSig(const Img &im, const std::vector<int> &pat, bool allSegs, size_t maxr) {
    int first = -1;
    for (size_t i = 0; i < pat.size(); i++) if (pat[i] >= 0) { first = (int)i; break; }
    if (first < 0) return "в сигнатуре только маски\n";
    Str out; size_t found = 0;
    for (const Seg &g : im.segs) {
        if (!g.r || (!allSegs && !g.x)) continue;
        size_t n = g.e - g.s;
        if (n < pat.size()) continue;
        const uint8_t *p = (const uint8_t *)g.s;
        size_t lim = n - pat.size();
        for (size_t i = 0; i <= lim; i++) {
            if (p[i + first] != (uint8_t)pat[first]) continue;
            bool ok = true;
            for (size_t k = 0; k < pat.size(); k++) if (pat[k] >= 0 && p[i + k] != (uint8_t)pat[k]) { ok = false; break; }
            if (!ok) continue;
            out += hx(g.s + i - im.base) + "\n";
            if (++found >= maxr) { out += "...лимит " + std::to_string(maxr) + "\n"; return out; }
        }
    }
    return found ? out : "не найдено\n";
}

static Str scanStr(const Img &im, const Str &needle, bool icase, size_t maxr) {
    if (needle.empty()) return "пустая строка\n";
    Str out; size_t found = 0;
    auto lc = [&](unsigned char c) { return icase ? (unsigned char)tolower(c) : c; };
    for (const Seg &g : im.segs) {
        if (!g.r) continue;
        size_t n = g.e - g.s;
        if (n < needle.size()) continue;
        const uint8_t *p = (const uint8_t *)g.s;
        size_t lim = n - needle.size();
        unsigned char f0 = lc((unsigned char)needle[0]);
        for (size_t i = 0; i <= lim; i++) {
            if (lc(p[i]) != f0) continue;
            bool ok = true;
            for (size_t k = 1; k < needle.size(); k++) if (lc(p[i + k]) != lc((unsigned char)needle[k])) { ok = false; break; }
            if (!ok) continue;
            size_t b = i;                                           // начало C-строки
            while (b > 0 && i - b < 200 && p[b - 1] >= 32 && p[b - 1] < 127) b--;
            Str txt;
            for (size_t k = b; k < n && txt.size() < 160 && p[k] >= 32 && p[k] < 127; k++) txt += (char)p[k];
            out += hx(g.s + b - im.base) + "  \"" + txt + "\"\n";
            i = b + txt.size();                                     // не дублировать матчи в той же строке
            if (++found >= maxr) { out += "...лимит " + std::to_string(maxr) + "\n"; return out; }
        }
    }
    return found ? out : "не найдено\n";
}

// эвристика: ближайший назад push {..., lr}
static uintptr_t fnStart(const Img &im, uintptr_t a, size_t maxBack = 0x4000) {
    a &= ~(uintptr_t)1;
    for (size_t d = 0; d <= maxBack; d += 2) {
        if (a < d + im.base) break;
        uintptr_t x = a - d;
        if (!segAt(im, x, 4)) break;
        uint16_t h = rd16(x);
        if ((h & 0xFF00) == 0xB500) return x;                          // push {.., lr}
        if (h == 0xE92D && (rd16(x + 2) & 0x4000)) return x;          // push.w {.., lr}
    }
    return 0;
}

// xref: Thumb "ldr rN,[pc,#imm]" (16/32-бит) + "add rN, pc" -> адрес в [lo,hi)
static Str findXref(const Img &im, uintptr_t lo, uintptr_t hi, size_t maxr) {
    Str out; size_t found = 0;
    for (const Seg &g : im.segs) {
        if (!g.r || !g.x) continue;
        for (uintptr_t a = g.s; a + 2 <= g.e; a += 2) {
            uint16_t h = rd16(a);
            int rt; uintptr_t lit; size_t len;
            if ((h & 0xF800) == 0x4800) {
                rt = (h >> 8) & 7; len = 2;
                lit = ((a + 4) & ~(uintptr_t)3) + (uintptr_t)(h & 0xFF) * 4;
            } else if ((h == 0xF8DF || h == 0xF85F) && a + 4 <= g.e) {
                uint16_t h2 = rd16(a + 2);
                rt = (h2 >> 12) & 15; len = 4;
                uintptr_t imm = h2 & 0xFFF, bs = (a + 4) & ~(uintptr_t)3;
                lit = (h == 0xF8DF) ? bs + imm : bs - imm;
            } else continue;
            if (rt == 13 || rt == 15) continue;
            if (!segAt(im, lit, 4)) continue;
            uint32_t L = rd32(lit);
            uint16_t want = rt < 8 ? (uint16_t)(0x4478 | rt) : (uint16_t)(0x44F8 | (rt - 8));
            for (int k = 0; k < 12; k++) {
                uintptr_t b = a + len + 2 * (uintptr_t)k;
                if (b + 2 > g.e) break;
                if (rd16(b) != want) continue;
                uintptr_t S = (uintptr_t)L + b + 4;
                if (S >= lo && S < hi) {
                    uintptr_t fs = fnStart(im, a);
                    out += "ссылка в " + hx(a - im.base) + "  -> функция ~" + (fs ? hx(fs - im.base) : Str("?")) + "\n";
                    if (++found >= maxr) { out += "...лимит\n"; return out; }
                }
                break;
            }
        }
    }
    // второй проход: movw rN,#lo ; movt rN,#hi ; ... ; add rN, pc
    for (const Seg &g : im.segs) {
        if (!g.r || !g.x) continue;
        for (uintptr_t a = g.s; a + 8 <= g.e; a += 2) {
            uint16_t h1 = rd16(a), h2 = rd16(a + 2);
            if ((h1 & 0xFBF0) != 0xF240 || (h2 & 0x8000)) continue;                 // movw
            int rd = (h2 >> 8) & 15;
            uint32_t lw = ((uint32_t)(h1 & 0xF) << 12) | ((uint32_t)((h1 >> 10) & 1) << 11) | ((uint32_t)((h2 >> 12) & 7) << 8) | (h2 & 0xFF);
            uint16_t m1 = rd16(a + 4), m2 = rd16(a + 6);
            if ((m1 & 0xFBF0) != 0xF2C0 || (m2 & 0x8000) || (int)((m2 >> 8) & 15) != rd) continue;   // movt того же регистра
            uint32_t hw = ((uint32_t)(m1 & 0xF) << 12) | ((uint32_t)((m1 >> 10) & 1) << 11) | ((uint32_t)((m2 >> 12) & 7) << 8) | (m2 & 0xFF);
            uint32_t L = (hw << 16) | lw;
            uint16_t want = rd < 8 ? (uint16_t)(0x4478 | rd) : (uint16_t)(0x44F8 | (rd - 8));
            for (int k = 0; k < 12; k++) {
                uintptr_t b = a + 8 + 2 * (uintptr_t)k;
                if (b + 2 > g.e) break;
                if (rd16(b) != want) continue;
                uintptr_t S = (uintptr_t)L + b + 4;
                if (S >= lo && S < hi) {
                    uintptr_t fs = fnStart(im, a);
                    out += "ссылка (movw/movt) в " + hx(a - im.base) + "  -> функция ~" + (fs ? hx(fs - im.base) : Str("?")) + "\n";
                    if (++found >= maxr) { out += "...лимит\n"; return out; }
                }
                break;
            }
        }
    }
    return found ? out : "ссылок не найдено (ищутся Thumb: literal pool и movw/movt + add pc)\n";
}

static Str hexdump(const Img &im, uintptr_t off, size_t n) {
    uintptr_t a = im.base + off;
    const Seg *g = segAt(im, a, 1);
    if (!g) return "адрес вне читаемых сегментов\n";
    if (a + n > g->e) n = g->e - a;
    if (n > 4096) n = 4096;
    Str out; char b[8];
    for (size_t i = 0; i < n; i += 16) {
        out += hx(off + i) + ": ";
        for (size_t k = 0; k < 16 && i + k < n; k++) { snprintf(b, sizeof b, "%02X ", *(const uint8_t *)(a + i + k)); out += b; }
        out += "\n";
    }
    return out;
}

// ---------------------------------------------------------------- дизассемблер Thumb/Thumb-2 (подмножество, в стиле radare2)
static const char *RN[16] = {"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "sb", "sl", "fp", "ip", "sp", "lr", "pc"};
static const char *CCN[16] = {"eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"};

static Str dn(uint32_t v) { char b[16]; if (v < 10) snprintf(b, sizeof b, "%u", v); else snprintf(b, sizeof b, "0x%x", v); return b; }
static Str ds(int32_t v) { return v < 0 ? "-" + dn((uint32_t)(-v)) : dn((uint32_t)v); }
static Str h0(uint32_t v) { char b[16]; snprintf(b, sizeof b, "0x%x", v); return b; }
static Str h8(uint32_t v) { char b[16]; snprintf(b, sizeof b, "0x%08x", v); return b; }
static int32_t sext(uint32_t v, int bits) { uint32_t m = 1u << (bits - 1); return (int32_t)((v ^ m) - m); }
static uint32_t ror32(uint32_t v, int r) { r &= 31; return r ? (v >> r) | (v << (32 - r)) : v; }
static Str rlist(uint32_t m) {
    Str s = "{"; bool f = true;
    for (int i = 0; i < 16; i++) if (m & (1u << i)) { if (!f) s += ", "; s += RN[i]; f = false; }
    return s + "}";
}
static Str memop(int rn, int32_t imm) { return imm ? Str("[") + RN[rn] + ", " + ds(imm) + "]" : Str("[") + RN[rn] + "]"; }
static Str sreg(int n) { return "s" + std::to_string(n); }
static Str dreg(int n) { return "d" + std::to_string(n); }

static uint32_t thumbExpand(uint32_t i12) {
    uint32_t b = i12 & 0xFF;
    if ((i12 >> 10) == 0) {
        switch ((i12 >> 8) & 3) {
            case 0: return b;
            case 1: return (b << 16) | b;
            case 2: return (b << 24) | (b << 8);
            default: return (b << 24) | (b << 16) | (b << 8) | b;
        }
    }
    return ror32(0x80 | (i12 & 0x7F), (i12 >> 7) & 0x1F);
}

static Str litNote(const Img &im, uint32_t voff) {
    uintptr_t a = im.base + voff;
    if (!segAt(im, a, 4)) return "";
    return "      ; [" + h0(voff) + "]=" + h0(rd32(a));
}

struct Br { int kind; uint32_t target; int cond; };     // kind: 1 bl, 2 b.w, 3 blx, 4 b<cond>.w
static bool decodeBr(uint16_t h1, uint16_t h2, uint32_t addr, Br &r) {
    if ((h1 >> 11) != 0x1E || !(h2 & 0x8000)) return false;
    uint32_t pc = addr + 4, S = (h1 >> 10) & 1, J1 = (h2 >> 13) & 1, J2 = (h2 >> 11) & 1;
    if ((h2 & 0xD000) == 0x8000) {
        uint32_t cond = (h1 >> 6) & 0xF;
        if (cond >= 14) return false;
        uint32_t imm = (S << 20) | (J2 << 19) | (J1 << 18) | ((uint32_t)(h1 & 0x3F) << 12) | ((uint32_t)(h2 & 0x7FF) << 1);
        r.kind = 4; r.cond = (int)cond; r.target = pc + (uint32_t)sext(imm, 21);
        return true;
    }
    uint32_t I1 = (~(J1 ^ S)) & 1, I2 = (~(J2 ^ S)) & 1, imm10 = h1 & 0x3FF;
    if ((h2 & 0xD000) == 0x9000 || (h2 & 0xD000) == 0xD000) {
        uint32_t imm = (S << 24) | (I1 << 23) | (I2 << 22) | (imm10 << 12) | ((uint32_t)(h2 & 0x7FF) << 1);
        r.kind = (h2 & 0x4000) ? 1 : 2; r.cond = 0; r.target = pc + (uint32_t)sext(imm, 25);
        return true;
    }
    if ((h2 & 0xD001) == 0xC000) {
        uint32_t imm = (S << 24) | (I1 << 23) | (I2 << 22) | (imm10 << 12) | ((uint32_t)((h2 >> 1) & 0x3FF) << 2);
        r.kind = 3; r.cond = 0; r.target = (pc & ~3u) + (uint32_t)sext(imm, 25);
        return true;
    }
    return false;
}

static Str dis16(const Img &im, uint32_t addr, uint16_t h) {
    uint32_t pc = addr + 4;
    int rd, rn, rm;
    switch (h >> 11) {
        case 0: case 1: case 2: {
            rd = h & 7; rm = (h >> 3) & 7; uint32_t imm = (h >> 6) & 0x1F; int op = h >> 11;
            if (op == 0 && imm == 0) return Str("movs ") + RN[rd] + ", " + RN[rm];
            if (op != 0 && imm == 0) imm = 32;
            return Str(op == 0 ? "lsls " : op == 1 ? "lsrs " : "asrs ") + RN[rd] + ", " + RN[rm] + ", " + dn(imm);
        }
        case 3: {
            rd = h & 7; rn = (h >> 3) & 7; int x = (h >> 6) & 7; bool imm = (h >> 10) & 1, sub = (h >> 9) & 1;
            return Str(sub ? "subs " : "adds ") + RN[rd] + ", " + RN[rn] + ", " + (imm ? dn(x) : Str(RN[x]));
        }
        case 4: return Str("movs ") + RN[(h >> 8) & 7] + ", " + dn(h & 0xFF);
        case 5: return Str("cmp ") + RN[(h >> 8) & 7] + ", " + dn(h & 0xFF);
        case 6: return Str("adds ") + RN[(h >> 8) & 7] + ", " + dn(h & 0xFF);
        case 7: return Str("subs ") + RN[(h >> 8) & 7] + ", " + dn(h & 0xFF);
        case 8: {
            if ((h >> 10) == 0x10) {
                static const char *alu[16] = {"ands", "eors", "lsls", "lsrs", "asrs", "adcs", "sbcs", "rors", "tst", "rsbs", "cmp", "cmn", "orrs", "muls", "bics", "mvns"};
                rd = h & 7; rm = (h >> 3) & 7; int op = (h >> 6) & 0xF;
                if (op == 9) return Str("rsbs ") + RN[rd] + ", " + RN[rm] + ", 0";
                if (op == 13) return Str("muls ") + RN[rd] + ", " + RN[rm] + ", " + RN[rd];
                return Str(alu[op]) + " " + RN[rd] + ", " + RN[rm];
            }
            int op = (h >> 8) & 3; rm = (h >> 3) & 0xF; rd = (h & 7) | ((h >> 4) & 8);
            if (op == 0) return Str("add ") + RN[rd] + ", " + RN[rm];
            if (op == 1) return Str("cmp ") + RN[rd] + ", " + RN[rm];
            if (op == 2) return Str("mov ") + RN[rd] + ", " + RN[rm];
            return Str((h & 0x80) ? "blx " : "bx ") + RN[rm];
        }
        case 9: {
            rd = (h >> 8) & 7; uint32_t lit = (pc & ~3u) + (uint32_t)(h & 0xFF) * 4;
            return Str("ldr ") + RN[rd] + ", [" + h8(lit) + "]" + litNote(im, lit);
        }
        case 10: case 11: {
            static const char *m[8] = {"str", "strh", "strb", "ldrsb", "ldr", "ldrh", "ldrb", "ldrsh"};
            rd = h & 7; rn = (h >> 3) & 7; rm = (h >> 6) & 7;
            return Str(m[(h >> 9) & 7]) + " " + RN[rd] + ", [" + RN[rn] + ", " + RN[rm] + "]";
        }
        case 12: case 13: case 14: case 15: case 16: case 17: {
            static const char *m[6] = {"str", "ldr", "strb", "ldrb", "strh", "ldrh"};
            int k = (h >> 11) - 12; rd = h & 7; rn = (h >> 3) & 7; uint32_t imm = (h >> 6) & 0x1F;
            imm *= (k < 2) ? 4 : (k < 4) ? 1 : 2;
            return Str(m[k]) + " " + RN[rd] + ", " + memop(rn, (int32_t)imm);
        }
        case 18: case 19:
            return Str((h >> 11) == 18 ? "str " : "ldr ") + RN[(h >> 8) & 7] + ", " + memop(13, (int32_t)(h & 0xFF) * 4);
        case 20: { uint32_t lit = (pc & ~3u) + (uint32_t)(h & 0xFF) * 4; return Str("adr ") + RN[(h >> 8) & 7] + ", " + h0(lit); }
        case 21: return Str("add ") + RN[(h >> 8) & 7] + ", sp, " + dn((uint32_t)(h & 0xFF) * 4);
        case 22: case 23: {
            if ((h & 0xFF00) == 0xB000) return Str((h & 0x80) ? "sub sp, " : "add sp, ") + dn((uint32_t)(h & 0x7F) * 4);
            if ((h & 0xF500) == 0xB100) {
                uint32_t i = (h >> 9) & 1, imm5 = (h >> 3) & 0x1F;
                return Str((h & 0x0800) ? "cbnz " : "cbz ") + RN[h & 7] + ", " + h0(pc + ((i << 6) | (imm5 << 1)));
            }
            if ((h & 0xFF00) == 0xB200) { static const char *m[4] = {"sxth", "sxtb", "uxth", "uxtb"}; return Str(m[(h >> 6) & 3]) + " " + RN[h & 7] + ", " + RN[(h >> 3) & 7]; }
            if ((h & 0xFE00) == 0xB400) return "push " + rlist((h & 0xFF) | ((h & 0x100) ? 0x4000 : 0));
            if ((h & 0xFE00) == 0xBC00) return "pop " + rlist((h & 0xFF) | ((h & 0x100) ? 0x8000 : 0));
            if ((h & 0xFF00) == 0xBA00) { int o = (h >> 6) & 3; if (o != 2) return Str(o == 0 ? "rev " : o == 1 ? "rev16 " : "revsh ") + RN[h & 7] + ", " + RN[(h >> 3) & 7]; }
            if ((h & 0xFF00) == 0xBE00) return "bkpt " + dn(h & 0xFF);
            if ((h & 0xFF00) == 0xBF00) {
                int mask = h & 0xF, fc = (h >> 4) & 0xF;
                if (mask == 0) { static const char *hn[5] = {"nop", "yield", "wfe", "wfi", "sev"}; return fc < 5 ? hn[fc] : "hint"; }
                int tz = 0; while (!((mask >> tz) & 1)) tz++;
                int n = 4 - tz; Str s = "it";
                for (int i = 1; i < n; i++) s += (((mask >> (4 - i)) & 1) == (fc & 1)) ? "t" : "e";
                return s + " " + CCN[fc];
            }
            break;
        }
        case 24: case 25: {
            rn = (h >> 8) & 7; uint32_t regs = h & 0xFF; bool ld = (h >> 11) == 25;
            bool wb = !(ld && (regs & (1u << rn)));
            return Str(ld ? "ldm " : "stm ") + RN[rn] + (wb ? "!, " : ", ") + rlist(regs);
        }
        case 26: case 27: {
            int c = (h >> 8) & 0xF;
            if (c == 0xF) return "svc " + dn(h & 0xFF);
            if (c == 0xE) return "udf " + dn(h & 0xFF);
            return Str("b") + CCN[c] + " " + h0(pc + (uint32_t)(sext(h & 0xFF, 8) * 2));
        }
        case 28: return "b " + h0(pc + (uint32_t)(sext(h & 0x7FF, 11) * 2));
    }
    char b[24]; snprintf(b, sizeof b, ".hword 0x%04x", h); return b;
}

static Str shiftStr(int type, uint32_t imm5) {
    if (imm5 == 0 && type == 0) return "";
    if (imm5 == 0 && type == 3) return ", rrx";
    if (imm5 == 0) imm5 = 32;
    static const char *t[4] = {"lsl", "lsr", "asr", "ror"};
    return Str(", ") + t[type] + " " + dn(imm5);
}

static Str dis32(const Img &im, uint32_t addr, uint16_t h1, uint16_t h2) {
    uint32_t pc = addr + 4;
    uint32_t hi = h1 >> 11;
    Br br;
    if (decodeBr(h1, h2, addr, br)) {
        if (br.kind == 1) return "bl " + h0(br.target);
        if (br.kind == 2) return "b.w " + h0(br.target);
        if (br.kind == 3) return "blx " + h0(br.target);
        return Str("b") + CCN[br.cond] + ".w " + h0(br.target);
    }
    // --- load/store single
    if ((h1 & 0xFE00) == 0xF800) {
        int size = (h1 >> 5) & 3, sign = (h1 >> 8) & 1, L = (h1 >> 4) & 1, rn = h1 & 0xF, rt = (h2 >> 12) & 0xF;
        const char *nm = nullptr;
        if (size != 3) {
            if (L) nm = !sign ? (size == 0 ? "ldrb" : size == 1 ? "ldrh" : "ldr") : (size == 0 ? "ldrsb" : size == 1 ? "ldrsh" : nullptr);
            else if (!sign) nm = size == 0 ? "strb" : size == 1 ? "strh" : "str";
        }
        if (nm) {
            Str mn = Str(nm) + ".w ";
            if (rn == 15 && L) {
                uint32_t imm = h2 & 0xFFF, lit = ((h1 >> 7) & 1) ? (pc & ~3u) + imm : (pc & ~3u) - imm;
                return mn + RN[rt] + ", [" + h8(lit) + "]" + litNote(im, lit);
            }
            if (h1 & 0x80) return mn + RN[rt] + ", " + memop(rn, (int32_t)(h2 & 0xFFF));
            if ((h2 & 0x800) && (h2 & 0xF00) != 0xE00) {
                int P = (h2 >> 10) & 1, U = (h2 >> 9) & 1, W = (h2 >> 8) & 1; int32_t imm = h2 & 0xFF; if (!U) imm = -imm;
                if (P) return mn + RN[rt] + ", " + memop(rn, imm) + (W ? "!" : "");
                return mn + RN[rt] + ", [" + RN[rn] + "], " + ds(imm);
            }
            if ((h2 >> 6) == 0) {
                int rm = h2 & 0xF, sh = (h2 >> 4) & 3;
                return mn + RN[rt] + ", [" + RN[rn] + ", " + RN[rm] + (sh ? ", lsl " + dn(sh) : Str("")) + "]";
            }
        }
    }
    // --- data processing (modified immediate) / plain binary immediate
    if (hi == 0x1E && !(h2 & 0x8000)) {
        int rn = h1 & 0xF, rd = (h2 >> 8) & 0xF;
        uint32_t i = (h1 >> 10) & 1, imm3 = (h2 >> 12) & 7, imm8 = h2 & 0xFF, imm12 = (i << 11) | (imm3 << 8) | imm8;
        if (!(h1 & 0x200)) {
            int op = (h1 >> 5) & 0xF, S = (h1 >> 4) & 1; uint32_t v = thumbExpand(imm12);
            static const char *nm[16] = {"and", "bic", "orr", "orn", "eor", "", "", "", "add", "", "adc", "sbc", "", "sub", "rsb", ""};
            Str sfx = S ? "s.w " : ".w ";
            if (rd == 15 && S && (op == 0 || op == 4 || op == 8 || op == 13)) {
                const char *t = op == 0 ? "tst.w " : op == 4 ? "teq.w " : op == 8 ? "cmn.w " : "cmp.w ";
                return Str(t) + RN[rn] + ", " + dn(v);
            }
            if (op == 2 && rn == 15) return Str(S ? "movs.w " : "mov.w ") + RN[rd] + ", " + dn(v);
            if (op == 3 && rn == 15) return Str(S ? "mvns.w " : "mvn.w ") + RN[rd] + ", " + dn(v);
            if (nm[op][0]) return Str(nm[op]) + sfx + RN[rd] + ", " + RN[rn] + ", " + dn(v);
        } else {
            int op = (h1 >> 4) & 0x1F;
            if (op == 0x04 || op == 0x0C) {
                uint32_t imm16 = ((uint32_t)(h1 & 0xF) << 12) | imm12;
                return Str(op == 0x04 ? "movw " : "movt ") + RN[rd] + ", " + dn(imm16);
            }
            if (op == 0x00) return rn == 15 ? Str("adr.w ") + RN[rd] + ", " + h0((pc & ~3u) + imm12) : Str("addw ") + RN[rd] + ", " + RN[rn] + ", " + dn(imm12);
            if (op == 0x0A) return rn == 15 ? Str("adr.w ") + RN[rd] + ", " + h0((pc & ~3u) - imm12) : Str("subw ") + RN[rd] + ", " + RN[rn] + ", " + dn(imm12);
            if (op == 0x14 || op == 0x1C) {
                uint32_t lsb = (imm3 << 2) | ((h2 >> 6) & 3), w = (h2 & 0x1F) + 1;
                return Str(op == 0x14 ? "sbfx " : "ubfx ") + RN[rd] + ", " + RN[rn] + ", " + dn(lsb) + ", " + dn(w);
            }
            if (op == 0x16) {
                uint32_t lsb = (imm3 << 2) | ((h2 >> 6) & 3), msb = h2 & 0x1F, w = msb >= lsb ? msb - lsb + 1 : 0;
                if (rn == 15) return Str("bfc ") + RN[rd] + ", " + dn(lsb) + ", " + dn(w);
                return Str("bfi ") + RN[rd] + ", " + RN[rn] + ", " + dn(lsb) + ", " + dn(w);
            }
        }
    }
    // --- data processing (shifted register)
    if ((h1 & 0xFE00) == 0xEA00) {
        int op = (h1 >> 5) & 0xF, S = (h1 >> 4) & 1, rn = h1 & 0xF, rd = (h2 >> 8) & 0xF, rm = h2 & 0xF, type = (h2 >> 4) & 3;
        uint32_t imm5 = (((h2 >> 12) & 7) << 2) | ((h2 >> 6) & 3);
        static const char *nm[16] = {"and", "bic", "orr", "orn", "eor", "", "pkh", "", "add", "", "adc", "sbc", "", "sub", "rsb", ""};
        if (rd == 15 && S && (op == 0 || op == 4 || op == 8 || op == 13)) {
            const char *t = op == 0 ? "tst.w " : op == 4 ? "teq.w " : op == 8 ? "cmn.w " : "cmp.w ";
            return Str(t) + RN[rn] + ", " + RN[rm] + shiftStr(type, imm5);
        }
        if (op == 2 && rn == 15) {
            if (type == 0 && imm5 == 0) return Str(S ? "movs.w " : "mov.w ") + RN[rd] + ", " + RN[rm];
            if (type == 3 && imm5 == 0) return Str(S ? "rrxs " : "rrx ") + RN[rd] + ", " + RN[rm];
            static const char *t[4] = {"lsl", "lsr", "asr", "ror"};
            return Str(t[type]) + (S ? "s.w " : ".w ") + RN[rd] + ", " + RN[rm] + ", " + dn(imm5 ? imm5 : 32);
        }
        if (op == 3 && rn == 15) return Str(S ? "mvns.w " : "mvn.w ") + RN[rd] + ", " + RN[rm] + shiftStr(type, imm5);
        if (nm[op][0]) return Str(nm[op]) + (S ? "s.w " : ".w ") + RN[rd] + ", " + RN[rn] + ", " + RN[rm] + shiftStr(type, imm5);
    }
    // --- register-controlled shifts
    if ((h1 & 0xFF80) == 0xFA00 && (h2 & 0xF0F0) == 0xF000) {
        static const char *t[4] = {"lsl", "lsr", "asr", "ror"};
        return Str(t[(h1 >> 5) & 3]) + (((h1 >> 4) & 1) ? "s.w " : ".w ") + RN[(h2 >> 8) & 0xF] + ", " + RN[h1 & 0xF] + ", " + RN[h2 & 0xF];
    }
    // --- multiply / divide
    if ((h1 & 0xFFF0) == 0xFB00) {
        int rn = h1 & 0xF, rd = (h2 >> 8) & 0xF, rm = h2 & 0xF, ra = (h2 >> 12) & 0xF;
        if (ra == 15 && (h2 & 0xF0) == 0) return Str("mul ") + RN[rd] + ", " + RN[rn] + ", " + RN[rm];
        if ((h2 & 0xF0) == 0) return Str("mla ") + RN[rd] + ", " + RN[rn] + ", " + RN[rm] + ", " + RN[ra];
        if ((h2 & 0xF0) == 0x10) return Str("mls ") + RN[rd] + ", " + RN[rn] + ", " + RN[rm] + ", " + RN[ra];
    }
    if (((h1 & 0xFFF0) == 0xFB90 || (h1 & 0xFFF0) == 0xFBB0) && (h2 & 0xF0F0) == 0xF0F0)
        return Str((h1 & 0x20) ? "udiv " : "sdiv ") + RN[(h2 >> 8) & 0xF] + ", " + RN[h1 & 0xF] + ", " + RN[h2 & 0xF];
    if (((h1 & 0xFFF0) == 0xFBA0 || (h1 & 0xFFF0) == 0xFB80) && (h2 & 0xF0) == 0)
        return Str((h1 & 0x20) ? "umull " : "smull ") + RN[(h2 >> 12) & 0xF] + ", " + RN[(h2 >> 8) & 0xF] + ", " + RN[h1 & 0xF] + ", " + RN[h2 & 0xF];
    // --- ldm/stm, push/pop
    if ((h1 & 0xFE40) == 0xE800) {
        int op = (h1 >> 7) & 3, W = (h1 >> 5) & 1, L = (h1 >> 4) & 1, rn = h1 & 0xF;
        if (op == 2 && !L && W && rn == 13) return "push.w " + rlist(h2);
        if (op == 1 && L && W && rn == 13) return "pop.w " + rlist(h2);
        if (op == 1 || op == 2) return Str(L ? "ldm" : "stm") + (op == 1 ? "" : "db") + ".w " + RN[rn] + (W ? "!, " : ", ") + rlist(h2);
    }
    if ((h1 & 0xFFF0) == 0xE8D0 && (h2 & 0xFFE0) == 0xF000) {
        bool tbh = h2 & 0x10;
        return Str(tbh ? "tbh [" : "tbb [") + RN[h1 & 0xF] + ", " + RN[h2 & 0xF] + (tbh ? ", lsl 1]" : "]");
    }
    if ((h1 & 0xFE40) == 0xE840) {
        int P = (h1 >> 8) & 1, U = (h1 >> 7) & 1, W = (h1 >> 5) & 1, L = (h1 >> 4) & 1, rn = h1 & 0xF;
        if (P || W) {
            int32_t imm = (int32_t)(h2 & 0xFF) * 4; if (!U) imm = -imm;
            Str o = Str(L ? "ldrd " : "strd ") + RN[(h2 >> 12) & 0xF] + ", " + RN[(h2 >> 8) & 0xF] + ", ";
            if (P) return o + memop(rn, imm) + (W ? "!" : "");
            return o + "[" + RN[rn] + "], " + ds(imm);
        }
    }
    // --- VFP (одинарная/двойная точность, основные команды)
    if ((h1 >> 10) == 0x3B) {
        int cp = (h2 >> 8) & 0xF, sz = cp & 1;
        if ((cp & 0xE) == 0xA) {
            int D = (h1 >> 6) & 1, vd = (h2 >> 12) & 0xF, N = (h2 >> 7) & 1, M = (h2 >> 5) & 1, vn = h1 & 0xF, vm = h2 & 0xF;
            auto R = [&](int v, int x) { return sz ? dreg((x << 4) | v) : sreg((v << 1) | x); };
            if ((h1 & 0xFF20) == 0xED00) {
                int L = (h1 >> 4) & 1, U = (h1 >> 7) & 1, rn = h1 & 0xF; uint32_t imm = (uint32_t)(h2 & 0xFF) * 4;
                Str nm = L ? "vldr " : "vstr ";
                if (rn == 15) { uint32_t lit = U ? (pc & ~3u) + imm : (pc & ~3u) - imm; return nm + R(vd, D) + ", [" + h8(lit) + "]" + litNote(im, lit); }
                return nm + R(vd, D) + ", " + memop(rn, U ? (int32_t)imm : -(int32_t)imm);
            }
            if ((h1 & 0xFFBF) == 0xEEB4 && (h2 & 0x0E50) == 0x0A40)
                return Str((h2 & 0x80) ? "vcmpe" : "vcmp") + (sz ? ".f64 " : ".f32 ") + R(vd, D) + ", " + R(vm, M);
            if ((h1 & 0xFFBF) == 0xEEB5 && (h2 & 0x0E7F) == 0x0A40)
                return Str((h2 & 0x80) ? "vcmpe" : "vcmp") + (sz ? ".f64 " : ".f32 ") + R(vd, D) + ", 0";
            if (h1 == 0xEEF1 && (h2 & 0x0FFF) == 0x0A10) { int rt = (h2 >> 12) & 0xF; return rt == 15 ? "vmrs apsr_nzcv, fpscr" : Str("vmrs ") + RN[rt] + ", fpscr"; }
            if (h1 == 0xEEE1 && (h2 & 0x0FFF) == 0x0A10) return Str("vmsr fpscr, ") + RN[(h2 >> 12) & 0xF];
            if ((h1 & 0xFFE0) == 0xEE00 && (h2 & 0x0F7F) == 0x0A10) {
                int rt = (h2 >> 12) & 0xF; Str s = sreg((vn << 1) | N);
                return ((h1 >> 4) & 1) ? Str("vmov ") + RN[rt] + ", " + s : "vmov " + s + ", " + RN[rt];
            }
            if ((h2 & 0x0E10) == 0x0A00) {
                int op6 = (h2 >> 6) & 1; const char *t = nullptr;
                if ((h1 & 0xFFB0) == 0xEE30) t = op6 ? "vsub" : "vadd";
                else if ((h1 & 0xFFB0) == 0xEE20) t = op6 ? "vnmul" : "vmul";
                else if ((h1 & 0xFFB0) == 0xEE80 && !op6) t = "vdiv";
                if (t) return Str(t) + (sz ? ".f64 " : ".f32 ") + R(vd, D) + ", " + R(vn, N) + ", " + R(vm, M);
                if ((h1 & 0xFFB0) == 0xEEB0 && op6 && vn <= 1) {
                    const char *u = vn == 0 ? ((h2 & 0x80) ? "vabs" : "vmov") : ((h2 & 0x80) ? "vsqrt" : "vneg");
                    return Str(u) + (sz ? ".f64 " : ".f32 ") + R(vd, D) + ", " + R(vm, M);
                }
            }
        }
    }
    char b[40]; snprintf(b, sizeof b, ".inst.w 0x%04x%04x", h1, h2); return b;
}

static Str disOne(const Img &im, uintptr_t a, int &len) {
    uint32_t v = (uint32_t)(a - im.base);
    const Seg *g = segAt(im, a, 2);
    if (!g) { len = 2; return "?"; }
    uint16_t h = rd16(a);
    if ((h >> 11) >= 0x1D) {
        if (a + 4 > g->e) { len = 2; char b[24]; snprintf(b, sizeof b, ".hword 0x%04x", h); return b; }
        len = 4;
        return dis32(im, v, h, rd16(a + 2));
    }
    len = 2;
    return dis16(im, v, h);
}

static Str disasm(const Img &im, uintptr_t off, size_t n) {
    uintptr_t a = (im.base + off) & ~(uintptr_t)1;
    Str out; char b[16];
    for (size_t i = 0; i < n; i++) {
        if (!segAt(im, a, 2)) break;
        int len; Str t = disOne(im, a, len);
        Str bytes;
        for (int k = 0; k < len; k++) { snprintf(b, sizeof b, "%02x", *(const uint8_t *)(a + k)); bytes += b; }
        char hd[32]; snprintf(hd, sizeof hd, "0x%08x  ", (unsigned)(a - im.base));
        out += hd + bytes + (len == 2 ? "      " : "  ") + t + "\n";
        a += len;
    }
    return out.empty() ? "адрес вне читаемых сегментов\n" : out;
}

// кто вызывает функцию: bl / blx / b.w на заданное смещение
static Str findCallers(const Img &im, uint32_t target, size_t maxr) {
    target &= ~1u;
    Str out; size_t found = 0;
    for (const Seg &g : im.segs) {
        if (!g.r || !g.x) continue;
        for (uintptr_t a = g.s; a + 4 <= g.e; a += 2) {
            uint16_t h1 = rd16(a);
            if ((h1 & 0xF800) != 0xF000) continue;
            Br br;
            if (!decodeBr(h1, rd16(a + 2), (uint32_t)(a - im.base), br) || br.kind == 4) continue;
            if (br.target != target) continue;
            uintptr_t fs = fnStart(im, a);
            out += Str(br.kind == 1 ? "bl" : br.kind == 2 ? "b.w" : "blx") + " в " + hx(a - im.base) + "  -> функция ~" + (fs ? hx(fs - im.base) : Str("?")) + "\n";
            if (++found >= maxr) { out += "...лимит\n"; return out; }
        }
    }
    return found ? out : "вызовов не найдено (ищутся только bl/blx/b.w; вызов через указатель или vtable не виден)\n";
}

// ---------------------------------------------------------------- патчи
static std::map<uintptr_t, std::vector<uint8_t>> g_patches;   // смещение -> оригинальные байты

static bool parseBytes(const Str &s, std::vector<uint8_t> &out) {
    std::vector<int> pat; Str err;
    if (!parseSig(s, pat, err)) return false;
    for (int v : pat) { if (v < 0) return false; out.push_back((uint8_t)v); }
    return true;
}

static Str writeMem(const Img &im, uintptr_t off, const std::vector<uint8_t> &b, bool remember) {
    uintptr_t a = im.base + off;
    const Seg *g = segAt(im, a, b.size());
    if (!g) return "адрес вне сегмента\n";
    size_t pg = (size_t)sysconf(_SC_PAGESIZE);
    uintptr_t p = a & ~(uintptr_t)(pg - 1);
    size_t len = ((a + b.size() + pg - 1) & ~(uintptr_t)(pg - 1)) - p;
    int orig = PROT_READ | (g->w ? PROT_WRITE : 0) | (g->x ? PROT_EXEC : 0);
    if (remember && !g_patches.count(off)) g_patches[off] = std::vector<uint8_t>((uint8_t *)a, (uint8_t *)a + b.size());
    if (mprotect((void *)p, len, PROT_READ | PROT_WRITE) != 0) return "mprotect RW не удался\n";
    memcpy((void *)a, b.data(), b.size());
    mprotect((void *)p, len, orig);
    __builtin___clear_cache((char *)a, (char *)(a + b.size()));
    return "ok: записано " + std::to_string(b.size()) + " байт по " + hx(off) + "\n";
}

// ---------------------------------------------------------------- сохранение патчей между запусками
struct Saved { uintptr_t off; std::vector<uint8_t> orig, now; };
static std::vector<Saved> g_saved;
static std::mutex g_mu;

static Str dataDir() {
    const char *e = getenv("MGG_DATA");
    if (e && *e) return e;
    char b[256] = {0};
    FILE *f = fopen("/proc/self/cmdline", "r");
    if (f) { size_t n = fread(b, 1, sizeof b - 1, f); b[n] = 0; fclose(f); }
    Str p = b;
    size_t c = p.find(':');
    if (c != Str::npos) p = p.substr(0, c);
    return "/data/data/" + p;
}
static Str patchFile() { return dataDir() + "/mgg_patches.txt"; }

static Str hexs(const std::vector<uint8_t> &v) {
    Str o; char b[4];
    for (uint8_t x : v) { snprintf(b, sizeof b, "%02X", x); o += b; }
    return o;
}
static bool unhex(const Str &s, std::vector<uint8_t> &o) {
    if (s.empty() || s.size() % 2) return false;
    for (size_t i = 0; i < s.size(); i += 2) {
        if (!isxdigit((unsigned char)s[i]) || !isxdigit((unsigned char)s[i + 1])) return false;
        o.push_back((uint8_t)strtol(s.substr(i, 2).c_str(), nullptr, 16));
    }
    return true;
}
static void saveFile() {
    FILE *f = fopen(patchFile().c_str(), "w");
    if (!f) { LOGI("не могу писать %s", patchFile().c_str()); return; }
    for (const Saved &s : g_saved) fprintf(f, "%lX %s %s\n", (unsigned long)s.off, hexs(s.orig).c_str(), hexs(s.now).c_str());
    fclose(f);
}
static void loadFile() {
    g_saved.clear();
    FILE *f = fopen(patchFile().c_str(), "r");
    if (!f) return;
    char line[2048];
    while (fgets(line, sizeof line, f)) {
        char a[32], o[1024], n[1024];
        if (sscanf(line, "%31s %1023s %1023s", a, o, n) != 3) continue;
        Saved s; s.off = (uintptr_t)strtoull(a, nullptr, 16);
        if (unhex(o, s.orig) && unhex(n, s.now) && s.orig.size() == s.now.size()) g_saved.push_back(s);
    }
    fclose(f);
}

static Str doPatch(const Img &im, uintptr_t off, const std::vector<uint8_t> &b, bool keep) {
    auto it = g_patches.find(off);
    if (it != g_patches.end() && it->second.size() != b.size()) return "по этому смещению уже есть патч другой длины: сначала откати\n";
    Str r = writeMem(im, off, b, true);
    if (r.compare(0, 2, "ok") != 0) return r;
    if (keep) {
        Saved s; s.off = off; s.orig = g_patches[off]; s.now = b;
        for (size_t i = 0; i < g_saved.size(); i++) if (g_saved[i].off == off) { g_saved.erase(g_saved.begin() + i); break; }
        g_saved.push_back(s);
        saveFile();
        r += "сохранён: применится при следующих запусках\n";
    }
    return r;
}

// автоприменение сохранённых патчей через несколько секунд после старта игры
static void autoApply() {
    Img im;
    for (int i = 0; i < 120; i++) { im = Img(); if (loadImg(im)) break; sleep(1); }
    if (im.segs.empty()) return;
    sleep(8);
    std::lock_guard<std::mutex> lk(g_mu);
    Str lock = dataDir() + "/mgg_apply.lock";
    loadFile();
    if (g_saved.empty()) return;
    if (access(lock.c_str(), F_OK) == 0) {                       // прошлый запуск упал, пока патчи применялись
        rename(patchFile().c_str(), (patchFile() + ".disabled").c_str());
        remove(lock.c_str());
        g_saved.clear();
        LOGI("прошлый запуск упал после применения патчей: они отключены (файл .disabled)");
        return;
    }
    FILE *lf = fopen(lock.c_str(), "w"); if (lf) fclose(lf);
    im = Img(); loadImg(im);
    for (const Saved &s : g_saved) {
        uintptr_t a = im.base + s.off;
        if (!segAt(im, a, s.now.size())) { LOGI("патч %lX вне сегмента", (unsigned long)s.off); continue; }
        std::vector<uint8_t> cur((uint8_t *)a, (uint8_t *)a + s.now.size());
        if (cur == s.now) continue;
        if (cur != s.orig) { LOGI("патч %lX пропущен: байты не совпали (другая версия игры?)", (unsigned long)s.off); continue; }
        Str r = writeMem(im, s.off, s.now, true);
        LOGI("автопатч %lX: %s", (unsigned long)s.off, r.c_str());
    }
    std::thread([lock] { sleep(45); remove(lock.c_str()); }).detach();   // игра прожила 45 с: считаем запуск безопасным
}

// ---------------------------------------------------------------- хуки (нужен Dobby)
#ifdef MGG_HAS_DOBBY
struct Slot {
    bool used; void *target; void *orig; int mode; uintptr_t val;     // mode: 0 лог, 1 вернуть val без вызова, 2 вызвать и подменить результат
    uintptr_t off; std::atomic<uint32_t> calls; uintptr_t last[8];
};
static Slot g_slots[16];

template <int N>
static uintptr_t hk(uintptr_t a0, uintptr_t a1, uintptr_t a2, uintptr_t a3, uintptr_t a4, uintptr_t a5, uintptr_t a6, uintptr_t a7) {
    Slot &s = g_slots[N];
    s.calls++;
    s.last[0] = a0; s.last[1] = a1; s.last[2] = a2; s.last[3] = a3; s.last[4] = a4; s.last[5] = a5; s.last[6] = a6; s.last[7] = a7;
    if (s.mode == 1) return s.val;
    uintptr_t r = ((uintptr_t(*)(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t))s.orig)(a0, a1, a2, a3, a4, a5, a6, a7);
    return s.mode == 2 ? s.val : r;
}
template <size_t... I>
static std::array<void *, sizeof...(I)> mkHooks(std::index_sequence<I...>) { return {{(void *)&hk<(int)I>...}}; }
static std::array<void *, 16> g_hk = mkHooks(std::make_index_sequence<16>{});

static Str hooksList() {
    Str out;
    for (int i = 0; i < 16; i++) {
        const Slot &s = g_slots[i];
        if (!s.used) continue;
        const char *m = s.mode == 0 ? "лог" : s.mode == 1 ? "ret" : "set";
        out += "#" + std::to_string(i) + " " + hx(s.off) + " режим=" + m + " val=" + hx(s.val) + " вызовов=" + std::to_string(s.calls.load()) + "\n   арги:";
        for (int k = 0; k < 8; k++) out += " " + hx(s.last[k]);
        out += "\n";
    }
    return out.empty() ? "хуков нет\n" : out;
}
#endif

// ---------------------------------------------------------------- файлы игры (только внутри папок приложения)
static Str baseName(const Str &p) { size_t i = p.rfind('/'); return i == Str::npos ? p : p.substr(i + 1); }

static std::vector<Str> fileRoots() {
    Str d = dataDir(), pkg = baseName(d);
    return {d, "/storage/emulated/0/Android/data/" + pkg, "/sdcard/Android/data/" + pkg, "/storage/emulated/0/games/com.mojang", "/sdcard/games/com.mojang"};
}

static bool allowedPath(const Str &p, Str &real, Str &err) {
    if (p.empty()) { err = "нужен параметр p (путь)"; return false; }
    char buf[PATH_MAX];
    if (!realpath(p.c_str(), buf)) { err = "путь не найден: " + p; return false; }
    real = buf;
    for (const Str &r : fileRoots()) {
        char rb[PATH_MAX];
        if (!realpath(r.c_str(), rb)) continue;
        Str rr = rb;
        if (real == rr || (real.size() > rr.size() && real.compare(0, rr.size(), rr) == 0 && real[rr.size()] == '/')) return true;
    }
    err = "путь вне папок игры (разрешены данные приложения и Android/data/<пакет>)";
    return false;
}

static bool readFile(const Str &path, Str &out, size_t maxn = 1 << 20) {
    FILE *f = fopen(path.c_str(), "rb");
    if (!f) return false;
    char b[4096]; size_t n;
    while ((n = fread(b, 1, sizeof b, f)) > 0 && out.size() < maxn) out.append(b, n);
    fclose(f);
    return true;
}

static bool writeFile(const Str &path, const Str &data) {
    FILE *f = fopen(path.c_str(), "wb");
    if (!f) return false;
    bool ok = fwrite(data.data(), 1, data.size(), f) == data.size();
    fclose(f);
    return ok;
}

static bool backupOnce(const Str &path, const Str &cur) {
    Str bak = path + ".mgg.bak";
    if (access(bak.c_str(), F_OK) == 0) return true;
    return writeFile(bak, cur);
}

static void grepDir(const Str &dir, const Str &needle, int depth, size_t maxr, size_t &found, size_t &scanned, Str &out) {
    if (depth > 8 || found >= maxr || scanned > 30000) return;
    DIR *d = opendir(dir.c_str());
    if (!d) return;
    std::vector<Str> names; struct dirent *e;
    while ((e = readdir(d)) != nullptr) { Str n = e->d_name; if (n != "." && n != "..") names.push_back(n); }
    closedir(d);
    std::sort(names.begin(), names.end());
    for (const Str &n : names) {
        if (found >= maxr) return;
        Str full = dir + "/" + n;
        struct stat st;
        if (lstat(full.c_str(), &st) != 0 || S_ISLNK(st.st_mode)) continue;
        if (S_ISDIR(st.st_mode)) { grepDir(full, needle, depth + 1, maxr, found, scanned, out); continue; }
        if (!S_ISREG(st.st_mode) || st.st_size > (16 << 20) || st.st_size < (off_t)needle.size()) continue;
        scanned++;
        Str data;
        if (!readFile(full, data, 17u << 20)) continue;
        size_t at = 0, per = 0;
        while ((at = data.find(needle, at)) != Str::npos && per < 3 && found < maxr) {
            size_t a0 = at > 40 ? at - 40 : 0, a1 = std::min(data.size(), at + needle.size() + 40);
            Str ctx;
            for (size_t i = a0; i < a1; i++) { unsigned char c = (unsigned char)data[i]; ctx += (c >= 32 && c < 127) ? (char)c : '.'; }
            out += full + "  @" + std::to_string((unsigned long long)at) + "\n    " + ctx + "\n";
            at += needle.size(); per++; found++;
        }
    }
}

static Str fileRoute(const Str &path, const Params &q) {
    Str real, err;
    if (path == "grep") {                                       // поиск текста по файлам (без учёта регистра не умеет)
        Str needle = P(q, "s");
        if (needle.size() < 3) return "нужен текст s, минимум 3 символа\n";
        std::vector<Str> dirs;
        if (P(q, "p").empty()) { for (const Str &r : fileRoots()) { char rb[PATH_MAX]; if (realpath(r.c_str(), rb) && std::find(dirs.begin(), dirs.end(), Str(rb)) == dirs.end()) dirs.push_back(rb); } }
        else { if (!allowedPath(P(q, "p"), real, err)) return err + "\n"; dirs.push_back(real); }
        Str out; size_t found = 0, scanned = 0, maxr = decNum(q, "max", 30);
        for (const Str &d : dirs) grepDir(d, needle, 0, maxr, found, scanned, out);
        return out + "\nпросмотрено файлов: " + std::to_string(scanned) + (found >= maxr ? ", найдено (лимит " + std::to_string(maxr) + ")\n" : ", найдено: " + std::to_string(found) + "\n");
    }
    if (path == "ls") {
        Str p = P(q, "p");
        if (p.empty()) {
            Str o = "папки игры:\n";
            for (const Str &r : fileRoots()) { char rb[PATH_MAX]; if (realpath(r.c_str(), rb)) o += "  " + Str(rb) + "\n"; }
            Str opt = "/storage/emulated/0/Android/data/" + baseName(dataDir()) + "/files/games/com.mojang/minecraftpe/options.txt";
            if (access(opt.c_str(), F_OK) == 0) o += "\noptions.txt:\n  " + opt + "\n";
            return o;
        }
        if (!allowedPath(p, real, err)) return err + "\n";
        DIR *d = opendir(real.c_str());
        if (!d) return "это не папка или нет доступа\n";
        std::vector<Str> names; struct dirent *e;
        while ((e = readdir(d)) != nullptr) { Str n = e->d_name; if (n != "." && n != "..") names.push_back(n); }
        closedir(d);
        std::sort(names.begin(), names.end());
        Str o = real + "\n";
        for (size_t i = 0; i < names.size() && i < 300; i++) {
            struct stat st;
            Str full = real + "/" + names[i];
            if (stat(full.c_str(), &st) == 0) o += (S_ISDIR(st.st_mode) ? "[d] " : "    ") + names[i] + (S_ISDIR(st.st_mode) ? "/" : "  " + std::to_string((long long)st.st_size) + " байт") + "\n";
            else o += "    " + names[i] + "\n";
        }
        if (names.size() > 300) o += "...ещё " + std::to_string(names.size() - 300) + "\n";
        return o;
    }
    if (!allowedPath(P(q, "p"), real, err)) return err + "\n";
    struct stat st;
    if (stat(real.c_str(), &st) != 0 || !S_ISREG(st.st_mode)) return "это не обычный файл\n";
    if (path == "cat") {
        Str d;
        if (!readFile(real, d, 65536)) return "не могу прочитать файл\n";
        return d.empty() ? "(пустой файл)\n" : d;
    }
    Str cur;
    if (path == "setkey") {                                   // формат "ключ:значение" (options.txt)
        Str k = P(q, "k"), v = P(q, "v");
        if (k.empty() || k.find('\n') != Str::npos || v.find('\n') != Str::npos) return "нужны k и v без переводов строк\n";
        if (!readFile(real, cur)) return "не могу прочитать файл\n";
        if (!backupOnce(real, cur)) return "не могу сделать копию .mgg.bak, правка отменена\n";
        Str out, line, prefix = k + ":"; bool done = false; size_t i = 0;
        while (i <= cur.size()) {
            size_t j = cur.find('\n', i);
            bool last = j == Str::npos;
            if (last) j = cur.size();
            line = cur.substr(i, j - i);
            bool cr = !line.empty() && line.back() == '\r';
            if (!done && line.compare(0, prefix.size(), prefix) == 0) { out += prefix + v + (cr ? "\r" : ""); done = true; }
            else out += line;
            if (!last) out += "\n";
            i = j + 1;
            if (last) break;
        }
        if (!done) { if (!out.empty() && out.back() != '\n') out += "\n"; out += prefix + v + "\n"; }
        return writeFile(real, out) ? Str("ok: ") + k + " = " + v + (done ? " (заменено)\n" : " (добавлено)\n") + "копия: " + real + ".mgg.bak\n" : "не удалось записать файл\n";
    }
    if (path == "freplace") {                                 // заменить первое вхождение текста a на b
        Str a = P(q, "a"), b = P(q, "b");
        if (a.empty()) return "нужен параметр a\n";
        if (!readFile(real, cur)) return "не могу прочитать файл\n";
        size_t at = cur.find(a);
        if (at == Str::npos) return "текст не найден\n";
        if (!backupOnce(real, cur)) return "не могу сделать копию .mgg.bak, правка отменена\n";
        cur.replace(at, a.size(), b);
        return writeFile(real, cur) ? "ok: заменено\nкопия: " + real + ".mgg.bak\n" : "не удалось записать файл\n";
    }
    if (path == "frestore") {
        Str bak = real + ".mgg.bak", d;
        if (!readFile(bak, d)) return "копии .mgg.bak нет\n";
        return writeFile(real, d) ? "ok: файл восстановлен из .mgg.bak\n" : "не удалось записать файл\n";
    }
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- память процесса (поиск значений, как в Cheat Engine)
static std::vector<uintptr_t> g_cand;
static int g_csz = 4;

#include <csetjmp>
#include <csignal>
#include <chrono>
static thread_local sigjmp_buf g_jb; static thread_local volatile sig_atomic_t g_guard = 0;
static void segvH(int) { if (g_guard) siglongjmp(g_jb, 1); signal(SIGSEGV, SIG_DFL); }
static bool instSegv() { struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_handler = segvH; sigemptyset(&sa.sa_mask); sa.sa_flags = SA_NODEFER; sigaction(SIGSEGV, &sa, nullptr); sigaction(SIGBUS, &sa, nullptr); return true; }
// безопасное чтение/запись своей памяти напрямую (без /proc/self/mem, он закрыт SELinux)
static bool guarded(void *dst, const void *src, size_t n) {
    static bool inst = instSegv(); (void)inst;
    if (sigsetjmp(g_jb, 1) == 0) { g_guard = 1; memcpy(dst, src, n); g_guard = 0; return true; }
    g_guard = 0; return false;
}
static int memOpen() { return 1; }
static void memClose(int) {}
struct MapR { uintptr_t s, e; };
static std::vector<MapR> memMaps(bool all) {
    std::vector<MapR> v;
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f) return v;
    char line[1024];
    while (fgets(line, sizeof line, f)) {
        unsigned long s, e, off, ino; char perms[8] = {0}, dev[16] = {0}, path[512] = {0};
        int n = sscanf(line, "%lx-%lx %7s %lx %15s %lu %511[^\n]", &s, &e, perms, &off, dev, &ino, path);
        if (n < 6 || perms[0] != 'r' || perms[1] != 'w') continue;
        Str p = n >= 7 ? Str(path) : Str();
        size_t k = p.find_first_not_of(' ');
        p = k == Str::npos ? Str() : p.substr(k);
        if (p == "[vvar]" || p == "[vdso]" || p == "[vectors]" || p.find("/dev/") != Str::npos || p.find("/dri/") != Str::npos) continue;
        if (!all && !p.empty() && p[0] == '/') continue;                // по умолчанию только куча/анонимная память
        v.push_back({(uintptr_t)s, (uintptr_t)e});
    }
    fclose(f);
    return v;
}


static std::vector<unsigned long long> g_prev;
static bool g_cf = false;

static unsigned long long maskSz(unsigned long long v, int sz) { return sz >= 8 ? v : v & ((1ULL << (8 * sz)) - 1); }
static unsigned long long rawOf(const Str &t, int sz, bool isf) {
    if (isf) { float f = strtof(t.c_str(), nullptr); uint32_t u; memcpy(&u, &f, 4); return u; }
    return maskSz((unsigned long long)strtoll(t.c_str(), nullptr, 10), sz);
}
static double numOf(unsigned long long raw, int sz, bool isf) {
    if (isf) { uint32_t u = (uint32_t)raw; float f; memcpy(&f, &u, 4); return f; }
    if (sz == 1) return (int8_t)raw;
    if (sz == 2) return (int16_t)raw;
    return (int32_t)raw;
}
static Str numStr(unsigned long long raw, int sz, bool isf) {
    char b[48];
    if (isf) snprintf(b, sizeof b, "%g", numOf(raw, sz, true)); else snprintf(b, sizeof b, "%lld", (long long)numOf(raw, sz, false));
    return b;
}
static unsigned long long memVal(uintptr_t a, int sz, bool &ok) {
    uint8_t b[8] = {0};
    ok = guarded(b, (const void *)a, sz);
    unsigned long long v = 0;
    for (int i = 0; i < sz; i++) v |= (unsigned long long)b[i] << (8 * i);
    return v;
}
static bool memWrite(uintptr_t a, unsigned long long raw, int sz) {
    uint8_t b[8]; for (int i = 0; i < 8; i++) b[i] = (uint8_t)(raw >> (8 * i));
    return guarded((void *)a, b, sz);
}

static Str memScan(unsigned long long raw, int sz, bool isf, bool all, size_t maxc) {
    g_cand.clear(); g_prev.clear(); g_csz = sz; g_cf = isf;
    uint8_t pat[8]; for (int i = 0; i < 8; i++) pat[i] = (uint8_t)(raw >> (8 * i));
    std::vector<uint8_t> buf(1 << 20);
    size_t regions = 0; unsigned long long bytes = 0;
    for (const MapR &m : memMaps(all)) {
        regions++;
        for (uintptr_t a = m.s; a < m.e;) {
            size_t n = std::min<size_t>(buf.size(), m.e - a);
            if (!guarded(buf.data(), (const void *)a, n)) { a += 4096; continue; }
            bytes += n;
            for (size_t i = 0; i + sz <= n; i += sz) {
                if (memcmp(buf.data() + i, pat, sz) != 0) continue;
                g_cand.push_back(a + i); g_prev.push_back(raw);
                if (g_cand.size() > maxc) { size_t c = g_cand.size(); g_cand.clear(); g_prev.clear(); return "слишком много совпадений (>" + std::to_string(maxc) + "): возьми менее частое значение или сузь позже\n"; (void)c; }
            }
            a += n;
        }
    }
    return "областей: " + std::to_string(regions) + ", просмотрено МБ: " + std::to_string(bytes >> 20) + ", найдено: " + std::to_string(g_cand.size()) + "\n";
}

static Str memNext(const Str &mode, unsigned long long raw) {
    std::vector<uintptr_t> ka; std::vector<unsigned long long> kp;
    for (size_t i = 0; i < g_cand.size(); i++) {
        bool ok; unsigned long long cur = memVal(g_cand[i], g_csz, ok);
        if (!ok) continue;
        unsigned long long pv = g_prev[i];
        bool keep = false;
        if (mode == "eq") keep = cur == raw;
        else if (mode == "same") keep = cur == pv;
        else if (mode == "chg") keep = cur != pv;
        else if (mode == "inc") keep = numOf(cur, g_csz, g_cf) > numOf(pv, g_csz, g_cf);
        else if (mode == "dec") keep = numOf(cur, g_csz, g_cf) < numOf(pv, g_csz, g_cf);
        if (keep) { ka.push_back(g_cand[i]); kp.push_back(cur); }
    }
    g_cand.swap(ka); g_prev.swap(kp);
    return "осталось: " + std::to_string(g_cand.size()) + "\n";
}

// заморозка значений
struct Frz { uintptr_t a; unsigned long long v; int sz; };
static std::vector<Frz> g_frz; static std::mutex g_fm; static bool g_frzTh = false;
static void frzThread() { for (;;) { usleep(30000); std::lock_guard<std::mutex> lk(g_fm); for (const Frz &f : g_frz) memWrite(f.a, f.v, f.sz); } }
static void addFrz(uintptr_t a, unsigned long long v, int sz) {
    std::lock_guard<std::mutex> lk(g_fm);
    for (Frz &f : g_frz) if (f.a == a) { f.v = v; f.sz = sz; return; }
    g_frz.push_back({a, v, sz});
    if (!g_frzTh) { g_frzTh = true; std::thread(frzThread).detach(); }
}

// монитор адреса
struct WState { bool run = false; uintptr_t a = 0; int sz = 4; bool f = false; std::vector<Str> log; unsigned long long last = 0; long long t0 = 0; int gen = 0; };
static WState g_w; static std::mutex g_wm;
static long long nowMs() { return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
static Str watchStart(uintptr_t a, int sz, bool f) {
    bool ok; unsigned long long v = memVal(a, sz, ok);
    if (!ok) return "адрес не читается\n";
    int gen;
    { std::lock_guard<std::mutex> lk(g_wm); g_w.gen++; gen = g_w.gen; g_w.run = true; g_w.a = a; g_w.sz = sz; g_w.f = f; g_w.last = v; g_w.t0 = nowMs(); g_w.log.clear(); }
    std::thread([gen] {
        for (;;) {
            usleep(15000);
            std::lock_guard<std::mutex> lk(g_wm);
            if (!g_w.run || g_w.gen != gen) return;
            bool ok2; unsigned long long x = memVal(g_w.a, g_w.sz, ok2);
            if (ok2 && x != g_w.last) {
                g_w.log.push_back(std::to_string(nowMs() - g_w.t0) + " мс: " + numStr(g_w.last, g_w.sz, g_w.f) + " -> " + numStr(x, g_w.sz, g_w.f));
                if (g_w.log.size() > 200) g_w.log.erase(g_w.log.begin());
                g_w.last = x;
            }
        }
    }).detach();
    return "слежу за " + hx(a) + " (текущее " + numStr(v, sz, f) + ")\n";
}

static Str memRoute(const Str &path, const Params &q) {
    int sz = (int)decNum(q, "sz", 4); if (sz != 1 && sz != 2 && sz != 4) sz = 4;
    bool isf = P(q, "f") == "1"; if (isf) sz = 4;
    Str vs = P(q, "v");
    if (path == "mscan") {
        if (vs.empty()) return "нужно число v\n";
        return memScan(rawOf(vs, sz, isf), sz, isf, P(q, "all") == "1", 2000000);
    }
    if (path == "mnext") {
        if (g_cand.empty()) return "список пуст: сначала «Первый поиск»\n";
        Str m = P(q, "m", "eq");
        if (m == "eq" && vs.empty()) return "нужно число v\n";
        return memNext(m, vs.empty() ? 0 : rawOf(vs, g_csz, g_cf));
    }
    if (path == "mlist") {
        size_t n = decNum(q, "n", 40);
        Str o = "кандидатов: " + std::to_string(g_cand.size()) + " (размер " + std::to_string(g_csz) + (g_cf ? ", float" : "") + ")\n";
        for (size_t i = 0; i < g_cand.size() && i < n; i++) { bool ok; unsigned long long x = memVal(g_cand[i], g_csz, ok); o += hx(g_cand[i]) + "  = " + (ok ? numStr(x, g_csz, g_cf) : Str("?")) + "\n"; }
        return o;
    }
    if (path == "mreset") { g_cand.clear(); g_prev.clear(); return "список сброшен\n"; }
    if (path == "mset" || path == "mfreeze") {
        if (vs.empty()) return "нужно число v\n";
        bool frz = path == "mfreeze";
        if (P(q, "all") == "1") {
            if (g_cand.empty()) return "список пуст\n";
            if (g_cand.size() > 50) return "кандидатов больше 50: сузь поиск, иначе это опасно\n";
            unsigned long long raw = rawOf(vs, g_csz, g_cf); size_t ok = 0;
            for (uintptr_t a : g_cand) { if (memWrite(a, raw, g_csz)) ok++; if (frz) addFrz(a, raw, g_csz); }
            return (frz ? "заморожено " : "записано ") + std::to_string(ok) + " из " + std::to_string(g_cand.size()) + "\n";
        }
        uintptr_t a = 0;
        if (!hexNum(q, "a", a)) return "нужен адрес a (hex)\n";
        unsigned long long raw = rawOf(vs, sz, isf);
        bool ok = memWrite(a, raw, sz);
        if (frz) addFrz(a, raw, sz);
        return ok ? Str(frz ? "заморожено: " : "ok: записано по ") + hx(a) + "\n" : "запись не удалась\n";
    }
    if (path == "mfrlist") {
        std::lock_guard<std::mutex> lk(g_fm);
        if (g_frz.empty()) return "заморозок нет\n";
        Str o; for (const Frz &f : g_frz) o += hx(f.a) + " = " + std::to_string((long long)numOf(f.v, f.sz, false)) + " (" + std::to_string(f.sz) + " б)\n";
        return o;
    }
    if (path == "munfreeze") {
        std::lock_guard<std::mutex> lk(g_fm);
        uintptr_t a = 0;
        if (P(q, "all") == "1" || !hexNum(q, "a", a)) { size_t n = g_frz.size(); g_frz.clear(); return "снято заморозок: " + std::to_string(n) + "\n"; }
        for (size_t i = 0; i < g_frz.size(); i++) if (g_frz[i].a == a) { g_frz.erase(g_frz.begin() + i); return "снято\n"; }
        return "такой заморозки нет\n";
    }
    if (path == "mwatch") {
        uintptr_t a = 0;
        if (!hexNum(q, "a", a)) return "нужен адрес a (hex)\n";
        return watchStart(a, sz, isf);
    }
    if (path == "mwlog") {
        std::lock_guard<std::mutex> lk(g_wm);
        if (!g_w.gen) return "монитор не запускался\n";
        Str o = Str(g_w.run ? "слежу за " : "остановлен: ") + hx(g_w.a) + ", изменений: " + std::to_string(g_w.log.size()) + "\n";
        size_t st = g_w.log.size() > 60 ? g_w.log.size() - 60 : 0;
        for (size_t i = st; i < g_w.log.size(); i++) o += g_w.log[i] + "\n";
        return o;
    }
    if (path == "mwstop") { std::lock_guard<std::mutex> lk(g_wm); g_w.run = false; return "монитор остановлен\n"; }
    if (path == "mdump") {
        uintptr_t a = 0;
        if (!hexNum(q, "a", a)) return "нужен адрес a (hex)\n";
        size_t n = decNum(q, "n", 128); if (n > 1024) n = 1024;
        std::vector<uint8_t> b(n);
        if (!guarded(b.data(), (const void *)a, n)) return "не читается\n";
        Str o; char t[8];
        for (size_t i = 0; i < n; i += 16) { o += hx(a + i) + ": "; for (size_t k = 0; k < 16 && i + k < n; k++) { snprintf(t, sizeof t, "%02X ", b[i + k]); o += t; } o += "\n"; }
        return o;
    }
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- функции (готовые наборы патчей из файла mgg_functions.txt)
// строка: Название|смещение_hex|оригинальные_байты|новые_байты   (одинаковые названия = одна функция)
// профиль: @Название|функция1,функция2
struct FnPart { uintptr_t off; std::vector<uint8_t> orig, now; };
struct FnSet { std::vector<std::pair<Str, std::vector<FnPart>>> fns; std::vector<std::pair<Str, std::vector<Str>>> profs; };
static Str fnFile() { return dataDir() + "/mgg_functions.txt"; }
static Str trimS(Str t) { size_t a = t.find_first_not_of(" \t\r\n"), b = t.find_last_not_of(" \t\r\n"); return a == Str::npos ? Str() : t.substr(a, b - a + 1); }

static FnSet fnLoad() {
    FnSet r; Str txt;
    if (!readFile(fnFile(), txt)) {
        FILE *f = fopen(fnFile().c_str(), "w");
        if (f) { fputs("# Название|смещение_hex|оригинальные_байты|новые_байты\n# одинаковые названия = одна функция (несколько патчей)\n# профиль (набор функций): @Название|функция1,функция2\n", f); fclose(f); }
        return r;
    }
    size_t i = 0;
    while (i <= txt.size()) {
        size_t e = txt.find('\n', i); if (e == Str::npos) e = txt.size();
        Str ln = trimS(txt.substr(i, e - i)); i = e + 1;
        if (ln.empty() || ln[0] == '#') continue;
        if (ln[0] == '@') {
            size_t p = ln.find('|'); if (p == Str::npos) continue;
            std::vector<Str> mem; Str rest = ln.substr(p + 1); size_t j = 0;
            while (j <= rest.size()) { size_t c = rest.find(',', j); if (c == Str::npos) c = rest.size(); Str m = trimS(rest.substr(j, c - j)); if (!m.empty()) mem.push_back(m); j = c + 1; }
            r.profs.push_back({trimS(ln.substr(1, p - 1)), mem});
            continue;
        }
        size_t p1 = ln.find('|'), p2 = p1 == Str::npos ? p1 : ln.find('|', p1 + 1), p3 = p2 == Str::npos ? p2 : ln.find('|', p2 + 1);
        if (p3 == Str::npos) continue;
        Str nm = trimS(ln.substr(0, p1)); FnPart pt;
        pt.off = (uintptr_t)strtoull(trimS(ln.substr(p1 + 1, p2 - p1 - 1)).c_str(), nullptr, 16);
        auto cl = [](Str h) { Str o; for (char c : h) if (isxdigit((unsigned char)c)) o += c; return o; };
        if (!unhex(cl(ln.substr(p2 + 1, p3 - p2 - 1)), pt.orig) || !unhex(cl(ln.substr(p3 + 1)), pt.now) || pt.orig.size() != pt.now.size()) continue;
        bool f = false;
        for (auto &kv : r.fns) if (kv.first == nm) { kv.second.push_back(pt); f = true; break; }
        if (!f) r.fns.push_back({nm, {pt}});
    }
    return r;
}

// 0 = выключена, 1 = включена, 2 = частично, 3 = байты не совпали (другая версия игры)
static int fnState(const Img &im, const std::vector<FnPart> &ps) {
    int on = 0, off = 0;
    for (const FnPart &p : ps) {
        uintptr_t a = im.base + p.off;
        if (!segAt(im, a, p.now.size())) return 3;
        std::vector<uint8_t> cur((uint8_t *)a, (uint8_t *)a + p.now.size());
        if (cur == p.now) on++; else if (cur == p.orig) off++; else return 3;
    }
    return on == (int)ps.size() ? 1 : off == (int)ps.size() ? 0 : 2;
}

static Str fnApply(const Img &im, const std::vector<FnPart> &ps, const Str &nm, bool on, bool keep) {
    if (fnState(im, ps) == 3) return nm + ": байты не совпали (другая версия игры?), не трогаю\n";
    Str o;
    for (const FnPart &p : ps) {
        if (on) o += doPatch(im, p.off, p.now, keep);
        else {
            o += writeMem(im, p.off, p.orig, false);
            g_patches.erase(p.off);
            for (size_t i = 0; i < g_saved.size(); i++) if (g_saved[i].off == p.off) { g_saved.erase(g_saved.begin() + i); break; }
        }
    }
    if (!on) saveFile();
    return (on ? "включено: " : "выключено: ") + nm + "\n" + o;
}

static Str fnRoute(const Img &im, const Str &path, const Params &q) {
    FnSet fs = fnLoad();
    auto stOf = [&](const Str &nm) { for (auto &kv : fs.fns) if (kv.first == nm) return fnState(im, kv.second); return 3; };
    if (path == "fnlist") {
        Str o;
        for (auto &kv : fs.fns) o += kv.first + "\t" + std::to_string(fnState(im, kv.second)) + "\t" + std::to_string(kv.second.size()) + "\n";
        for (auto &pr : fs.profs) {
            int all1 = 1, bad = 0, any1 = 0;
            for (const Str &m : pr.second) { int st = stOf(m); if (st != 1) all1 = 0; if (st == 3) bad = 1; if (st == 1) any1 = 1; }
            o += pr.first + "\tP" + (bad ? "3" : all1 ? "1" : any1 ? "2" : "0") + "\t" + std::to_string(pr.second.size()) + "\n";
        }
        return o.empty() ? "пусто\n" : o;
    }
    if (path == "fnsave") {                                        // превратить патчи этой сессии в функцию
        Str nm = P(q, "n");
        if (nm.empty()) return "нужно имя n\n";
        if (nm.find('|') != Str::npos) return "в имени нельзя символ |\n";
        if (g_patches.empty()) return "патчей в этой сессии нет\n";
        FILE *f = fopen(fnFile().c_str(), "a");
        if (!f) return "не могу писать файл функций\n";
        for (auto &kv : g_patches) {
            uintptr_t a = im.base + kv.first;
            std::vector<uint8_t> now((uint8_t *)a, (uint8_t *)a + kv.second.size());
            fprintf(f, "%s|%lX|%s|%s\n", nm.c_str(), (unsigned long)kv.first, hexs(kv.second).c_str(), hexs(now).c_str());
        }
        fclose(f);
        return "функция «" + nm + "» сохранена (" + std::to_string(g_patches.size()) + " патч.)\n";
    }
    if (path == "fnprof") {
        Str nm = P(q, "n"), l = P(q, "l");
        if (nm.empty() || l.empty() || nm.find('|') != Str::npos) return "нужны название n и список функций l\n";
        FILE *f = fopen(fnFile().c_str(), "a");
        if (!f) return "не могу писать файл функций\n";
        fprintf(f, "@%s|%s\n", nm.c_str(), l.c_str());
        fclose(f);
        return "профиль «" + nm + "» создан\n";
    }
    const Str nm = P(q, "n"); bool on = path == "fnon", keep = P(q, "k") == "1";
    if (path != "fnon" && path != "fnoff") return "неизвестный маршрут\n";
    for (auto &kv : fs.fns) if (kv.first == nm) return fnApply(im, kv.second, nm, on, keep);
    for (auto &pr : fs.profs) if (pr.first == nm) {
        Str o;
        for (const Str &m : pr.second) { bool f = false; for (auto &kv : fs.fns) if (kv.first == m) { o += fnApply(im, kv.second, m, on, keep); f = true; } if (!f) o += m + ": функция не найдена\n"; }
        return o;
    }
    return "функция не найдена\n";
}

// ---------------------------------------------------------------- поиск констант в коде, статус/откат, поиск options.txt
static Str constFind(const Img &im, uint32_t v, bool has2, uint32_t v2, uintptr_t win, size_t maxr) {
    auto collect = [&](uint32_t val, std::vector<uintptr_t> &hits) {
        for (const Seg &g : im.segs) {
            if (!g.r || !g.x) continue;
            for (uintptr_t a = g.s; a + 4 <= g.e && hits.size() < 40000; a += 2) {
                uint16_t h1 = rd16(a);
                if (val <= 255 && ((h1 & 0xF800) == 0x2000 || (h1 & 0xF800) == 0x2800) && (h1 & 0xFF) == val) { hits.push_back(a - im.base); continue; }
                if ((h1 & 0xF800) != 0xF000 && (h1 & 0xF800) != 0xF800 && (h1 & 0xF800) != 0xE800) continue;
                uint16_t h2 = rd16(a + 2);
                if ((h1 & 0xFBF0) == 0xF240 && (h2 & 0x8000) == 0) {                           // movw
                    uint32_t imm = ((h1 & 0xF) << 12) | (((h1 >> 10) & 1) << 11) | (((h2 >> 12) & 7) << 8) | (h2 & 0xFF);
                    if (imm == val) hits.push_back(a - im.base);
                } else if (((h1 & 0xFBF0) == 0xF1B0 && (h2 & 0x8F00) == 0x0F00) || ((h1 & 0xFBEF) == 0xF04F && (h2 & 0x8000) == 0)) {   // cmp.w / mov.w imm
                    uint32_t i12 = (((h1 >> 10) & 1) << 11) | (((h2 >> 12) & 7) << 8) | (h2 & 0xFF);
                    if (thumbExpand(i12) == val) hits.push_back(a - im.base);
                }
            }
        }
    };
    std::vector<uintptr_t> h1v, h2v; collect(v, h1v);
    Str o = "вхождений " + dn(v) + ": " + std::to_string(h1v.size()) + "\n";
    if (!has2) {
        size_t n = 0;
        for (uintptr_t a : h1v) { uintptr_t f = fnStart(im, im.base + a); o += hx(a) + "  функция ~" + (f ? hx(f - im.base) : Str("?")) + "\n"; if (++n >= maxr) { o += "...лимит\n"; break; } }
        return o;
    }
    collect(v2, h2v);
    o += "вхождений " + dn(v2) + ": " + std::to_string(h2v.size()) + "\n";
    size_t n = 0; uintptr_t lastF = 1;
    for (uintptr_t a : h1v) for (uintptr_t b : h2v) {
        uintptr_t d = a > b ? a - b : b - a;
        if (d > win) continue;
        uintptr_t f = fnStart(im, im.base + (a < b ? a : b));
        uintptr_t fo = f ? f - im.base : 0;
        if (fo == lastF) continue;
        lastF = fo;
        o += hx(a) + " & " + hx(b) + "  функция ~" + (f ? hx(fo) : Str("?")) + "\n";
        if (++n >= maxr) return o + "...лимит\n";
    }
    return n ? o : o + "рядом не найдено (увеличь окно w)\n";
}

static void findFile(const Str &dir, const Str &name, int depth, Str &out, size_t &n) {
    if (depth < 0 || n > 20) return;
    DIR *d = opendir(dir.c_str());
    if (!d) return;
    while (dirent *e = readdir(d)) {
        Str nm = e->d_name;
        if (nm == "." || nm == "..") continue;
        Str full = dir + "/" + nm;
        if (nm == name) { out += full + "\n"; n++; }
        if (e->d_type == DT_DIR) findFile(full, name, depth - 1, out, n);
    }
    closedir(d);
}

static Str miscRoute(const Str &path, const Params &q) {
    Str lock = dataDir() + "/mgg_apply.lock", dis = patchFile() + ".disabled";
    if (path == "findopt") {
        Str o; size_t n = 0;
        for (const Str &r : fileRoots()) findFile(r, "options.txt", 7, o, n);
        return o.empty() ? "options.txt не найден в доступных папках\n" : o;
    }
    if (path == "status") {
        size_t fz; { std::lock_guard<std::mutex> lk(g_fm); fz = g_frz.size(); }
        return "патчей в сессии: " + std::to_string(g_patches.size()) + "\nсохранённых: " + std::to_string(g_saved.size()) +
               "\nзаморозок: " + std::to_string(fz) + "\nблокировка краша: " + (access(lock.c_str(), F_OK) == 0 ? "есть" : "нет") +
               "\nотключённые патчи (.disabled): " + (access(dis.c_str(), F_OK) == 0 ? "есть" : "нет") + "\nпапка данных: " + dataDir() + "\n";
    }
    if (path == "unlock") { remove(lock.c_str()); return "блокировка снята\n"; }
    if (path == "reenable") {
        if (access(dis.c_str(), F_OK) != 0) return "отключённых патчей нет\n";
        rename(dis.c_str(), patchFile().c_str()); loadFile();
        return "патчи возвращены, применятся при следующем запуске игры\n";
    }
    if (path == "rollall") {
        Img im; Str o;
        if (loadImg(im)) for (auto &kv : g_patches) writeMem(im, kv.first, kv.second, false);
        size_t n = g_patches.size(); g_patches.clear(); g_saved.clear();
        remove(patchFile().c_str()); remove(lock.c_str());
        size_t fz; { std::lock_guard<std::mutex> lk(g_fm); fz = g_frz.size(); g_frz.clear(); }
        { std::lock_guard<std::mutex> lk(g_wm); g_w.run = false; }
        (void)q;
        return "откатано патчей: " + std::to_string(n) + ", снято заморозок: " + std::to_string(fz) + ", сохранённые очищены\n";
    }
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- маршруты
static const char *kPage = R"MGG(<!doctype html><html><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1,maximum-scale=1"><title>MGG</title>
<style>
:root{--bg:#12141c;--card:#1a1d29;--card2:#232736;--line:#2b3043;--tx:#e9eaf0;--dim:#8d92a6;--ac:#85775a;--acTx:#fff;--hl:#f0b429;--ok:#4cc38a;--r:10px}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
body{font:13px/1.35 system-ui,sans-serif;background:var(--bg);color:var(--tx);margin:0;padding:0 0 10px 64px}
.ic{width:15px;height:15px;stroke:currentColor;fill:none;stroke-width:1.7;stroke-linecap:round;stroke-linejoin:round;vertical-align:-3px;flex:none}
.ic.fi{fill:currentColor;stroke:none}
aside{position:fixed;left:0;top:0;bottom:0;width:64px;background:var(--card);border-right:1px solid var(--line);display:flex;flex-direction:column;padding:8px 0;z-index:9;overflow-y:auto}
aside .lg{font-weight:700;text-align:center;font-size:12px;padding:2px 0 10px;border-bottom:1px solid var(--line);margin:0 8px 8px;letter-spacing:.5px}
aside .lg span{display:block;font-weight:400;color:var(--dim);font-size:9px;letter-spacing:.3px}
.nav{background:none;border:0;margin:2px 6px;padding:6px 0 5px;color:var(--dim);font-size:9px;display:flex;flex-direction:column;align-items:center;gap:4px;width:auto;border-radius:12px}
.nav .bx{width:30px;height:30px;border-radius:9px;background:rgba(255,255,255,.05);display:flex;align-items:center;justify-content:center;color:var(--dim)}
.nav .bx .ic{width:17px;height:17px}
.nav.on{background:rgba(255,255,255,.03)}
.nav.on .bx{background:var(--ac);color:var(--acTx)}
.nav.on{color:var(--tx)}
#top{background:var(--bg);padding:8px 8px 4px}
#out{white-space:pre-wrap;word-break:break-all;background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:8px 10px;margin:0;max-height:24vh;min-height:42px;overflow:auto;font:11px/1.35 ui-monospace,monospace;color:var(--tx)}
#out.big{max-height:60vh}
.row{display:flex;gap:5px;margin-top:5px}.row>*{flex:1}
.pg{padding:0 8px}
.card{background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:9px;margin:7px 0}
.card h3{margin:0 0 6px;font-size:11px;color:var(--dim);font-weight:600;letter-spacing:.4px;text-transform:uppercase;display:flex;align-items:center;gap:6px}
details.card{padding:0}details.card>summary{padding:9px;font-weight:600;list-style:none;cursor:pointer;display:flex;align-items:center;gap:7px}
details.card>summary .ic{margin-left:auto;transition:transform .15s}
details[open].card>summary .ic{transform:rotate(45deg)}
details.card>div{padding:0 9px 9px}
input,select{width:100%;background:var(--card2);border:1px solid var(--line);color:var(--tx);border-radius:8px;padding:8px 9px;margin:3px 0;font:inherit;outline:none}
input:focus,select:focus{border-color:var(--ac)}
input[type=color]{padding:2px;height:34px}input[type=range]{padding:0;accent-color:var(--ac)}
button{font:inherit;color:var(--acTx);border:0;border-radius:var(--r);padding:8px 9px;margin:3px 0;background:var(--ac);width:100%;display:flex;align-items:center;justify-content:center;gap:7px}
button:active{filter:brightness(1.25)}button.s{background:var(--card2);border:1px solid var(--line);color:var(--tx)}
button.d{background:#8a3a40}button.g{background:#3f7a63}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:5px}.grid3{display:grid;grid-template-columns:1fr 1fr 1fr;gap:5px}
.grid2 button,.grid3 button{margin:0}
.fn{display:flex;align-items:center;gap:8px;background:var(--ac);color:var(--acTx);border-radius:var(--r);padding:9px 10px;margin:5px 0}
.fn .nm{flex:1;font-weight:600}.fn .sub{opacity:.7;font-size:10px;font-weight:400}
.sw{width:38px;height:21px;border-radius:999px;background:rgba(0,0,0,.35);flex:none;position:relative}
.sw::after{content:"";position:absolute;top:2px;left:2px;width:17px;height:17px;border-radius:50%;background:#fff;transition:transform .15s}
.sw.on{background:var(--hl)}.sw.on::after{transform:translateX(17px);background:#22240f}
.sw.bad{background:#8a3a40}.sw.bad::after{background:#ffd9db}
.sw.mid{background:#6b6450}.sw.mid::after{background:#fff3cf}
.tag{font-size:9px;background:rgba(0,0,0,.3);border-radius:5px;padding:1px 5px;margin-left:6px}
small{color:var(--dim);display:block;margin-top:4px}
.pre{display:flex;gap:5px;flex-wrap:wrap}.pre button{width:auto;flex:1;min-width:70px}
</style></head><body>
<svg style="position:absolute;width:0;height:0" aria-hidden="true"><defs>
<symbol id="i-bolt" viewBox="0 0 24 24"><path class=fi d="M13 2 4 14h6l-1 8 9-12h-6l1-8z"/></symbol>
<symbol id="i-mem" viewBox="0 0 24 24"><circle cx=10 cy=10 r=6/><path d="M14.5 14.5 20 20M10 7v6M7 10h6"/></symbol>
<symbol id="i-lib" viewBox="0 0 24 24"><rect x=6 y=6 width=12 height=12 rx=2/><path d="M9 2v4M15 2v4M9 18v4M15 18v4M2 9h4M2 15h4M18 9h4M18 15h4"/></symbol>
<symbol id="i-file" viewBox="0 0 24 24"><path d="M3 6a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V6z"/></symbol>
<symbol id="i-safe" viewBox="0 0 24 24"><path d="M12 2 4 5v6c0 5 3.5 8.5 8 11 4.5-2.5 8-6 8-11V5l-8-3z"/></symbol>
<symbol id="i-palette" viewBox="0 0 24 24"><path d="M12 3a9 8 0 1 0 0 16c1.5 0 2-1 2-2s-.5-1.5-.5-2.5S14 13 15 13h2a4 4 0 0 0 4-4c0-3.5-4-6-9-6z"/><circle class=fi cx=8 cy=12 r=1.3/><circle class=fi cx=9.5 cy=8 r=1.3/><circle class=fi cx=14.5 cy=8 r=1.3/></symbol>
<symbol id="i-copy" viewBox="0 0 24 24"><rect x=8 y=8 width=12 height=12 rx=2/><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"/></symbol>
<symbol id="i-expand" viewBox="0 0 24 24"><path d="M9 3H3v6M15 21h6v-6M21 3h-6v6M3 21h6v-6"/></symbol>
<symbol id="i-search" viewBox="0 0 24 24"><circle cx=11 cy=11 r=7/><path d="M21 21l-4.3-4.3"/></symbol>
<symbol id="i-up" viewBox="0 0 24 24"><path d="M12 19V5M5 12l7-7 7 7"/></symbol>
<symbol id="i-down" viewBox="0 0 24 24"><path d="M12 5v14M5 12l7 7 7-7"/></symbol>
<symbol id="i-eq" viewBox="0 0 24 24"><path d="M5 9h14M5 15h14"/></symbol>
<symbol id="i-list" viewBox="0 0 24 24"><path d="M8 6h13M8 12h13M8 18h13M3 6h.01M3 12h.01M3 18h.01"/></symbol>
<symbol id="i-reset" viewBox="0 0 24 24"><path d="M3 12a9 9 0 1 0 3-6.7"/><path d="M3 3v5h5"/></symbol>
<symbol id="i-save" viewBox="0 0 24 24"><path d="M5 4h11l3 3v13H5z"/><path d="M8 4v6h8V4M8 14h8v6H8z"/></symbol>
<symbol id="i-snow" viewBox="0 0 24 24"><path d="M12 2v20M4.5 6.5l15 11M19.5 6.5l-15 11"/></symbol>
<symbol id="i-stop" viewBox="0 0 24 24"><rect x=6 y=6 width=12 height=12 rx=1.5/></symbol>
<symbol id="i-link" viewBox="0 0 24 24"><path d="M10 14a4 4 0 0 0 6 0l3-3a4 4 0 0 0-6-6l-1.5 1.5"/><path d="M14 10a4 4 0 0 0-6 0l-3 3a4 4 0 0 0 6 6l1.5-1.5"/></symbol>
<symbol id="i-start" viewBox="0 0 24 24"><path d="M8 5l12 7-12 7z"/></symbol>
<symbol id="i-hex" viewBox="0 0 24 24"><path d="M9 3 3 7v10l6 4 6-4V7zM15 3l6 4v10l-6 4"/></symbol>
<symbol id="i-code" viewBox="0 0 24 24"><path d="M9 6 3 12l6 6M15 6l6 6-6 6"/></symbol>
<symbol id="i-undo" viewBox="0 0 24 24"><path d="M3 10h9a6 6 0 0 1 0 12h-3"/><path d="M8 5 3 10l5 5"/></symbol>
<symbol id="i-trash" viewBox="0 0 24 24"><path d="M4 7h16M9 7V5a2 2 0 0 1 2-2h2a2 2 0 0 1 2 2v2M6 7l1 13a2 2 0 0 0 2 2h6a2 2 0 0 0 2-2l1-13"/></symbol>
<symbol id="i-plug" viewBox="0 0 24 24"><path d="M9 2v6M15 2v6M6 8h12l-1 5a5 5 0 0 1-10 0z"/><path d="M12 17v5"/></symbol>
<symbol id="i-unlock" viewBox="0 0 24 24"><rect x=5 y=11 width=14 height=9 rx=2/><path d="M8 11V7a4 4 0 0 1 7-2.6"/></symbol>
<symbol id="i-info" viewBox="0 0 24 24"><circle cx=12 cy=12 r=9/><path d="M12 11v5M12 8h.01"/></symbol>
<symbol id="i-plus" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></symbol>
<symbol id="i-flag" viewBox="0 0 24 24"><path d="M5 3v18M5 4h11l-2 4 2 4H5"/></symbol>
<symbol id="i-sun" viewBox="0 0 24 24"><path d="M12 5v2M12 17v2M5 12H3M21 12h-2M6.3 6.3l1.4 1.4M16.3 16.3l1.4 1.4M6.3 17.7l1.4-1.4M16.3 7.7l1.4-1.4"/><circle cx=12 cy=12 r=4/></symbol>
<symbol id="i-eye" viewBox="0 0 24 24"><path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7-10-7-10-7z"/><circle cx=12 cy=12 r=3/></symbol>
</defs></svg>
<div id=top><pre id=out>MGG готов. Открой вкладку «Функции».</pre>
<div class=row><button class=s onclick="cp()"><svg class=ic><use href="#i-copy"/></svg>Копировать</button><button class=s onclick="document.getElementById('out').classList.toggle('big')"><svg class=ic><use href="#i-expand"/></svg>Размер</button></div></div>

<div class=pg id=pn>
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Готовые функции</h3><div id=fl>…</div>
<select id=fk2><option value=0>только сейчас</option><option value=1>запоминать (автоприменение при запуске)</option></select>
<button class=s onclick="fnl()"><svg class=ic><use href="#i-reset"/></svg>Обновить список</button></div>
<details class=card><summary><svg class=ic><use href="#i-plus"/></svg>Создать функцию из патчей сессии<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=fnn placeholder="название (например Disable render limit)">
<button onclick="call('fnsave',{n:v('fnn')}).then(fnl)"><svg class=ic><use href="#i-save"/></svg>Сохранить патчи сессии</button>
<input id=fpn placeholder="профиль: название"><input id=fpl placeholder="функции через запятую">
<button onclick="call('fnprof',{n:v('fpn'),l:v('fpl')}).then(fnl)"><svg class=ic><use href="#i-flag"/></svg>Создать профиль (набор функций)</button>
<small>Ручная правка: вкладка File → mgg_functions.txt. Формат: Название|смещение|оригинал|новое. Профиль: @Название|функция1,функция2</small></div></details>
</div>

<div class=pg id=pm style="display:none">
<div class=card><h3><svg class=ic><use href="#i-search"/></svg>Поиск значения</h3>
<input id=mv placeholder="значение (например 13)" inputmode=decimal>
<div class=grid2><select id=mt><option value=4>int 4 байта</option><option value=f>float</option><option value=2>2 байта</option><option value=1>1 байт</option></select>
<select id=mall><option value=0>куча (безопасно)</option><option value=1>вся rw-память</option></select></div>
<button onclick="call('mscan',{v:v('mv'),...ty(),all:v('mall')})"><svg class=ic><use href="#i-search"/></svg>Первый поиск</button>
<div class=grid3 style="margin-top:6px"><button class=s onclick="call('mnext',{m:'eq',v:v('mv')})"><svg class=ic><use href="#i-eq"/></svg>= значение</button><button class=s onclick="call('mnext',{m:'inc'})"><svg class=ic><use href="#i-up"/></svg>выросло</button><button class=s onclick="call('mnext',{m:'dec'})"><svg class=ic><use href="#i-down"/></svg>уменьшилось</button>
<button class=s onclick="call('mnext',{m:'same'})"><svg class=ic><use href="#i-eq"/></svg>не менялось</button><button class=s onclick="call('mnext',{m:'chg'})"><svg class=ic><use href="#i-reset"/></svg>менялось</button><button class=s onclick="call('mreset',{})"><svg class=ic><use href="#i-trash"/></svg>сброс</button></div>
<button class=s style="margin-top:6px" onclick="call('mlist',{n:60})"><svg class=ic><use href="#i-list"/></svg>Список найденных</button></div>
<div class=card><h3><svg class=ic><use href="#i-snow"/></svg>Запись и заморозка</h3>
<input id=ma placeholder="адрес (hex)"><input id=mw placeholder="новое значение">
<div class=grid2><button onclick="call('mset',{a:v('ma'),v:v('mw'),...ty()})"><svg class=ic><use href="#i-save"/></svg>Записать</button><button onclick="call('mset',{all:1,v:v('mw')})"><svg class=ic><use href="#i-save"/></svg>Во все найденные</button>
<button class=g onclick="call('mfreeze',{a:v('ma'),v:v('mw'),...ty()})"><svg class=ic><use href="#i-snow"/></svg>Заморозить</button><button class=g onclick="call('mfreeze',{all:1,v:v('mw')})"><svg class=ic><use href="#i-snow"/></svg>Все найденные</button>
<button class=s onclick="call('mfrlist',{})"><svg class=ic><use href="#i-list"/></svg>Список заморозок</button><button class=d onclick="call('munfreeze',{all:1})"><svg class=ic><use href="#i-sun"/></svg>Разморозить всё</button></div></div>
<div class=card><h3><svg class=ic><use href="#i-eye"/></svg>Монитор адреса</h3>
<div class=grid3><button onclick="call('mwatch',{a:v('ma'),...ty()})"><svg class=ic><use href="#i-start"/></svg>Старт</button><button class=s onclick="call('mwlog',{})"><svg class=ic><use href="#i-list"/></svg>Журнал</button><button class=d onclick="call('mwstop',{})"><svg class=ic><use href="#i-stop"/></svg>Стоп</button></div>
<small>Показывает, когда и как меняется значение по адресу из поля выше.</small>
<div class=row><input id=mn placeholder="байт (128)"><button class=s onclick="call('mdump',{a:v('ma'),n:v('mn')||128})"><svg class=ic><use href="#i-hex"/></svg>Hex</button></div></div>
</div>

<div class=pg id=pl style="display:none">
<details class=card open><summary><svg class=ic><use href="#i-hex"/></svg>Константы в коде<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=cv placeholder="число (например 13 или 0xD)"><input id=cv2 placeholder="второе число рядом (необязательно)">
<input id=cw placeholder="окно, байт (по умолч. 768)">
<button onclick="call('constfind',{v:v('cv'),v2:v('cv2'),w:v('cw')||768,max:60})"><svg class=ic><use href="#i-search"/></svg>Найти в коде</button>
<small>Ищет movs/cmp/movw с этим числом. Со вторым числом — только места, где оба рядом (одна функция).</small></div></details>
<details class=card><summary><svg class=ic><use href="#i-info"/></svg>Инфо / строки / сигнатуры<svg class=ic><use href="#i-plus"/></svg></summary><div>
<button class=s onclick="call('info',{})"><svg class=ic><use href="#i-info"/></svg>База и сегменты</button>
<input id=ss placeholder="строка (viewdistance)"><select id=si><option value=1>без учёта регистра</option><option value=0>с учётом</option></select>
<button onclick="call('str',{s:v('ss'),i:v('si'),max:60})"><svg class=ic><use href="#i-search"/></svg>Искать строку</button>
<input id=sp placeholder="F0 B5 03 AF ?? ??"><select id=sa><option value=0>только код</option><option value=1>вся библиотека</option></select>
<button onclick="call('sig',{p:v('sp'),all:v('sa'),max:50})"><svg class=ic><use href="#i-search"/></svg>Искать сигнатуру</button></div></details>
<details class=card><summary><svg class=ic><use href="#i-link"/></svg>Ссылки и функции<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=xa placeholder="смещение строки, hex"><input id=xn placeholder="длина диапазона (1)">
<button onclick="call('xref',{a:v('xa'),n:v('xn'),max:40})"><svg class=ic><use href="#i-link"/></svg>Кто использует (xref)</button>
<input id=fa placeholder="смещение внутри функции, hex"><button class=s onclick="call('fn',{a:v('fa')})"><svg class=ic><use href="#i-start"/></svg>Начало функции</button>
<input id=ca placeholder="начало функции, hex"><button class=s onclick="call('callers',{a:v('ca'),max:60})"><svg class=ic><use href="#i-link"/></svg>Кто вызывает</button></div></details>
<details class=card><summary><svg class=ic><use href="#i-code"/></svg>Hex / дизассемблер<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=ha placeholder="смещение, hex"><input id=hn placeholder="байт (128)"><button class=s onclick="call('hex',{a:v('ha'),n:v('hn')||128})"><svg class=ic><use href="#i-hex"/></svg>Hex</button>
<input id=da placeholder="смещение, hex"><input id=dn placeholder="команд (24)"><button class=s onclick="call('dis',{a:v('da'),n:v('dn')||24})"><svg class=ic><use href="#i-code"/></svg>Дизассемблер Thumb</button></div></details>
<details class=card><summary><svg class=ic><use href="#i-save"/></svg>Патчи<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=pa placeholder="смещение, hex"><input id=pb placeholder="байты: 00 20 70 47">
<select id=pk><option value=0>только сейчас</option><option value=1>сохранять на запуски</option></select>
<button onclick="call('patch',{a:v('pa'),b:v('pb'),k:v('pk')})"><svg class=ic><use href="#i-save"/></svg>Записать</button>
<div class=grid2><button class=s onclick="call('undo',{a:v('pa')})"><svg class=ic><use href="#i-undo"/></svg>Откатить</button><button class=s onclick="call('patches',{})"><svg class=ic><use href="#i-list"/></svg>Список (сессия)</button><button class=s onclick="call('saved',{})"><svg class=ic><use href="#i-list"/></svg>Сохранённые</button><button class=d onclick="call('clearsaved',{})"><svg class=ic><use href="#i-trash"/></svg>Удалить сохранённые</button></div>
<input id=qa placeholder="начало функции, hex"><input id=qv placeholder="число для ret, hex (0-FF)"><input id=qn placeholder="сколько NOP (1)">
<div class=grid2><button onclick="call('quick',{a:v('qa'),m:'ret',v:v('qv')||'0',k:v('pk')})"><svg class=ic><use href="#i-save"/></svg>Функция → число</button><button onclick="call('quick',{a:v('qa'),m:'nop',n:v('qn')||1,k:v('pk')})"><svg class=ic><use href="#i-stop"/></svg>Забить NOP</button></div></div></details>
<details class=card><summary><svg class=ic><use href="#i-plug"/></svg>Хуки (нужен Dobby)<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=ka placeholder="смещение функции, hex"><select id=km><option value=log>лог вызовов</option><option value=ret>вернуть значение</option><option value=set>подменить результат</option></select>
<input id=kv placeholder="значение, hex"><button onclick="call('hook',{a:v('ka'),m:v('km'),v:v('kv')})"><svg class=ic><use href="#i-plug"/></svg>Поставить</button>
<input id=ki placeholder="номер хука"><div class=grid3><button class=s onclick="call('hookset',{id:v('ki'),m:v('km'),v:v('kv')})"><svg class=ic><use href="#i-reset"/></svg>Режим</button><button class=s onclick="call('unhook',{id:v('ki')})"><svg class=ic><use href="#i-stop"/></svg>Снять</button><button class=s onclick="call('hooks',{})"><svg class=ic><use href="#i-list"/></svg>Список</button></div></div></details>
</div>

<div class=pg id=pf style="display:none">
<div class=card><h3><svg class=ic><use href="#i-file"/></svg>Быстрые настройки (options.txt)</h3>
<button class=s onclick="findopt()"><svg class=ic><use href="#i-search"/></svg>Найти options.txt</button>
<input id=op placeholder="путь к options.txt (заполнится сам)">
<div class=grid2><input id=ok1 placeholder="ключ" value="gfx_viewdistance"><input id=ov1 placeholder="значение" value="32"></div>
<button onclick="call('setkey',{p:v('op'),k:v('ok1'),v:v('ov1')})"><svg class=ic><use href="#i-save"/></svg>Задать</button>
<div class=grid3><button class=s onclick="q('gfx_viewdistance',v('ov1'))">дальность</button><button class=s onclick="q('gfx_field_of_view',v('ov1'))">FOV</button><button class=s onclick="q('gfx_gamma',v('ov1'))">яркость</button></div>
<small>Игра может перезаписать файл при выходе и ограничить значение.</small></div>
<div class=card><h3><svg class=ic><use href="#i-file"/></svg>Файлы игры</h3><input id=fp placeholder="путь (пусто = папки игры)">
<div class=grid2><button class=s onclick="call('ls',{p:v('fp')})"><svg class=ic><use href="#i-list"/></svg>Список</button><button class=s onclick="call('cat',{p:v('fp')})"><svg class=ic><use href="#i-eye"/></svg>Показать</button></div>
<input id=gs placeholder="искать текст в файлах"><button class=s onclick="call('grep',{p:v('fp'),s:v('gs'),max:30})"><svg class=ic><use href="#i-search"/></svg>Найти текст</button>
<input id=fk placeholder="ключ"><input id=fv placeholder="значение"><button onclick="call('setkey',{p:v('fp'),k:v('fk'),v:v('fv')})"><svg class=ic><use href="#i-save"/></svg>Задать ключ:значение</button>
<input id=fa2 placeholder="найти текст"><input id=fb placeholder="заменить на"><button onclick="call('freplace',{p:v('fp'),a:v('fa2'),b:v('fb')})"><svg class=ic><use href="#i-reset"/></svg>Заменить текст</button>
<button class=s onclick="call('frestore',{p:v('fp')})"><svg class=ic><use href="#i-undo"/></svg>Вернуть из .mgg.bak</button></div>
</div>

<div class=pg id=ps style="display:none">
<div class=card><h3><svg class=ic><use href="#i-safe"/></svg>Состояние</h3><button class=s onclick="call('status',{})"><svg class=ic><use href="#i-info"/></svg>Показать статус</button></div>
<div class=card><h3><svg class=ic><use href="#i-safe"/></svg>Аварийные кнопки</h3>
<button class=d onclick="call('rollall',{})"><svg class=ic><use href="#i-undo"/></svg>Откатить ВСЁ (патчи, заморозки, сохранённое)</button>
<button class=s onclick="call('unlock',{})"><svg class=ic><use href="#i-unlock"/></svg>Снять блокировку после краша</button>
<button class=s onclick="call('reenable',{})"><svg class=ic><use href="#i-reset"/></svg>Вернуть отключённые патчи (.disabled)</button>
<small>Если игра вылетает при запуске: открой панель сразу после старта и нажми «Откатить всё».</small></div>
</div>

<div class=pg id=pt style="display:none">
<div class=card><h3><svg class=ic><use href="#i-palette"/></svg>Пресеты</h3><div class=pre>
<button onclick="preset('#85775a','#12141c','#1a1d29','#f0b429')">Asteria</button>
<button onclick="preset('#4f6bff','#0b0d12','#151922','#7dd3fc')">Neon</button>
<button onclick="preset('#2f9e6e','#0e1512','#16211c','#b7f7cf')">Green</button>
<button onclick="preset('#b5424d','#150d10','#22151a','#ffb3ba')">Red</button>
<button onclick="preset('#6c5ce7','#101018','#1b1b2b','#d0c8ff')">Violet</button>
<button onclick="preset('#3b82f6','#eef1f6','#ffffff','#1d4ed8')">Light</button></div></div>
<div class=card><h3><svg class=ic><use href="#i-palette"/></svg>Свои цвета</h3>
<div class=grid2><div>Кнопки<input type=color id=c_ac oninput="applyTheme()"></div><div>Галочки<input type=color id=c_hl oninput="applyTheme()"></div>
<div>Фон<input type=color id=c_bg oninput="applyTheme()"></div><div>Карточки<input type=color id=c_card oninput="applyTheme()"></div></div>
Скругление<input type=range id=c_r min=0 max=20 value=10 oninput="applyTheme()">
<button class=s onclick="preset('#85775a','#12141c','#1a1d29','#f0b429')"><svg class=ic><use href="#i-reset"/></svg>Сбросить тему</button></div>
</div>
<aside><div class=lg>MGG<span>panel</span></div>
<button id=bn class="nav on" onclick="tab('n')"><span class=bx><svg class=ic><use href="#i-bolt"/></svg></span>Функции</button>
<button id=bm class=nav onclick="tab('m')"><span class=bx><svg class=ic><use href="#i-mem"/></svg></span>Mem</button>
<button id=bl class=nav onclick="tab('l')"><span class=bx><svg class=ic><use href="#i-lib"/></svg></span>Lib</button>
<button id=bf class=nav onclick="tab('f')"><span class=bx><svg class=ic><use href="#i-file"/></svg></span>File</button>
<button id=bs class=nav onclick="tab('s')"><span class=bx><svg class=ic><use href="#i-safe"/></svg></span>Safe</button>
<button id=bt class=nav onclick="tab('t')"><span class=bx><svg class=ic><use href="#i-palette"/></svg></span>Тема</button></aside>
<script>
const T=new URLSearchParams(location.search).get('t')||'';const out=document.getElementById('out');
function tab(x){for(const k of ['n','m','l','f','s','t']){document.getElementById('p'+k).style.display=x==k?'':'none';document.getElementById('b'+k).className=x==k?'nav on':'nav'}
if(x=='n')fnl();if(x=='f'&&!window.fOnce){window.fOnce=1;findopt()}window.scrollTo(0,0)}
function v(i){return document.getElementById(i).value.trim()}
function ty(){const t=v('mt');return t=='f'?{sz:4,f:1}:{sz:t,f:0}}
async function call(p,o){const q=new URLSearchParams(o);q.set('t',T);out.textContent='…';
try{const r=await fetch('/api/'+p+'?'+q);const t=await r.text();out.textContent=t;return t}catch(e){out.textContent='ошибка: '+e;return ''}}
function cp(){const t=out.textContent;if(window.MGGJ){MGGJ.copy(t)}else if(navigator.clipboard){navigator.clipboard.writeText(t)}}
async function fnl(){const q=new URLSearchParams({t:T});let r='';try{r=await(await fetch('/api/fnlist?'+q)).text()}catch(e){r='ошибка'}
const d=document.getElementById('fl');d.textContent='';
if(r.startsWith('пусто')||r.indexOf('\t')<0){d.textContent=r.startsWith('пусто')?'Функций пока нет. Добавь их через File → mgg_functions.txt или сохрани патчи сессии.':r;return}
for(const ln of r.trim().split('\n')){const [n,st,c]=ln.split('\t');const prof=st[0]=='P';const s=prof?st[1]:st;const on=s=='1';
const row=document.createElement('div');row.className='fn';
const nm=document.createElement('div');nm.className='nm';nm.textContent=n;const sub=document.createElement('div');sub.className='sub';
sub.textContent=(prof?'набор функций: ':'патчей: ')+c+(s=='3'?' · другая версия игры':s=='2'?' · частично':'');nm.appendChild(sub);if(prof){const t=document.createElement('span');t.className='tag';t.textContent='профиль';nm.firstChild.after(t)}
const sw=document.createElement('div');sw.className='sw '+(on?'on':s=='3'?'bad':s=='2'?'mid':'');
row.onclick=async()=>{if(s=='3'){out.textContent='байты не совпали: функция для другой версии игры';return}
await call(on?'fnoff':'fnon',{n:n,k:v('fk2')});fnl()};row.appendChild(nm);row.appendChild(sw);d.appendChild(row)}}
async function findopt(){const t=await call('findopt',{});const m=t.split('\n').find(l=>l.endsWith('options.txt'));if(m)document.getElementById('op').value=m.trim()}
function q(k,val){document.getElementById('ok1').value=k;call('setkey',{p:v('op'),k:k,v:val})}

function mix(h,p){const n=parseInt(h.slice(1),16);let r=n>>16,g=(n>>8)&255,b=n&255;const f=x=>Math.max(0,Math.min(255,Math.round(x+(p>0?(255-x):x)*p)));return '#'+[r,g,b].map(f).map(x=>x.toString(16).padStart(2,'0')).join('')}
function lum(h){const n=parseInt(h.slice(1),16);return (0.299*(n>>16)+0.587*((n>>8)&255)+0.114*(n&255))/255}
function applyTheme(save=true){const ac=v('c_ac'),hl=v('c_hl'),bg=v('c_bg'),cd=v('c_card'),r=v('c_r');const R=document.documentElement.style;
const light=lum(bg)>.6;R.setProperty('--ac',ac);R.setProperty('--hl',hl);R.setProperty('--bg',bg);R.setProperty('--card',cd);R.setProperty('--card2',mix(cd,light?-0.06:0.08));R.setProperty('--line',mix(cd,light?-0.14:0.14));
R.setProperty('--tx',light?'#161a24':'#e9eaf0');R.setProperty('--dim',light?'#5d6578':'#8d92a6');R.setProperty('--acTx',lum(ac)>.65?'#111':'#fff');R.setProperty('--r',r+'px');
if(save)try{localStorage.setItem('mggTheme',JSON.stringify([ac,bg,cd,hl,r]))}catch(e){}}
function preset(ac,bg,cd,hl){document.getElementById('c_ac').value=ac;document.getElementById('c_bg').value=bg;document.getElementById('c_card').value=cd;document.getElementById('c_hl').value=hl;applyTheme()}
(function(){let t=null;try{t=JSON.parse(localStorage.getItem('mggTheme'))}catch(e){}t=t||['#85775a','#12141c','#1a1d29','#f0b429',10];
document.getElementById('c_ac').value=t[0];document.getElementById('c_bg').value=t[1];document.getElementById('c_card').value=t[2];document.getElementById('c_hl').value=t[3];document.getElementById('c_r').value=t[4];applyTheme(false)})();
fnl();
</script></body></html>)MGG";


static Str route(const Str &path, const Params &q) {
    std::lock_guard<std::mutex> lk(g_mu);
    if (path == "ls" || path == "cat" || path == "grep" || path == "setkey" || path == "freplace" || path == "frestore") return fileRoute(path, q);
    if (path == "mscan" || path == "mnext" || path == "mlist" || path == "mreset" || path == "mset" || path == "mdump" || path == "mfreeze" || path == "mfrlist" || path == "munfreeze" || path == "mwatch" || path == "mwlog" || path == "mwstop") return memRoute(path, q);
    if (path == "findopt" || path == "status" || path == "unlock" || path == "reenable" || path == "rollall") return miscRoute(path, q);
    if (path == "mscan" || path == "mnext") {}
    Img im;
    if (!loadImg(im)) return Str("библиотека ") + MGG_TARGET_LIB + " не найдена в /proc/self/maps\n";
    uintptr_t a = 0;

    if (path == "fnlist" || path == "fnon" || path == "fnoff" || path == "fnsave" || path == "fnprof") return fnRoute(im, path, q);
    if (path == "constfind") {
        Str a1 = P(q, "v"), a2 = P(q, "v2");
        if (a1.empty()) return "нужно число v\n";
        auto pn = [](const Str &t) { return (uint32_t)strtoull(t.c_str(), nullptr, 0); };
        return constFind(im, pn(a1), !a2.empty(), a2.empty() ? 0 : pn(a2), (uintptr_t)decNum(q, "w", 768), decNum(q, "max", 60));
    }
    if (path == "info") {
        Str o = "база: " + hx(im.base) + "\nсегменты (смещения):\n";
        for (const Seg &g : im.segs) o += "  " + hx(g.s - im.base) + " - " + hx(g.e - im.base) + "  " + (g.r ? "r" : "-") + (g.w ? "w" : "-") + (g.x ? "x" : "-") + "\n";
        return o;
    }
    if (path == "sig") {
        std::vector<int> pat; Str err;
        if (!parseSig(P(q, "p"), pat, err)) return "ошибка: " + err + "\n";
        return scanSig(im, pat, P(q, "all") == "1", decNum(q, "max", 50));
    }
    if (path == "str") return scanStr(im, P(q, "s"), P(q, "i", "1") != "0", decNum(q, "max", 60));
    if (path == "xref") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        size_t n = decNum(q, "n", 1); if (n == 0) n = 1;
        return findXref(im, im.base + a, im.base + a + n, decNum(q, "max", 40));
    }
    if (path == "fn") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        uintptr_t s = fnStart(im, im.base + a);
        return s ? "начало ~" + hx(s - im.base) + " (Thumb: для хука " + hx(s - im.base + 1) + ")\nэто эвристика: ближайший push {..,lr} назад\n" : "не найдено\n";
    }
    if (path == "hex") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        return hexdump(im, a, decNum(q, "n", 128));
    }
    if (path == "patch") {
        std::vector<uint8_t> b;
        if (!hexNum(q, "a", a) || !parseBytes(P(q, "b"), b)) return "нужны a (hex) и b (байты, без масок)\n";
        return doPatch(im, a, b, P(q, "k") == "1");
    }
    if (path == "quick") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        std::vector<uint8_t> b; Str m = P(q, "m");
        if (m == "ret") {
            uintptr_t v = 0; hexNum(q, "v", v);
            if (v > 255) return "значение больше FF: шаблон не подходит (пришли байты функции)\n";
            b = {(uint8_t)v, 0x20, 0x70, 0x47};                                  // movs r0,#v ; bx lr  (Thumb)
        } else if (m == "nop") {
            size_t n = decNum(q, "n", 1); if (n < 1) n = 1; if (n > 32) n = 32;
            for (size_t i = 0; i < n; i++) { b.push_back(0x00); b.push_back(0xBF); }   // nop (Thumb)
        } else return "неизвестный режим\n";
        return doPatch(im, a, b, P(q, "k") == "1");
    }
    if (path == "undo") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        auto it = g_patches.find(a);
        Str r = "патча по этому смещению нет в этой сессии\n";
        if (it != g_patches.end()) { r = "откат: " + writeMem(im, a, it->second, false); g_patches.erase(it); }
        for (size_t i = 0; i < g_saved.size(); i++) if (g_saved[i].off == a) { g_saved.erase(g_saved.begin() + i); saveFile(); r += "убран из сохранённых\n"; break; }
        return r;
    }
    if (path == "patches") {
        if (g_patches.empty()) return "патчей в этой сессии нет\n";
        Str o;
        for (auto &kv : g_patches) {
            o += hx(kv.first) + "  оригинал:";
            char b[8];
            for (uint8_t x : kv.second) { snprintf(b, sizeof b, " %02X", x); o += b; }
            o += "\n";
        }
        return o;
    }
    if (path == "saved") {
        if (g_saved.empty()) loadFile();
        if (g_saved.empty()) return "сохранённых патчей нет\n";
        Str o = "файл: " + patchFile() + "\n";
        for (const Saved &s : g_saved) o += hx(s.off) + "  " + hexs(s.orig) + " -> " + hexs(s.now) + "\n";
        return o;
    }
    if (path == "clearsaved") {
        g_saved.clear();
        remove(patchFile().c_str());
        return "сохранённые патчи удалены (уже применённые в памяти остаются до перезапуска игры)\n";
    }
    if (path == "dis") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        size_t n = decNum(q, "n", 24); if (n > 200) n = 200;
        return disasm(im, a, n);
    }
    if (path == "callers") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex, начало функции)\n";
        return findCallers(im, (uint32_t)a, decNum(q, "max", 60));
    }
#ifdef MGG_HAS_DOBBY
    if (path == "hooks") return hooksList();
    if (path == "hook") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        int id = -1;
        for (int i = 0; i < 16; i++) if (!g_slots[i].used) { id = i; break; }
        if (id < 0) return "все 16 слотов заняты\n";
        Slot &s = g_slots[id];
        Str m = P(q, "m", "log");
        s.mode = m == "ret" ? 1 : m == "set" ? 2 : 0;
        uintptr_t v = 0; hexNum(q, "v", v); s.val = v;
        s.off = a; s.calls = 0; s.target = (void *)(im.base + a + 1);          // +1: Thumb
        int rc = MGG_HOOK(s.target, g_hk[id], &s.orig);
        if (rc != 0) return "Dobby вернул ошибку " + std::to_string(rc) + "\n";
        s.used = true;
        return "хук #" + std::to_string(id) + " на " + hx(a) + " (Thumb)\n";
    }
    if (path == "hookset" || path == "unhook") {
        size_t id = decNum(q, "id", 99);
        if (id >= 16 || !g_slots[id].used) return "нет такого хука\n";
        Slot &s = g_slots[id];
        if (path == "unhook") { MGG_UNHOOK(s.target); s.used = false; return "снят\n"; }
        Str m = P(q, "m", "log");
        uintptr_t v = 0; hexNum(q, "v", v);
        s.val = v; s.mode = m == "ret" ? 1 : m == "set" ? 2 : 0;
        return "режим обновлён\n";
    }
#else
    if (path == "hooks" || path == "hook" || path == "hookset" || path == "unhook")
        return "эта сборка без Dobby: хуки недоступны (поиск, xref, hex и патчи работают)\n";
#endif
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- HTTP (только 127.0.0.1)
static void sendAll(int c, const Str &s) {
    size_t o = 0;
    while (o < s.size()) {
        ssize_t n = send(c, s.data() + o, s.size() - o, MSG_NOSIGNAL);
        if (n <= 0) break;
        o += (size_t)n;
    }
}

static void reply(int c, int code, const char *ctype, const Str &body) {
    Str h = "HTTP/1.1 " + std::to_string(code) + (code == 200 ? " OK" : " ERR") + "\r\nContent-Type: " + ctype +
            "; charset=utf-8\r\nContent-Length: " + std::to_string(body.size()) + "\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n";
    sendAll(c, h + body);
}

static void handle(int c) {
    char buf[8192];
    ssize_t n = recv(c, buf, sizeof buf - 1, 0);
    if (n <= 0) return;
    buf[n] = 0;
    Str req(buf);
    if (req.compare(0, 4, "GET ") != 0) { reply(c, 405, "text/plain", "только GET\n"); return; }
    size_t e = req.find(' ', 4);
    if (e == Str::npos) { reply(c, 400, "text/plain", "bad request\n"); return; }
    Str target = req.substr(4, e - 4), path = target, qs;
    size_t qm = target.find('?');
    if (qm != Str::npos) { path = target.substr(0, qm); qs = target.substr(qm + 1); }
    if (path == "/") { reply(c, 200, "text/html", kPage); return; }
    if (path.compare(0, 5, "/api/") != 0) { reply(c, 404, "text/plain", "нет такой страницы\n"); return; }
    Params q = parseQuery(qs);
    if (P(q, "t") != MGG_TOKEN) { reply(c, 403, "text/plain", "неверный токен: открой /?t=<токен>\n"); return; }
    reply(c, 200, "text/plain", route(path.substr(5), q));
}

static void serve() {
    int s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0) { LOGI("socket() не удался"); return; }
    int one = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_port = htons(MGG_PORT); sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(s, (sockaddr *)&sa, sizeof sa) != 0 || listen(s, 4) != 0) { LOGI("bind/listen не удался (порт %d занят?)", MGG_PORT); close(s); return; }
    LOGI("панель: http://127.0.0.1:%d/?t=%s", MGG_PORT, MGG_TOKEN);
    for (;;) {
        int c = accept(s, nullptr, nullptr);
        if (c < 0) continue;
        timeval tv{2, 0};
        setsockopt(c, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        handle(c);
        close(c);
    }
}

#ifndef MGG_NO_AUTOSTART
__attribute__((constructor)) static void mggInit() {
    std::thread(serve).detach();
    std::thread(autoApply).detach();
}
#endif
