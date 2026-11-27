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
// Свои объявления вместо dobby.h: у разных версий Dobby типы параметров разные, а символ в библиотеке один и тот же.
extern "C" int DobbyHook(void *address, void *replace_func, void **origin_func);
extern "C" int DobbyDestroy(void *address);
#define MGG_HOOK(addr, rep, orig) DobbyHook((void *)(addr), (void *)(rep), (void **)(orig))
#define MGG_UNHOOK(addr) DobbyDestroy((void *)(addr))
#endif

typedef std::string Str;
typedef std::map<Str, Str> Params;

// ---------------------------------------------------------------- образ библиотеки
struct Seg { uintptr_t s, e; bool r, w, x; };
struct Img { uintptr_t base = 0; std::vector<Seg> segs; };

static Str g_lib = MGG_TARGET_LIB;     // выбранная для патчинга библиотека (вкладка Lib)

// строка /proc/self/maps -> диапазон, права, путь
static bool mapLine(const char *line, unsigned long &s, unsigned long &e, char *perms, Str &path) {
    int n = 0;
    if (sscanf(line, "%lx-%lx %7s %*s %*s %*s %n", &s, &e, perms, &n) < 3 || n <= 0) {
        if (sscanf(line, "%lx-%lx %7s", &s, &e, perms) != 3) return false;
        path.clear(); return true;
    }
    path = line + n;
    while (!path.empty() && (path.back() == '\n' || path.back() == '\r' || path.back() == ' ')) path.pop_back();
    return true;
}
static Str mapBase(const Str &p) { size_t k = p.rfind('/'); return k == Str::npos ? p : p.substr(k + 1); }

static bool loadImg(Img &im, const char *lib = nullptr) {
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f) return false;
    char line[1024];
    uintptr_t lo = ~(uintptr_t)0;
    Str want = lib ? Str(lib) : g_lib;
    while (fgets(line, sizeof line, f)) {
        unsigned long s, e; char perms[8] = {0}; Str path;
        if (!mapLine(line, s, e, perms, path)) continue;
        if (mapBase(path) != want) continue;
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

// число из панели -> 32-битное слово (float: биты IEEE, int: как есть)
static bool numWord(const Str &s, bool isf, uint32_t &w) {
    if (s.empty()) return false;
    char *e = nullptr;
    if (isf) { float f = strtof(s.c_str(), &e); memcpy(&w, &f, 4); }
    else w = (uint32_t)strtol(s.c_str(), &e, 10);
    return e && *e == 0;
}
static Str wordStr(uint32_t w, bool isf) {
    char b[48];
    if (isf) { float f; memcpy(&f, &w, 4); snprintf(b, sizeof b, "%g", (double)f); }
    else snprintf(b, sizeof b, "%d", (int)w);
    return b;
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

// поиск констант-лимитов: слова f1 (и f2 рядом, в пределах win байт) в неписываемых сегментах (код с литерал-пулами и rodata)
static Str fPair(const Img &im, const Params &q) {
    bool isf = P(q, "t", "f") != "i";
    uint32_t w1 = 0, w2 = 0; Str s1 = P(q, "f1"), s2 = P(q, "f2");
    if (!numWord(s1, isf, w1)) return "нужен f1 (число)\n";
    bool two = !s2.empty();
    if (two && !numWord(s2, isf, w2)) return "f2 не число\n";
    size_t win = decNum(q, "win", 256); if (win < 8) win = 8; if (win > 4096) win = 4096;
    std::vector<std::pair<uintptr_t, bool>> A, B;
    for (const Seg &g : im.segs) {
        if (!g.r || g.w) continue;
        const uint8_t *p = (const uint8_t *)g.s; size_t n = g.e - g.s;
        for (size_t i = 0; i + 4 <= n; i += 4) {
            uint32_t w; memcpy(&w, p + i, 4);
            if (w == w1) A.push_back({g.s + i, g.x});
            else if (two && w == w2) B.push_back({g.s + i, g.x});
        }
    }
    Str o; int shown = 0;
    if (!two) {
        o = "найдено " + std::to_string(A.size()) + " слов " + wordStr(w1, isf) + "\n";
        for (auto &x : A) { if (shown++ >= 80) { o += "...\n"; break; } o += hx(x.first - im.base) + (x.second ? "  код\n" : "  данные\n"); }
        return o;
    }
    o = Str("слов ") + wordStr(w1, isf) + ": " + std::to_string(A.size()) + ", слов " + wordStr(w2, isf) + ": " + std::to_string(B.size()) + "\nпары в пределах " + std::to_string(win) + " байт:\n";
    for (auto &x : A) for (auto &y : B) {
        size_t d = x.first > y.first ? x.first - y.first : y.first - x.first;
        if (d > win) continue;
        if (shown++ >= 60) { o += "...\n"; return o; }
        o += hx(x.first - im.base) + " (" + wordStr(w1, isf) + ")  " + hx(y.first - im.base) + " (" + wordStr(w2, isf) + ")  " + (x.second ? "код" : "данные") + "\n";
    }
    if (!shown) o += "пар нет: попробуй окно побольше (win) или поищи по одной константе (f2 пусто)\n";
    else o += "Дальше: fset по адресу нужной константы (литерал в коде общий для всех, кто его читает).\n";
    return o;
}

static Str doPatch(const Img &im, uintptr_t off, const std::vector<uint8_t> &b, bool keep) {
    if (keep && g_lib != MGG_TARGET_LIB) return Str("«сохранять на запуски» только для ") + MGG_TARGET_LIB + ": выбери «только сейчас» или основную библиотеку\n";
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

static bool hooksSavedExists();
static void autoApplyHooks(const Img &im);
static void hooksDisable();
// автоприменение сохранённых патчей через несколько секунд после старта игры
static void autoApply() {
    Img im;
    for (int i = 0; i < 120; i++) { im = Img(); if (loadImg(im, MGG_TARGET_LIB)) break; sleep(1); }
    if (im.segs.empty()) return;
    sleep(8);
    std::lock_guard<std::mutex> lk(g_mu);
    Str lock = dataDir() + "/mgg_apply.lock";
    loadFile();
    if (g_saved.empty() && !hooksSavedExists()) return;
    if (access(lock.c_str(), F_OK) == 0) {                       // прошлый запуск упал, пока патчи применялись
        rename(patchFile().c_str(), (patchFile() + ".disabled").c_str());
        remove(lock.c_str());
        g_saved.clear();
        hooksDisable();
        LOGI("прошлый запуск упал после применения патчей и хуков: они отключены (файл .disabled)");
        return;
    }
    FILE *lf = fopen(lock.c_str(), "w"); if (lf) fclose(lf);
    im = Img(); loadImg(im, MGG_TARGET_LIB);
    for (const Saved &s : g_saved) {
        uintptr_t a = im.base + s.off;
        if (!segAt(im, a, s.now.size())) { LOGI("патч %lX вне сегмента", (unsigned long)s.off); continue; }
        std::vector<uint8_t> cur((uint8_t *)a, (uint8_t *)a + s.now.size());
        if (cur == s.now) continue;
        if (cur != s.orig) { LOGI("патч %lX пропущен: байты не совпали (другая версия игры?)", (unsigned long)s.off); continue; }
        Str r = writeMem(im, s.off, s.now, true);
        LOGI("автопатч %lX: %s", (unsigned long)s.off, r.c_str());
    }
    autoApplyHooks(im);
    std::thread([lock] { sleep(45); remove(lock.c_str()); }).detach();   // игра прожила 45 с: считаем запуск безопасным
}

// ---------------------------------------------------------------- хуки (нужен Dobby)
#ifdef MGG_HAS_DOBBY
struct Slot {
    bool used; void *target; void *orig; int mode; uintptr_t val;     // mode: 0 лог, 1 вернуть val без вызова, 2 вызвать и подменить результат, 3 вызвать, подставив val вместо аргумента arg, 4 после успешного вызова сломать блоки вокруг (val = радиус 1–2)
    uintptr_t off; std::atomic<uint32_t> calls; uintptr_t last[8];
    int arg; bool arm; uint8_t sig[8]; long long t0;                           // arg — какой аргумент подменять (режим 3); sig — первые байты функции до хука (для сохранения и проверки версии); t0 — время постановки, мс
    uintptr_t seen[8]; uint32_t seenN[8]; uint32_t rr;               // разные a0 (this), которые видели при вызовах: так находятся адреса объектов (моб, игрок)
};
static Slot g_slots[16];
static bool guarded(void *dst, const void *src, size_t n);          // определена ниже (безопасное чтение памяти)
static thread_local bool g_inArea = false;                         // защита от повторного входа в режиме 4

template <int N>
static uintptr_t hk(uintptr_t a0, uintptr_t a1, uintptr_t a2, uintptr_t a3, uintptr_t a4, uintptr_t a5, uintptr_t a6, uintptr_t a7) {
    Slot &s = g_slots[N];
    s.calls++;
    s.last[0] = a0; s.last[1] = a1; s.last[2] = a2; s.last[3] = a3; s.last[4] = a4; s.last[5] = a5; s.last[6] = a6; s.last[7] = a7;
    int ix = -1;
    for (int i = 0; i < 8; i++) if (s.seen[i] == a0) { ix = i; break; }
    if (ix < 0) { ix = (int)(s.rr++ & 7); s.seen[ix] = a0; s.seenN[ix] = 0; }
    s.seenN[ix]++;
    if (s.mode == 1) return s.val;
    uintptr_t a[8] = {a0, a1, a2, a3, a4, a5, a6, a7};
    if (s.mode == 3 && s.arg >= 0 && s.arg < 8) a[s.arg] = s.val;
    uintptr_t r = ((uintptr_t(*)(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t))s.orig)(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    if (s.mode == 4 && !g_inArea && (r & 0xFF) && a[1] > 0x10000) {   // слом вокруг: оригинал уже сломал блок, ломаем соседей
        int p[3];
        if (guarded(p, (const void *)a[1], 12) && p[0] > -30000000 && p[0] < 30000000 && p[2] > -30000000 && p[2] < 30000000) {
            int R = s.val < 1 ? 1 : s.val > 2 ? 2 : (int)s.val;       // радиус 1 = 3x3x3, 2 = 5x5x5 (больше нельзя: зависнет)
            g_inArea = true;
            for (int dx = -R; dx <= R; dx++) for (int dy = -R; dy <= R; dy++) for (int dz = -R; dz <= R; dz++) {
                if (!dx && !dy && !dz) continue;
                int q[3] = {p[0] + dx, p[1] + dy, p[2] + dz};          // BlockPos const& = указатель на 3 int
                ((uintptr_t(*)(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t))s.orig)(a[0], (uintptr_t)q, a[2], a[3], a[4], a[5], a[6], a[7]);
            }
            g_inArea = false;
        }
    }
    if (s.mode == 5 && !g_inArea && (r & 0xFF) && a[1] > 0x10000) {   // зона: пластина W x H (в плоскости грани) на D блоков вглубь
        int p[3];
        if (guarded(p, (const void *)a[1], 12) && p[0] > -30000000 && p[0] < 30000000 && p[2] > -30000000 && p[2] < 30000000) {
            int W = (int)(s.val & 0xFF), H = (int)((s.val >> 8) & 0xFF), D = (int)((s.val >> 16) & 0xFF);
            W = W < 1 ? 1 : W > 9 ? 9 : W; H = H < 1 ? 1 : H > 9 ? 9 : H; D = D < 1 ? 1 : D > 5 ? 5 : D;
            int f = (int)(a[2] & 0xFF); if (f > 5) f = 1;              // грань: 0 низ, 1 верх, 2 север(-z), 3 юг(+z), 4 запад(-x), 5 восток(+x)
            static const int U[6][3] = {{1,0,0},{1,0,0},{1,0,0},{1,0,0},{0,0,1},{0,0,1}};      // ось ширины
            static const int V[6][3] = {{0,0,1},{0,0,1},{0,1,0},{0,1,0},{0,1,0},{0,1,0}};      // ось высоты
            static const int Nn[6][3] = {{0,1,0},{0,-1,0},{0,0,1},{0,0,-1},{1,0,0},{-1,0,0}};  // внутрь блока (против нормали грани)
            g_inArea = true;
            for (int n = 0; n < D; n++) for (int v = -(H - 1) / 2; v <= H / 2; v++) for (int u = -(W - 1) / 2; u <= W / 2; u++) {
                if (!u && !v && !n) continue;
                int q[3] = {p[0] + u * U[f][0] + v * V[f][0] + n * Nn[f][0],
                            p[1] + u * U[f][1] + v * V[f][1] + n * Nn[f][1],
                            p[2] + u * U[f][2] + v * V[f][2] + n * Nn[f][2]};
                ((uintptr_t(*)(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t))s.orig)(a[0], (uintptr_t)q, a[2], a[3], a[4], a[5], a[6], a[7]);
            }
            g_inArea = false;
        }
    }
    if (s.mode == 6 && !g_inArea && (r & 0xFF) && a[1] > 0x10000 && (a[2] & 0xFF) <= 5) {   // Multiple place: после успешной постановки ставим пластину W x H на той же грани
        int p[3];
        if (guarded(p, (const void *)a[1], 12) && p[0] > -30000000 && p[0] < 30000000 && p[2] > -30000000 && p[2] < 30000000) {
            int W = (int)(s.val & 0xFF), H = (int)((s.val >> 8) & 0xFF);
            W = W < 1 ? 1 : W > 9 ? 9 : W; H = H < 1 ? 1 : H > 9 ? 9 : H;
            int f = (int)(a[2] & 0xFF);                                // грань, по которой кликнули: 0 низ, 1 верх, 2 север, 3 юг, 4 запад, 5 восток
            static const int PU[6][3] = {{1,0,0},{1,0,0},{1,0,0},{1,0,0},{0,0,1},{0,0,1}};
            static const int PV[6][3] = {{0,0,1},{0,0,1},{0,1,0},{0,1,0},{0,1,0},{0,1,0}};
            g_inArea = true;
            for (int v = -(H - 1) / 2; v <= H / 2; v++) for (int u = -(W - 1) / 2; u <= W / 2; u++) {
                if (!u && !v) continue;
                int q[3] = {p[0] + u * PU[f][0] + v * PV[f][0], p[1] + u * PU[f][1] + v * PV[f][1], p[2] + u * PU[f][2] + v * PV[f][2]};
                ((uintptr_t(*)(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t))s.orig)(a[0], (uintptr_t)q, a[2], a[3], a[4], a[5], a[6], a[7]);
            }
            g_inArea = false;
        }
    }
    return s.mode == 2 ? s.val : r;
}
template <size_t... I>
static std::array<void *, sizeof...(I)> mkHooks(std::index_sequence<I...>) { return {{(void *)&hk<(int)I>...}}; }
static std::array<void *, 16> g_hk = mkHooks(std::make_index_sequence<16>{});

static long long hkNow() { return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
static int hkMode(const Str &m) { return m == "ret" ? 1 : m == "set" ? 2 : m == "arg" ? 3 : m == "area" ? 4 : m == "zone" ? 5 : m == "place" ? 6 : 0; }
static Str hooksFile() { return dataDir() + "/mgg_hooks.txt"; }

static Str hooksList() {
    Str out; long long now = hkNow();
    for (int i = 0; i < 16; i++) {
        const Slot &s = g_slots[i];
        if (!s.used) continue;
        const char *m = s.mode == 0 ? "лог" : s.mode == 1 ? "ret" : s.mode == 2 ? "set" : s.mode == 3 ? "арг" : s.mode == 4 ? "area" : s.mode == 5 ? "зона" : "place";
        uint32_t c = s.calls.load(); double sec = (now - s.t0) / 1000.0; char t[64];
        snprintf(t, sizeof t, "%.1f", sec > 0.5 ? c / sec : 0.0);
        out += "#" + std::to_string(i) + " " + hx(s.off) + (s.arm ? " ARM" : " T") + " режим=" + m + (s.mode == 3 ? " арг=" + std::to_string(s.arg) : Str()) + " val=" + hx(s.val) + " вызовов=" + std::to_string(c) + " (" + t + "/с)\n   арги:";
        for (int k = 0; k < 8; k++) out += " " + hx(s.last[k]);
        std::vector<std::pair<uint32_t, uintptr_t>> th;
        for (int k = 0; k < 8; k++) if (s.seenN[k]) th.push_back({s.seenN[k], s.seen[k]});
        std::sort(th.begin(), th.end(), [](const std::pair<uint32_t, uintptr_t> &x, const std::pair<uint32_t, uintptr_t> &y) { return x.first > y.first; });
        if (!th.empty()) { out += "\n   this:"; for (auto &p : th) out += " " + hx(p.second) + "×" + std::to_string(p.first); }
        out += "\n";
    }
    return out.empty() ? "хуков нет\n" : out;
}

// Thumb или ARM? isa: 0 авто, 1 Thumb, 2 ARM. Авто: адрес не кратен 4 = Thumb (ARM всегда выровнен по 4);
// иначе смотрим первые 4 слова: в ARM-коде почти у всех условие "всегда" (старший полубайт 0xE) и привычные начала функций.
static bool hookIsArm(uintptr_t a, int isa) {
    if (isa == 1) return false;
    if (isa == 2) return true;
    if (a & 3) return false;
    uint32_t w[4]; if (!guarded(w, (const void *)a, 16)) return false;
    int al = 0; for (int i = 0; i < 4; i++) if ((w[i] >> 28) == 0xE) al++;
    uint32_t f = w[0];
    bool strong = (f & 0xFFFF0000u) == 0xE92D0000u || f == 0xE52DE004u || (f & 0xFFFFF000u) == 0xE24DD000u || f == 0xE12FFF1Eu ||
                  (f & 0xFFFF0FFFu) == 0xE1A00000u || (f & 0xFFFFF000u) == 0xE59F0000u || (f & 0xFFF00000u) == 0xE3000000u ||
                  (f & 0xFFF00000u) == 0xE3A00000u || (f & 0xFF000000u) == 0xEA000000u || (f & 0xFFF0F000u) == 0xE5900000u;
    return al == 4 || (al == 3 && strong);
}

// единая постановка хука (из панели и из автозагрузки): off — смещение функции; нечётное = Thumb (как в таблице символов), isa задаёт Thumb/ARM
static int hookInstall(const Img &im, uintptr_t off, int mode, int arg, uintptr_t val, Str &msg, int isa = 0) {
    if (off & 1) { isa = 1; off &= ~(uintptr_t)1; }
    for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].off == off) { msg = "на этом смещении уже есть хук #" + std::to_string(i); return -1; }
    int id = -1;
    for (int i = 0; i < 16; i++) if (!g_slots[i].used) { id = i; break; }
    if (id < 0) { msg = "все 16 слотов заняты"; return -1; }
    uintptr_t a = im.base + off;
    if (!segAt(im, a, 8)) { msg = "смещение вне сегмента библиотеки"; return -1; }
    bool arm = hookIsArm(a, isa);
    if (arm && (a & 3)) { msg = "ARM-функция должна быть выровнена по 4 (смещение кратно 4)"; return -1; }
    Slot &s = g_slots[id];
    s.mode = mode; s.val = val; s.arg = arg > 7 ? 7 : arg < 0 ? 0 : arg; s.off = off; s.arm = arm; s.calls = 0; s.t0 = hkNow(); s.rr = 0;
    for (int k = 0; k < 8; k++) { s.seen[k] = 0; s.seenN[k] = 0; s.last[k] = 0; }
    memcpy(s.sig, (const void *)a, 8);                                 // до хука: потом тут будет прыжок Dobby
    s.target = (void *)(arm ? a : a + 1);                              // +1 только для Thumb: Dobby по младшему биту выбирает режим
    int rc = MGG_HOOK(s.target, g_hk[id], &s.orig);
    if (rc != 0) { msg = "Dobby вернул ошибку " + std::to_string(rc) + (arm ? " (ARM)" : " (Thumb)"); return -1; }
    s.used = true; return id;
}

// автопоиск GameMode::destroyBlock (символы вырезаны): "8GameMode" → typeinfo → vtable (слово перед typeinfo = 0) → слот 3. Возвращает смещение (+1 = Thumb)
static uintptr_t gmVtable(const Img &im, Str &why) {   // адрес слота 0 в vtable GameMode (первая запись после typeinfo)
    static const char key[] = "8GameMode";
    std::vector<uintptr_t> names;
    for (const Seg &g : im.segs) {
        if (!g.r) continue;
        const uint8_t *p = (const uint8_t *)g.s; size_t n = g.e - g.s;
        for (size_t i = 1; i + sizeof key <= n; i++)
            if (p[i] == '8' && p[i - 1] == 0 && memcmp(p + i, key, sizeof key) == 0) names.push_back(g.s + i);
    }
    if (names.empty()) { why = "не найдена строка 8GameMode (другая сборка?)\n"; return 0; }
    auto findWord = [&](uintptr_t val, std::vector<uintptr_t> &out) {
        for (const Seg &g : im.segs) {
            if (!g.r || g.x) continue;
            const uint32_t *w = (const uint32_t *)g.s; size_t n = (g.e - g.s) / 4;
            for (size_t i = 0; i < n; i++) if (w[i] == (uint32_t)val) out.push_back(g.s + i * 4);
        }
    };
    for (uintptr_t nm : names) {
        std::vector<uintptr_t> ti; findWord(nm, ti);
        for (uintptr_t t : ti) {
            uintptr_t info = t - 4; std::vector<uintptr_t> vt; findWord(info, vt);
            for (uintptr_t h : vt) {
                if (!segAt(im, h - 4, 4) || *(const uint32_t *)(h - 4) != 0) continue;       // offset_to_top = 0: это vtable самого GameMode, а не наследника
                if (!segAt(im, h + 16, 4)) continue;
                uint32_t fp = *(const uint32_t *)(h + 4 + 4 * 3);                              // проверка на слоте 3 (destroyBlock)
                if (!segAt(im, fp & ~1u, 4)) continue;
                const Seg *sg = segAt(im, fp & ~1u, 4); if (!sg || !sg->x) continue;
                return h + 4;
            }
        }
    }
    why = "vtable GameMode не найден\n"; return 0;
}

// функция из слота vtable GameMode: смещение (+1 = Thumb). Слоты: 3 = destroyBlock, 7 = buildBlock, 11 = getPickRange (не везде одинаково: см. «Слоты GameMode»)
static uintptr_t findGameModeSlot(const Img &im, int slot, Str &why) {
    uintptr_t v = gmVtable(im, why);
    if (!v) return 0;
    if (slot < 0 || !segAt(im, v + 4 * slot, 4)) { why = "слот вне vtable\n"; return 0; }
    uint32_t fp = *(const uint32_t *)(v + 4 * slot);
    const Seg *sg = segAt(im, fp & ~1u, 4);
    if (!sg || !sg->x) { why = "слот " + std::to_string(slot) + " не указывает на код (другая сборка или конец vtable)\n"; return 0; }
    return (uintptr_t)(fp - im.base);
}

// диагностика: что лежит в слотах vtable GameMode (смещение и первые байты). Короткие функции (bx lr рядом с началом) — вероятные геттеры вроде getPickRange
static Str gmSlots(const Img &im, size_t n) {
    Str why; uintptr_t v = gmVtable(im, why);
    if (!v) return why;
    Str o = "vtable GameMode: " + hx(v - im.base) + " (слот 0 = деструктор)\nслот  смещение  байты\n";
    for (size_t i = 0; i < n && i < 90; i++) {
        if (!segAt(im, v + 4 * i, 4)) break;
        uint32_t fp = rd32(v + 4 * i);
        const Seg *sg = segAt(im, fp & ~1u, 8);
        if (!sg || !sg->x) { o += std::to_string(i) + "  - не код\n"; continue; }
        const uint8_t *b = (const uint8_t *)(uintptr_t)(fp & ~1u);
        bool shortFn = false;
        if (fp & 1) for (int k = 0; k < 8; k += 2) if (b[k] == 0x70 && b[k + 1] == 0x47) shortFn = true;
        o += std::to_string(i) + "  " + hx(fp - im.base) + "  " + hexs(std::vector<uint8_t>(b, b + 8)) + (shortFn ? "  короткая" : "") + "\n";
    }
    return o;
}

// заготовки: готовые «хуки с названием». Слот >= 0: адрес берётся из vtable GameMode; -1: нужен адрес от тебя (заготовка)
struct Pre { const char *id, *name; int slot; bool isf; const char *def; const char *hint; };
static const Pre kPre[] = {
    {"reach",      "Reach (дальность руки)",  11, true,  "7.0",    "GameMode::getPickRange: float, ваниль около 5. Слот 11 — предположение: сверь по «Слоты GameMode» (короткая функция, вызывается каждый кадр)."},
    {"breakspd",   "Скорость слома",          -1, true,  "1000.0", "Нужен адрес функции скорости/прогресса слома. Ищи: Lib → sym по destroy, либо hook в режиме лог и ломай блок."},
    {"viewdist",   "Лимит чанков",            -1, false, "96",     "Нужен адрес функции, что зажимает дальность прорисовки. Проще константой: карточка «Лимиты», int-пара."},
    {"vibrant",    "Vibrant Visuals везде",   -1, false, "1",      "Нужен адрес проверки «устройство поддерживает Vibrant Visuals» (возвращает bool). Значение 1."},
    {"timefreeze", "Заморозка времени",       -1, false, "0",      "Нужен адрес обновления времени суток (Level). Режим ret пропускает вызов. Только одиночная игра."},
    {"weather",    "Погода: заморозка",       -1, false, "0",      "Нужен адрес обновления погоды (Weather/Level tick). Режим ret пропускает вызов."},
    {"fly",        "Полёт",                   -1, false, "1",      "Нужен адрес проверки «может летать» (abilities игрока). Значение 1. Только одиночная игра."},
    {"noclip",     "Noclip",                  -1, false, "1",      "Нужен адрес проверки столкновений игрока. Значение 1. Только одиночная игра."},
};
static std::map<Str, int> g_preSlot;                                   // id заготовки -> номер слота хука

static Str preList() {
    Str o;
    for (const Pre &p : kPre) {
        bool on = false; Str off = "-";
        auto it = g_preSlot.find(p.id);
        if (it != g_preSlot.end() && g_slots[it->second].used) { off = hx(g_slots[it->second].off); on = g_slots[it->second].mode == 1; }
        o += Str(p.id) + "\t" + p.name + "\t" + (on ? "1" : "0") + "\t" + (p.slot >= 0 ? std::to_string(p.slot) : Str("-")) + "\t" + p.def + "\t" + off + "\t" + p.hint + "\n";
    }
    return o;
}

static Str preSet(const Img &im, const Params &q) {
    Str id = P(q, "id"); const Pre *pp = nullptr;
    for (const Pre &p : kPre) if (id == p.id) pp = &p;
    if (!pp) return "нет такой заготовки\n";
    Str on = P(q, "on", "1"); auto it = g_preSlot.find(id);
    if (on == "0") {
        if (it == g_preSlot.end() || !g_slots[it->second].used) return "не включено\n";
        g_slots[it->second].mode = 0;                                  // хук остаётся стоять в режиме лога
        return Str("выключено: ") + pp->name + "\n";
    }
    uint32_t w = 0; Str vs = P(q, "v"); if (vs.empty()) vs = pp->def;
    if (!numWord(vs, pp->isf, w)) return "значение не число: " + vs + "\n";
    uintptr_t off = 0;
    if (!hexNum(q, "a", off)) {
        Str ss = P(q, "s"); int sl = ss.empty() ? pp->slot : atoi(ss.c_str());
        if (sl < 0) return Str("заготовка «") + pp->name + "»: впиши адрес функции (hex) или слот vtable GameMode.\n" + pp->hint + "\n";
        Str why; off = findGameModeSlot(im, sl, why); if (!off) return why;
    }
    uintptr_t base = off & ~(uintptr_t)1; int use = -1;
    if (it != g_preSlot.end() && g_slots[it->second].used) { if (g_slots[it->second].off == base) use = it->second; else g_slots[it->second].mode = 0; }
    if (use < 0) for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].off == base) {
        if (g_slots[i].mode == 5 || g_slots[i].mode == 6) return "на этом адресе уже стоит Multiple destroy/place\n";
        use = i; break;
    }
    if (use >= 0) { g_slots[use].mode = 1; g_slots[use].val = w; g_preSlot[id] = use; return Str("включено: ") + pp->name + " = " + vs + " (хук #" + std::to_string(use) + ")\n"; }
    Str msg; int n = hookInstall(im, off, 1, 0, w, msg, 0);
    if (n < 0) return msg + "\n";
    g_preSlot[id] = n;
    return Str("включено: ") + pp->name + " = " + vs + " (хук #" + std::to_string(n) + " на " + hx(g_slots[n].off) + ")\n";
}

static uintptr_t findDestroyBlock(const Img &im, Str &why) { return findGameModeSlot(im, 3, why); }   // слот 3 = GameMode::destroyBlock

static Str hooksSave() {
    int n = 0; Str body = "HOOKS1\n"; char t[96];
    for (const Slot &s : g_slots) {
        if (!s.used) continue;
        snprintf(t, sizeof t, "%lX %d %d %lX ", (unsigned long)s.off, s.mode, s.arg, (unsigned long)s.val); body += t;
        for (int k = 0; k < 8; k++) { snprintf(t, sizeof t, "%02X", s.sig[k]); body += t; }
        body += s.arm ? " 2" : " 1";                                   // ISA: 1 Thumb, 2 ARM (старые файлы без поля = Thumb)
        body += "\n"; n++;
    }
    if (!n) return "нет хуков для сохранения\n";
    FILE *f = fopen(hooksFile().c_str(), "w"); if (!f) return "не могу писать " + hooksFile() + "\n";
    fputs(body.c_str(), f); fclose(f);
    return "сохранено хуков: " + std::to_string(n) + ". Они поставятся при старте игры после патчей, если первые байты функции не изменились (проверка версии). Если игра упадёт при этом, хуки отключатся сами (файл .disabled)\n";
}
static Str hooksApply(const Img &im) {
    FILE *f = fopen(hooksFile().c_str(), "r"); if (!f) return "сохранённых хуков нет\n";
    Str o; char line[256]; bool first = true;
    while (fgets(line, sizeof line, f)) {
        if (first) { first = false; if (strncmp(line, "HOOKS1", 6) != 0) { o += "неверный формат файла хуков\n"; break; } continue; }
        unsigned long off = 0, val = 0; int mode = 0, arg = 0, isa = 1; char sg[40] = {0};
        int nf = sscanf(line, "%lx %d %d %lx %33s %d", &off, &mode, &arg, &val, sg, &isa);
        if (nf < 5 || strlen(sg) != 16 || mode < 0 || mode > 6) continue;
        if (nf < 6 || isa < 1 || isa > 2) isa = 1;
        std::vector<uint8_t> want; if (!unhex(sg, want)) continue;
        bool already = false;
        for (const Slot &s : g_slots) if (s.used && s.off == off) already = true;
        if (already) { o += hx(off) + ": хук уже стоит\n"; continue; }
        uintptr_t a = im.base + off;
        if (!segAt(im, a, 8)) { o += hx(off) + ": вне сегмента, пропущен\n"; continue; }
        if (memcmp((const void *)a, want.data(), 8) != 0) { o += hx(off) + ": пропущен, байты функции другие (другая версия игры?)\n"; continue; }
        Str msg; int id = hookInstall(im, off, mode, arg, val, msg, isa);
        o += id >= 0 ? "хук #" + std::to_string(id) + " на " + hx(off) + " поставлен\n" : hx(off) + ": " + msg + "\n";
    }
    fclose(f); return o.empty() ? "файл хуков пуст\n" : o;
}
static bool hooksSavedExists() { return access(hooksFile().c_str(), F_OK) == 0; }
static void hooksDisable() { rename(hooksFile().c_str(), (hooksFile() + ".disabled").c_str()); }
static void autoApplyHooks(const Img &im) { if (hooksSavedExists()) { Str r = hooksApply(im); LOGI("автохуки: %s", r.c_str()); } }
#else
static bool hooksSavedExists() { return false; }
static void hooksDisable() {}
static void autoApplyHooks(const Img &) {}
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
#include <set>
#include <climits>
#include <algorithm>
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

// ---------------------------------------------------------------- Символы: имя функции → смещение (из .dynsym загруженной библиотеки)
// Если libminecraftpe.so экспортирует имена (_ZN8GameMode12destroyBlockE…), офсет функции находится по имени, без ручного поиска.
static Str symPretty(const Str &m) {                                  // _ZN8GameMode12destroyBlockE… → GameMode::destroyBlock
    if (m.compare(0, 3, "_ZN") != 0) return Str();
    size_t i = 3; if (i < m.size() && m[i] == 'K') i++;
    Str out;
    while (i < m.size() && isdigit((unsigned char)m[i])) {
        size_t n = 0; while (i < m.size() && isdigit((unsigned char)m[i])) n = n * 10 + (size_t)(m[i++] - '0');
        if (n == 0 || i + n > m.size()) break;
        if (!out.empty()) out += "::";
        out += m.substr(i, n); i += n;
    }
    if (out.empty()) return Str();
    if (i + 1 < m.size() && m[i] == 'C' && isdigit((unsigned char)m[i + 1])) out += " (конструктор)";
    else if (i + 1 < m.size() && m[i] == 'D' && isdigit((unsigned char)m[i + 1])) out += " (деструктор)";
    return out;
}
static size_t symGnuCount(uintptr_t gh, bool is64) {
    uint32_t h[4]; if (!guarded(h, (const void *)gh, 16)) return 0;
    uint32_t nb = h[0], symoff = h[1], bloom = h[2];
    if (nb == 0 || nb > (1u << 22)) return 0;
    uintptr_t buckets = gh + 16 + (uintptr_t)bloom * (is64 ? 8 : 4), chain = buckets + (uintptr_t)nb * 4;
    std::vector<uint32_t> b(nb); if (!guarded(b.data(), (const void *)buckets, (size_t)nb * 4)) return 0;
    uint32_t mx = 0; for (uint32_t v : b) if (v > mx) mx = v;
    if (mx < symoff) return symoff;
    uint32_t idx = mx;
    for (uint32_t k = 0; k < 4000000; k++) { uint32_t c; if (!guarded(&c, (const void *)(chain + (uintptr_t)(idx - symoff) * 4), 4)) break; idx++; if (c & 1) break; }
    return idx;
}
// sym: s — часть имени (без регистра), all=1 — ещё и переменные, max — сколько показать
static Str symRoute(const Img &im, const Params &q) {
    if (im.segs.empty()) return "#\tбиблиотека не найдена\n";
    uint8_t eh[64]; if (!guarded(eh, (const void *)im.base, sizeof eh) || memcmp(eh, "\x7f""ELF", 4) != 0) return "#\tзаголовок ELF не читается\n";
    bool is64 = eh[4] == 2; size_t PS = is64 ? 8 : 4;
    uint64_t phoff = 0; uint32_t phn = 0, phes = 0;
    if (is64) { memcpy(&phoff, eh + 0x20, 8); phes = eh[0x36] | (eh[0x37] << 8); phn = eh[0x38] | (eh[0x39] << 8); }
    else { uint32_t t; memcpy(&t, eh + 0x1C, 4); phoff = t; phes = eh[0x2A] | (eh[0x2B] << 8); phn = eh[0x2C] | (eh[0x2D] << 8); }
    uintptr_t dyn = 0; size_t dynsz = 0;
    for (uint32_t i = 0; i < phn && i < 64; i++) {
        uint8_t ph[64]; if (!guarded(ph, (const void *)(im.base + phoff + (uint64_t)i * phes), phes < sizeof ph ? phes : sizeof ph)) break;
        uint32_t type; memcpy(&type, ph, 4); if (type != 2) continue;
        if (is64) { uint64_t va, ms; memcpy(&va, ph + 16, 8); memcpy(&ms, ph + 40, 8); dyn = im.base + (uintptr_t)va; dynsz = (size_t)ms; }
        else { uint32_t va, ms; memcpy(&va, ph + 8, 4); memcpy(&ms, ph + 20, 4); dyn = im.base + va; dynsz = ms; }
    }
    if (!dyn) return "#\tнет секции динамики (PT_DYNAMIC)\n";
    uintptr_t symtab = 0, strtab = 0, hash = 0, gnu = 0;
    for (size_t o = 0; o + 2 * PS <= dynsz && o < 0x4000; o += 2 * PS) {
        uint64_t tag = 0, val = 0; if (!guarded(&tag, (const void *)(dyn + o), PS) || !guarded(&val, (const void *)(dyn + o + PS), PS)) break;
        if (!is64) { tag &= 0xFFFFFFFFull; val &= 0xFFFFFFFFull; }
        if (tag == 0) break;
        uintptr_t p = (uintptr_t)val; if (p < im.base) p += im.base;       // у разных линкеров адреса в .dynamic — относительные или уже абсолютные
        if (tag == 6) symtab = p; else if (tag == 5) strtab = p; else if (tag == 4) hash = p; else if (tag == 0x6ffffef5) gnu = p;
    }
    if (!symtab || !strtab) return "#\tв библиотеке нет таблицы экспортируемых символов\n";
    size_t n = 0;
    if (hash) { uint32_t nc; if (guarded(&nc, (const void *)(hash + 4), 4)) n = nc; }
    if (!n && gnu) n = symGnuCount(gnu, is64);
    if (!n || n > 2000000) return "#\tне смог определить число символов\n";
    Str nd = P(q, "s"); std::transform(nd.begin(), nd.end(), nd.begin(), [](unsigned char c) { return (char)tolower(c); });
    if (nd.size() < 2) return "#\tвведи часть имени (от 2 символов), например destroyBlock\n";
    bool allk = P(q, "all") == "1"; size_t mx = decNum(q, "max", 100), cnt = 0, total = 0; Str o;
    size_t es = is64 ? 24 : 16; std::vector<uint8_t> blk;
    for (size_t i0 = 0; i0 < n; i0 += 4096) {
        size_t m = std::min<size_t>(4096, n - i0); blk.assign(m * es, 0);
        if (!guarded(blk.data(), (const void *)(symtab + i0 * es), m * es)) continue;
        for (size_t k = 0; k < m; k++) {
            const uint8_t *e = &blk[k * es]; uint32_t nm; memcpy(&nm, e, 4);
            uint8_t info; uint16_t shn; uint64_t val, sz;
            if (is64) { info = e[4]; memcpy(&shn, e + 6, 2); memcpy(&val, e + 8, 8); memcpy(&sz, e + 16, 8); }
            else { info = e[12]; memcpy(&shn, e + 14, 2); uint32_t v32, s32; memcpy(&v32, e + 4, 4); memcpy(&s32, e + 8, 4); val = v32; sz = s32; }
            int ty = info & 0xF; if (shn == 0 || val == 0 || !(ty == 2 || (allk && ty == 1))) continue;
            char nb[256]; size_t got = 0;
            for (size_t L = sizeof nb; L >= 8; L /= 2) if (guarded(nb, (const void *)(strtab + nm), L)) { got = L; break; }
            if (!got) continue;
            size_t len = strnlen(nb, got); if (len == got) continue;
            Str name(nb, len), low = name; std::transform(low.begin(), low.end(), low.begin(), [](unsigned char c) { return (char)tolower(c); });
            if (low.find(nd) == Str::npos) continue;
            total++; if (cnt >= mx) continue;
            bool thumb = !is64 && (val & 1); uintptr_t off = (uintptr_t)(thumb ? (val & ~(uint64_t)1) : val);
            char t[48]; snprintf(t, sizeof t, "0x%lX\t%lu\t%c\t", (unsigned long)off, (unsigned long)sz, ty == 1 ? 'D' : is64 ? 'A' : thumb ? 'T' : 'A');
            o += Str(t) + name + "\t" + symPretty(name) + "\n"; cnt++;
        }
    }
    return "#\tнайдено: " + std::to_string(total) + (total > cnt ? " (показаны первые " + std::to_string(cnt) + ")" : Str()) + " · всего символов в таблице: " + std::to_string(n) + "\n" + o;
}

// ---------------------------------------------------------------- Привязанные значения в куче: дальность прорисовки (чанки), FOV, данные игрока
// Значение лежит в куче, и адрес меняется при каждом запуске игры. Поэтому при «Привязать» запоминаем окружение адреса
// (по 16 слов вокруг): слово-указатель в libminecraftpe.so хранится как смещение от базы (стабильно), указатель в любую другую
// память игнорируется (нестабилен), остальное хранится как есть. При «Применить» окружение ищется в куче заново.
// Пока значение заморожено, поток каждые 60 мс перепроверяет окружение: если оно изменилось (вышел из мира, память освобождена),
// заморозка снимается и ничего не пишется в чужую память.
// Привязок несколько: chunk (int), fov (float) — их можно писать; p_* (данные игрока) — только читаются во вкладке World.
struct CsWord { uint8_t k; uint32_t v; };                 // k: 0 пропуск, 1 точное значение, 2 указатель в lib (v = смещение от базы)
struct CsSig { std::vector<CsWord> w; int tgt = 0; };
static const int CS_BEFORE = 16, CS_AFTER = 16;

struct CsSlot {
    const char *name; bool isf; double lo, hi; bool canSet;
    CsSig sg; bool tried; uintptr_t a, base; uint32_t val; bool freeze; Str msg;
    CsSlot(const char *n, bool f, double l, double h, bool c) : name(n), isf(f), lo(l), hi(h), canSet(c), tried(false), a(0), base(0), val(0), freeze(false) {}
};
static CsSlot g_cslot[] = {
    CsSlot("chunk", false, 1, 96, true),
    CsSlot("fov", true, 30, 170, true),
    CsSlot("p_hp", true, 0, 0, false),
    CsSlot("p_armor", true, 0, 0, false),
    CsSlot("p_food", true, 0, 0, false),
    CsSlot("p_pos", true, 0, 0, false),       // X, дальше по +4 Y и +8 Z
    CsSlot("p_rot", true, 0, 0, false),       // два float подряд (поворот)
};
static bool g_cth = false;
static std::mutex g_cm;

static CsSlot *csSlot(const Str &n) { for (CsSlot &s : g_cslot) if (n == s.name) return &s; return nullptr; }
static Str csFile(const CsSlot &s) { Str n = s.name; return dataDir() + (n == "chunk" ? Str("/mgg_chunk.txt") : "/mgg_" + n + ".txt"); }

static std::vector<MapR> allMaps() {
    std::vector<MapR> v; FILE *f = fopen("/proc/self/maps", "r"); if (!f) return v;
    char line[1024];
    while (fgets(line, sizeof line, f)) { unsigned long s, e; if (sscanf(line, "%lx-%lx", &s, &e) == 2) v.push_back({(uintptr_t)s, (uintptr_t)e}); }
    fclose(f); return v;
}
static bool csIsAnchor(const CsWord &c) { return c.k == 2 || (c.k == 1 && c.v >= 0x100); }

// подходит ли слово как значение этой привязки
static bool csValOk(const CsSlot &s, uint32_t raw) {
    if (!s.isf) return raw <= 4096;
    float f; memcpy(&f, &raw, 4);
    if (!(f == f)) return false;
    if (s.canSet) return f >= 1.f && f <= 400.f;           // FOV
    return f > -1e7f && f < 1e7f;
}
static Str csFmt(const CsSlot &s, uint32_t raw) {
    char b[32];
    if (s.isf) { float f; memcpy(&f, &raw, 4); snprintf(b, sizeof b, "%g", f); } else snprintf(b, sizeof b, "%d", (int)raw);
    return b;
}

static bool csBuild(const Img &im, uintptr_t a, CsSig &sg, Str &err) {
    if (a & 3) { err = "адрес должен быть кратен 4"; return false; }
    int n = CS_BEFORE + 1 + CS_AFTER; std::vector<uint32_t> raw(n);
    if (!guarded(raw.data(), (const void *)(a - CS_BEFORE * 4), n * 4)) { err = "память вокруг адреса не читается"; return false; }
    std::vector<MapR> mr = allMaps();
    sg.w.assign(n, CsWord{0, 0}); sg.tgt = CS_BEFORE; int anch = 0;
    for (int i = 0; i < n; i++) {
        if (i == CS_BEFORE) continue;
        uint32_t w = raw[i]; bool inlib = false;
        for (const Seg &g : im.segs) if ((uintptr_t)w >= g.s && (uintptr_t)w < g.e) { inlib = true; break; }
        if (inlib) { sg.w[i] = CsWord{2, (uint32_t)((uintptr_t)w - im.base)}; }
        else {
            bool ptr = false;
            if (w >= 0x10000) for (const MapR &m : mr) if ((uintptr_t)w >= m.s && (uintptr_t)w < m.e) { ptr = true; break; }
            if (!ptr) sg.w[i] = CsWord{1, w};
        }
        if (csIsAnchor(sg.w[i])) anch++;
    }
    if (anch < 3) { err = "вокруг адреса слишком мало уникальных данных, привязка ненадёжна"; return false; }
    return true;
}

// доля совпавших слов: все слова и только «якорные»
static bool csScore(const CsSig &sg, uintptr_t base, uintptr_t a, double &all, double &anc) {
    int n = (int)sg.w.size(); if (!n) return false;
    std::vector<uint32_t> raw(n);
    if (!guarded(raw.data(), (const void *)(a - sg.tgt * 4), n * 4)) return false;
    int t1 = 0, o1 = 0, t2 = 0, o2 = 0;
    for (int i = 0; i < n; i++) {
        const CsWord &c = sg.w[i]; if (!c.k) continue;
        bool ok = c.k == 1 ? raw[i] == c.v : raw[i] == (uint32_t)(base + c.v);
        t1++; if (ok) o1++;
        if (csIsAnchor(c)) { t2++; if (ok) o2++; }
    }
    all = t1 ? (double)o1 / t1 : 0; anc = t2 ? (double)o2 / t2 : 0; return true;
}
static bool csOk(const CsSlot &s, const CsSig &sg, uintptr_t base, uintptr_t a, double lo) {
    double x, y; if (!csScore(sg, base, a, x, y)) return false;
    bool ok; unsigned long long v = memVal(a, 4, ok);
    return ok && x >= lo && y >= lo - 0.1 && csValOk(s, (uint32_t)v);
}

// поиск окружения в куче: берём до 3 якорных слов, ищем каждое (шаг 4 байта), проверяем кандидатов
static Str csFind(const CsSlot &s, const CsSig &sg, uintptr_t base, uintptr_t &found) {
    found = 0; int n = (int)sg.w.size(); std::vector<int> an;
    for (int i = 0; i < n; i++) if (sg.w[i].k == 2) an.push_back(i);
    for (int i = 0; i < n; i++) if (sg.w[i].k == 1 && sg.w[i].v >= 0x100) an.push_back(i);
    if (an.empty()) return "в привязке нет якорных слов\n";
    std::vector<MapR> regs = memMaps(false); std::vector<uint8_t> buf(1 << 20);
    for (size_t ai = 0; ai < an.size() && ai < 3; ai++) {
        int ix = an[ai]; uint32_t want = sg.w[ix].k == 2 ? (uint32_t)(base + sg.w[ix].v) : sg.w[ix].v;
        std::vector<uintptr_t> hits; bool many = false;
        for (const MapR &m : regs) {
            for (uintptr_t a = m.s; a < m.e && !many;) {
                size_t len = std::min<size_t>(buf.size(), m.e - a);
                if (!guarded(buf.data(), (const void *)a, len)) { a += 4096; continue; }
                for (size_t i = 0; i + 4 <= len; i += 4) { uint32_t x; memcpy(&x, buf.data() + i, 4); if (x == want) { hits.push_back(a + i); if (hits.size() > 100000) { many = true; break; } } }
                a += len;
            }
            if (many) break;
        }
        if (many) continue;
        double best = 0; uintptr_t bestA = 0; int ties = 0;
        for (uintptr_t h : hits) {
            uintptr_t t = h + (uintptr_t)(sg.tgt - ix) * 4; double x, y; if (!csScore(sg, base, t, x, y)) continue;
            bool ok; unsigned long long v = memVal(t, 4, ok);
            if (!ok || !csValOk(s, (uint32_t)v) || x < 0.8 || y < 0.7) continue;
            if (x > best + 1e-9) { best = x; bestA = t; ties = 1; } else if (x > best - 1e-9 && t != bestA) ties++;
        }
        if (bestA && ties == 1) { found = bestA; return ""; }
        if (ties > 1) return "найдено несколько одинаково похожих мест (" + std::to_string(ties) + "), привяжи заново\n";
    }
    return "окружение не найдено в куче\n";
}

static bool csSave(const CsSlot &s, const CsSig &sg) {
    FILE *f = fopen(csFile(s).c_str(), "w"); if (!f) return false;
    fprintf(f, "MGGCHUNK1 %d %d\n", sg.tgt, (int)sg.w.size());
    for (const CsWord &c : sg.w) fprintf(f, "%d %X\n", (int)c.k, (unsigned)c.v);
    fclose(f); return true;
}
// Встроенные привязки: сюда вставляется текст «Экспорт привязки» (Функции → карточка → «Адрес и привязка» → «Экспорт»),
// тогда функция работает с первого запуска без ручной привязки. Файл на устройстве, если он есть, главнее.
static const char *kCsPreset[][2] = {{"chunk", ""}, {"fov", ""}};
static bool csParse(const Str &txt, CsSig &sg) {
    const char *p = txt.c_str(); int used = 0, tgt = 0, n = 0;
    if (sscanf(p, "MGGCHUNK1 %d %d%n", &tgt, &n, &used) != 2 || n <= 0 || n >= 200 || tgt < 0 || tgt >= n) return false;
    p += used; CsSig t; t.tgt = tgt;
    for (int i = 0; i < n; i++) { int k = 0; unsigned v = 0; if (sscanf(p, " %d %x%n", &k, &v, &used) != 2 || k < 0 || k > 2) return false; p += used; t.w.push_back(CsWord{(uint8_t)k, (uint32_t)v}); }
    sg = t; return true;
}
static bool csLoad(const CsSlot &s, CsSig &sg) {
    Str txt;
    if (readFile(csFile(s), txt) && csParse(txt, sg)) return true;
    for (auto &pr : kCsPreset) if (Str(pr[0]) == s.name && pr[1][0] && csParse(pr[1], sg)) return true;
    return false;
}
// есть ли привязка (в памяти или в файле); вызывать под g_cm
static bool csHas(CsSlot &s) {
    if (s.sg.w.empty() && !s.tried) { s.tried = true; csLoad(s, s.sg); }
    return !s.sg.w.empty();
}
// 0 = нет привязки, 1 = адрес рабочий, 2 = адрес устарел (нужен поиск заново); вызывать под g_cm
static int csState(CsSlot &s, const Img &im, uintptr_t &a) {
    if (!csHas(s)) return 0;
    if (!s.a || !csOk(s, s.sg, im.base, s.a, 0.6)) return 2;
    a = s.a; return 1;
}

static void csThread() {
    for (;;) {
        usleep(60000);
        std::lock_guard<std::mutex> lk(g_cm);
        for (CsSlot &s : g_cslot) {
            if (!s.freeze || !s.a) continue;
            if (!csOk(s, s.sg, s.base, s.a, 0.6)) { s.freeze = false; s.msg = "заморозка снята: данные по адресу изменились (выход из мира или перезапуск игры)"; continue; }
            bool ok; unsigned long long cur = memVal(s.a, 4, ok);
            if (ok && (uint32_t)cur != s.val) memWrite(s.a, (unsigned long long)s.val, 4);
        }
    }
}

// маршруты: csst (короткий статус), csinfo, csbind, csfind, csapply, csstop;  параметр s = chunk | fov | p_hp | ...
static Str csRoute(const Str &path, const Params &q) {
    CsSlot *sp = csSlot(P(q, "s", "chunk"));
    if (!sp) return "неизвестная привязка\n";
    CsSlot &s = *sp;
    Img im;
    if (!loadImg(im, MGG_TARGET_LIB)) return Str(MGG_TARGET_LIB) + " не найдена в процессе игры\n";
    if (path == "csstop") {
        std::lock_guard<std::mutex> lk(g_cm); s.freeze = false;
        return "заморозка снята, значение осталось как есть (верни его в настройках игры)\n";
    }
    if (path == "csst" || path == "csinfo") {
        std::lock_guard<std::mutex> lk(g_cm);
        uintptr_t a = 0; int st = csState(s, im, a);
        Str o = st == 0 ? "не привязано" : st == 1 ? "привязано" : "привязано, адрес устарел (кнопка «Применить» найдёт заново)";
        if (st == 1) { bool ok; unsigned long long v = memVal(a, 4, ok); o += ok ? " · сейчас " + csFmt(s, (uint32_t)v) : Str(" · не читается"); }
        if (s.freeze) o += " · заморожено на " + csFmt(s, s.val);
        if (!s.msg.empty()) o += "\n" + s.msg;
        if (path == "csinfo" && s.a) o += "\nадрес: " + hx(s.a);
        return o + "\n";
    }
    if (path == "csexport") {
        std::lock_guard<std::mutex> lk(g_cm);
        if (!csHas(s)) return "нет привязки: сначала привяжи адрес\n";
        Str o = Str("# привязка ") + s.name + ": пришли весь текст ниже\nMGGCHUNK1 " + std::to_string(s.sg.tgt) + " " + std::to_string(s.sg.w.size()) + "\n"; char t[32];
        for (const CsWord &c : s.sg.w) { snprintf(t, sizeof t, "%d %X\n", (int)c.k, (unsigned)c.v); o += t; }
        return o;
    }
    if (path == "csbind") {
        uintptr_t a = 0;
        if (!hexNum(q, "a", a)) {
            if (g_cand.size() == 1) a = g_cand[0];
            else return g_cand.empty() ? "нужен адрес (hex): впиши его или найди значение во вкладке Mem\n"
                                       : "во вкладке Mem найдено адресов: " + std::to_string(g_cand.size()) + ". Впиши нужный или сузь поиск до одного\n";
        }
        bool ok; unsigned long long v = memVal(a, 4, ok);
        if (!ok) return "адрес не читается\n";
        if (!csValOk(s, (uint32_t)v)) return "значение по адресу (" + csFmt(s, (uint32_t)v) + ") не подходит для этой привязки: проверь тип (int / float) в поиске\n";
        CsSig sg; Str err; if (!csBuild(im, a, sg, err)) return "не привязал: " + err + "\n";
        if (!csSave(s, sg)) return "не могу записать файл привязки\n";
        std::lock_guard<std::mutex> lk(g_cm);
        s.sg = sg; s.tried = true; s.a = a; s.base = im.base; s.msg.clear(); s.freeze = false;
        int an = 0; for (const CsWord &c : sg.w) if (csIsAnchor(c)) an++;
        return "привязано: " + hx(a) + ", значение " + csFmt(s, (uint32_t)v) + "\nякорных слов: " + std::to_string(an) + " из " + std::to_string(sg.w.size() - 1) + "\nпосле перезапуска игры адрес найдётся сам\n";
    }
    if (path == "csfind" || path == "csapply") {
        CsSig sg; uintptr_t cur;
        { std::lock_guard<std::mutex> lk(g_cm); csHas(s); sg = s.sg; cur = s.a; }
        if (sg.w.empty()) return "сначала «Привязать» адрес (значение ищется во вкладке Mem)\n";
        uintptr_t a = 0; Str how;
        if (cur && csOk(s, sg, im.base, cur, 0.8)) { a = cur; how = "адрес прежний"; }
        else { Str e = csFind(s, sg, im.base, a); if (!e.empty() || !a) return e.empty() ? Str("не нашёл адрес\n") : e; how = "адрес найден заново"; }
        if (path == "csfind") { std::lock_guard<std::mutex> lk(g_cm); s.sg = sg; s.a = a; s.base = im.base; return "ok: " + hx(a) + "\n"; }
        if (!s.canSet) return "эту привязку нельзя записывать\n";
        uint32_t raw;
        if (s.isf) {
            double d = strtod(P(q, "v").c_str(), nullptr); if (!(d == d) || d < s.lo) d = s.lo; if (d > s.hi) d = s.hi;
            float f = (float)d; memcpy(&raw, &f, 4);
        } else {
            size_t n = decNum(q, "v", (size_t)s.lo); if (n < (size_t)s.lo) n = (size_t)s.lo; if (n > (size_t)s.hi) n = (size_t)s.hi;
            raw = (uint32_t)n;
        }
        if (!memWrite(a, (unsigned long long)raw, 4)) return "запись не удалась\n";
        bool ok; unsigned long long rb = memVal(a, 4, ok);
        std::lock_guard<std::mutex> lk(g_cm);
        s.sg = sg; s.a = a; s.base = im.base; s.val = raw; s.freeze = true; s.msg.clear();
        if (!g_cth) { g_cth = true; std::thread(csThread).detach(); }
        return Str(s.name) + " = " + csFmt(s, raw) + " (" + how + " " + hx(a) + ")" + (ok && (uint32_t)rb == raw ? "" : ", но чтение вернуло " + csFmt(s, (uint32_t)rb)) + "\n";
    }
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- World: игрок, ближайший моб, последний сломанный блок
// Игрок: значения берутся из привязок p_* (вкладка World, кнопка-ссылка у строки), скорость считается по смещению позиции.
// Моб и блок: нужны смещения из файла mgg_world.txt (цепочки указателей от базы libminecraftpe.so, они зависят от версии игры).
// Формат файла mgg_world.txt (hex без 0x допустим):
//   player.chain|ГЛОБАЛ,смещ1,смещ2       необязательно: цепочка к структуре игрока (первое число — смещение глобальной переменной от базы lib)
//   player.f|Название|смещение|тип         поле внутри этой структуры
//   mob.list|ГЛОБАЛ,смещ1,...             цепочка к началу вектора указателей на сущности (begin, затем end)
//   mob.pos|смещение                       три float (x,y,z) внутри сущности: по ним ищется ближайший
//   mob.f|Название|смещение|тип            поля сущности (ник, HP ...)
//   block.chain|ГЛОБАЛ,смещ1,...          цепочка к структуре с данными последнего сломанного блока
//   block.f|Название|смещение|тип          поля этой структуры
// тип: float, int, byte, bool, hex, str (std::string / C-строка, автоопределение)
static Str trimS(Str t);
struct WField { Str label; std::vector<uintptr_t> offs; Str type; };
struct WCfg { int bits = 0; Str pchain, mlist, bchain; uintptr_t mpos = 0; bool hasMpos = false; std::vector<WField> pf, mf, bf; };
static std::vector<uintptr_t> wParseOffs(const Str &t) {            // "2B4" или цепочка "10,2B4,8": первое прибавляется к базе, дальше «прочитать указатель + смещение»
    std::vector<uintptr_t> v; size_t i = 0;
    while (i <= t.size()) { size_t j = t.find(',', i); if (j == Str::npos) j = t.size(); Str tk = trimS(t.substr(i, j - i)); if (!tk.empty()) v.push_back((uintptr_t)strtoull(tk.c_str(), nullptr, 16)); i = j + 1; }
    return v;
}
static Str worldFile() { return dataDir() + "/mgg_world.txt"; }
static const char *kWorldHelp =
    "# MGG World: настройки для Mob и Block (и необязательно Player)\n"
    "# Цепочка: ГЛОБАЛ,смещ1,смещ2 — первое число: смещение глобальной переменной от базы libminecraftpe.so,\n"
    "# дальше на каждом шаге читается указатель и прибавляется смещение. Всё в hex.\n"
    "# player.chain|1A2B3C,10\n"
    "# player.f|Прыжок|2C0|byte\n"
    "# mob.list|1A2B3C,40        (вектор указателей на сущности: begin, затем end)\n"
    "# mob.pos|A0                (три float x,y,z внутри сущности)\n"
    "# mob.f|Ник|1D0|str\n"
    "# mob.f|HP|2B4|float\n"
    "# block.chain|1A2B3C,8\n"
    "# block.f|X|0|int\n"
    "# block.f|Y|4|int\n"
    "# block.f|Z|8|int\n"
    "# типы: float, int, byte, bool, hex, str\n"
    "# смещение поля может быть цепочкой: mob.f|HP|10,2B4,8 (первое прибавляется к началу сущности, дальше: прочитать указатель + смещение)\n"
    "# bits|32   (для какой разрядности написан файл; при несовпадении панель предупредит)\n";

static WCfg worldLoad() {
    WCfg c; Str txt;
    if (!readFile(worldFile(), txt)) { FILE *f = fopen(worldFile().c_str(), "w"); if (f) { fputs(kWorldHelp, f); fclose(f); } return c; }
    size_t i = 0;
    while (i <= txt.size()) {
        size_t e = txt.find('\n', i); if (e == Str::npos) e = txt.size();
        Str ln = trimS(txt.substr(i, e - i)); i = e + 1;
        if (ln.empty() || ln[0] == '#') continue;
        std::vector<Str> p; size_t j = 0;
        while (j <= ln.size()) { size_t k = ln.find('|', j); if (k == Str::npos) k = ln.size(); p.push_back(trimS(ln.substr(j, k - j))); j = k + 1; }
        if (p.size() < 2) continue;
        const Str &k = p[0];
        auto fld = [&](std::vector<WField> &v) { if (p.size() >= 4) v.push_back({p[1], wParseOffs(p[2]), p[3]}); };
        if (k == "player.chain") c.pchain = p[1];
        else if (k == "mob.list") c.mlist = p[1];
        else if (k == "bits") c.bits = atoi(p[1].c_str());
        else if (k == "block.chain") c.bchain = p[1];
        else if (k == "mob.pos") { c.mpos = (uintptr_t)strtoull(p[1].c_str(), nullptr, 16); c.hasMpos = true; }
        else if (k == "player.f") fld(c.pf);
        else if (k == "mob.f") fld(c.mf);
        else if (k == "block.f") fld(c.bf);
    }
    return c;
}

static bool wChain(const Img &im, const Str &spec, uintptr_t &out) {
    std::vector<uintptr_t> t; size_t i = 0;
    while (i <= spec.size()) {
        size_t j = spec.find(',', i); if (j == Str::npos) j = spec.size();
        Str tk = trimS(spec.substr(i, j - i)); if (!tk.empty()) t.push_back((uintptr_t)strtoull(tk.c_str(), nullptr, 16));
        i = j + 1;
    }
    if (t.empty()) return false;
    uintptr_t a = im.base + t[0];
    for (size_t k = 1; k < t.size(); k++) {
        uintptr_t p = 0;
        if (!guarded(&p, (const void *)a, sizeof p) || p < 0x10000) return false;
        a = p + t[k];
    }
    out = a; return true;
}

static bool wPrintable(const char *s, size_t n) { if (!n) return false; for (size_t i = 0; i < n; i++) { unsigned char c = (unsigned char)s[i]; if (c < 32 || c == 127) return false; } return true; }
static Str wStr(uintptr_t a, bool &ok) {
    const size_t PS = sizeof(void *);
    uint8_t h[32]; char tmp[96]; ok = true;
    if (!guarded(h, (const void *)a, 3 * PS)) { ok = false; return "—"; }
    if ((h[0] & 1) == 0) {                                        // libc++ короткая строка: длина в первом байте, текст со второго
        size_t n = h[0] >> 1;
        if (n > 0 && n <= 3 * PS - 2 && wPrintable((const char *)h + 1, n)) return Str((const char *)h + 1, n);
    } else {                                                      // libc++ длинная: cap, size, data
        size_t n = 0; uintptr_t p = 0; memcpy(&n, h + PS, PS); memcpy(&p, h + 2 * PS, PS);
        if (n > 0 && n < sizeof tmp && p > 0x10000 && guarded(tmp, (const void *)p, n) && wPrintable(tmp, n)) return Str(tmp, n);
    }
    uintptr_t p = 0; memcpy(&p, h, PS);                           // запасные варианты: указатель на C-строку / текст прямо по адресу
    if (p > 0x10000 && guarded(tmp, (const void *)p, 64)) { size_t n = strnlen(tmp, 64); if (n < 64 && wPrintable(tmp, n)) return Str(tmp, n); }
    size_t n = strnlen((const char *)h, 3 * PS); if (n < 3 * PS && wPrintable((const char *)h, n)) return Str((const char *)h, n);
    ok = false; return "—";
}
static Str wRead(uintptr_t a, const Str &ty, bool &ok) {
    char b[48]; ok = true;
    if (ty == "str") return wStr(a, ok);
    unsigned long long v = memVal(a, ty == "byte" || ty == "bool" ? 1 : 4, ok);
    if (!ok) return "—";
    if (ty == "float") { uint32_t u = (uint32_t)v; float f; memcpy(&f, &u, 4); if (!(f == f) || f > 1e9f || f < -1e9f) { ok = false; return "—"; } snprintf(b, sizeof b, "%.2f", f); return b; }
    if (ty == "int") { snprintf(b, sizeof b, "%d", (int)(uint32_t)v); return b; }
    if (ty == "byte") { snprintf(b, sizeof b, "%u", (unsigned)v); return b; }
    if (ty == "bool") return v ? "да" : "нет";
    snprintf(b, sizeof b, "0x%llX", v); return b;
}
static Str wRow(const Str &key, const Str &label, const Str &val, int st) { return key + "\t" + label + "\t" + val + "\t" + std::to_string(st) + "\n"; }

static Str wFields(uintptr_t base, const std::vector<WField> &fs) {
    Str o;
    for (const WField &f : fs) {
        bool ok = !f.offs.empty(); uintptr_t a = base; Str v = "—";
        if (ok) { a = base + f.offs[0]; for (size_t k = 1; k < f.offs.size() && ok; k++) { uintptr_t pp = 0; if (!guarded(&pp, (const void *)a, sizeof pp) || pp < 0x10000) ok = false; else a = pp + f.offs[k]; } }
        if (ok) v = wRead(a, f.type, ok);
        o += wRow("-", f.label, v, ok ? 1 : 0);
    }
    return o;
}

static bool wPlayerPos(const Img &im, float p[3]) {
    std::lock_guard<std::mutex> lk(g_cm);
    CsSlot *s = csSlot("p_pos"); uintptr_t a = 0;
    if (!s || csState(*s, im, a) != 1) return false;
    return guarded(p, (const void *)a, 12);
}

static double g_wpx = 0, g_wpy = 0, g_wpz = 0; static long long g_wpt = 0; static bool g_wph = false;

static Str worldPlayer() {
    Img im;
    if (!loadImg(im, MGG_TARGET_LIB)) return Str("#\t") + MGG_TARGET_LIB + " не найдена в процессе игры\n";
    struct R { const char *key, *label; int n; };
    static const R rs[] = {{"p_hp", "Здоровье", 1}, {"p_armor", "Броня", 1}, {"p_food", "Голод", 1}, {"p_pos", "Позиция X / Y / Z", 3}, {"p_rot", "Поворот", 2}};
    Str rows, staleKey; int bound = 0, live = 0, stale = 0; bool posOk = false; float pos[3] = {0, 0, 0};
    {
        std::lock_guard<std::mutex> lk(g_cm);
        for (const R &r : rs) {
            CsSlot *s = csSlot(r.key); uintptr_t a = 0; int st = csState(*s, im, a);
            Str val = "—";
            if (st) bound++;
            if (st == 2) { stale++; if (staleKey.empty()) staleKey = r.key; }
            if (st == 1) {
                float v[3] = {0, 0, 0};
                if (guarded(v, (const void *)a, r.n * 4)) {
                    live++; char b[96];
                    if (r.n == 1) snprintf(b, sizeof b, "%.2f", v[0]); else if (r.n == 2) snprintf(b, sizeof b, "%.2f / %.2f", v[0], v[1]); else snprintf(b, sizeof b, "%.2f / %.2f / %.2f", v[0], v[1], v[2]);
                    val = b;
                    if (r.n == 3) { posOk = true; memcpy(pos, v, 12); }
                } else st = 2;
            }
            rows += wRow(r.key, r.label, val, st);
        }
    }
    if (posOk) {                                                  // движение: скорость по смещению позиции
        long long t = nowMs();
        if (g_wph && t - g_wpt >= 50 && t - g_wpt <= 3000) {
            double dt = (t - g_wpt) / 1000.0, dx = pos[0] - g_wpx, dy = pos[1] - g_wpy, dz = pos[2] - g_wpz; char b[48];
            snprintf(b, sizeof b, "%.2f", __builtin_sqrt(dx * dx + dz * dz) / dt); rows += wRow("-", "Скорость (блок/с)", b, 1);
            snprintf(b, sizeof b, "%.2f", dy / dt); rows += wRow("-", "Верт. скорость (блок/с)", b, 1);
        }
        g_wpx = pos[0]; g_wpy = pos[1]; g_wpz = pos[2]; g_wpt = t; g_wph = true;
    } else g_wph = false;
    WCfg c = worldLoad(); uintptr_t pa = 0;
    if ((!c.bits || c.bits == (int)(sizeof(void *) * 8)) && !c.pchain.empty() && wChain(im, c.pchain, pa)) rows += wFields(pa, c.pf);
    Str h = live ? "в мире · данные идут" : stale ? "адреса устарели (вышел из мира?) · ищу заново" : bound ? "ждём мир" : "ничего не привязано: нажми значок-ссылку у строки";
    return "#\t" + h + "\n" + (staleKey.empty() ? Str() : "#stale\t" + staleKey + "\n") + rows;
}

static Str worldMob() {
    Img im;
    if (!loadImg(im, MGG_TARGET_LIB)) return Str("#\t") + MGG_TARGET_LIB + " не найдена в процессе игры\n";
    WCfg c = worldLoad();
    if (c.bits && c.bits != (int)(sizeof(void *) * 8)) return "#\tконфиг написан для " + std::to_string(c.bits) + " bit, а игра сейчас " + std::to_string(sizeof(void *) * 8) + " bit: офсеты не подойдут\n";
    if (c.mlist.empty() || !c.hasMpos) return "#\tне настроено: нужны mob.list и mob.pos в mgg_world.txt (кнопка «Конфиг»)\n";
    const size_t PS = sizeof(void *);
    uintptr_t la = 0, be[2] = {0, 0};
    if (!wChain(im, c.mlist, la) || !guarded(be, (const void *)la, 2 * PS)) return "#\tсписок сущностей не читается (ты не в мире или неверная цепочка)\n";
    if (be[0] < 0x10000 || be[1] < be[0]) return "#\tсписок сущностей пуст\n";
    size_t n = (be[1] - be[0]) / PS;
    if (n == 0 || n > 5000) return "#\tсписок сущностей выглядит неверно (" + std::to_string(n) + " шт.): проверь mob.list\n";
    std::vector<uintptr_t> ents(n);
    if (!guarded(ents.data(), (const void *)be[0], n * PS)) return "#\tсписок сущностей не читается\n";
    float me[3] = {0, 0, 0}; bool hasMe = wPlayerPos(im, me);
    uintptr_t best = 0; double bd = 1e18; size_t good = 0;
    for (uintptr_t e : ents) {
        if (e < 0x10000) continue;
        float p[3]; if (!guarded(p, (const void *)(e + c.mpos), 12)) continue;
        bool fin = true; for (int k = 0; k < 3; k++) if (!(p[k] == p[k]) || p[k] > 3e7f || p[k] < -3e7f) fin = false;
        if (!fin) continue;
        good++;
        double d = 0;
        if (hasMe) { double dx = p[0] - me[0], dy = p[1] - me[1], dz = p[2] - me[2]; d = dx * dx + dy * dy + dz * dz; if (d < 0.0025) continue; }   // сам игрок
        if (!best || d < bd) { best = e; bd = d; }
    }
    if (!best) return "#\tсущностей в списке: " + std::to_string(n) + ", подходящих нет\n";
    char b[48]; Str rows;
    if (hasMe) { snprintf(b, sizeof b, "%.1f", __builtin_sqrt(bd)); rows += wRow("-", "Расстояние (блоков)", b, 1); }
    rows += wFields(best, c.mf);
    return "#\tсущностей: " + std::to_string(good) + (hasMe ? " · показан ближайший" : " · позиция игрока не привязана (Player → Позиция), показан первый") + "\n" + rows;
}

static Str worldBlock() {
    Img im;
    if (!loadImg(im, MGG_TARGET_LIB)) return Str("#\t") + MGG_TARGET_LIB + " не найдена в процессе игры\n";
    WCfg c = worldLoad(); uintptr_t a = 0;
    if (c.bits && c.bits != (int)(sizeof(void *) * 8)) return "#\tконфиг написан для " + std::to_string(c.bits) + " bit, а игра сейчас " + std::to_string(sizeof(void *) * 8) + " bit: офсеты не подойдут\n";
    if (c.bchain.empty() || c.bf.empty()) return "#\tне настроено: нужны block.chain и block.f в mgg_world.txt (кнопка «Конфиг»)\n";
    if (!wChain(im, c.bchain, a)) return "#\tданные блока не читаются (ты не в мире или неверная цепочка)\n";
    return "#\tпоследний сломанный блок\n" + wFields(a, c.bf);
}

static Str worldCfg() {
    WCfg c = worldLoad(); Str t; readFile(worldFile(), t);
    return "файл: " + worldFile() + "\n(правится во вкладке File)\n\n" + t;
}

// ---------------------------------------------------------------- Помощники поиска (строки, соседи, допуск по float, цепочки указателей, путь от объекта)
static bool hInSeg(const Img &im, uintptr_t v) { for (const Seg &g : im.segs) if (v >= g.s && v < g.e) return true; return false; }
static bool hInMaps(const std::vector<MapR> &m, uintptr_t v) {         // m отсортирован по возрастанию
    size_t lo = 0, hi = m.size();
    while (lo < hi) { size_t mid = (lo + hi) / 2; if (m[mid].e <= v) lo = mid + 1; else hi = mid; }
    return lo < m.size() && v >= m[lo].s && v < m[lo].e;
}
static bool hPrint(const uint8_t *s, size_t n) { for (size_t i = 0; i < n; i++) if (s[i] < 32 || s[i] > 126) return false; return n > 0; }

// float с допуском: игра показывает округлённые числа (HP 18.5, координаты 123.45), точное совпадение не годится
static Str hScanF(double v, double tol, bool all) {
    g_cand.clear(); g_prev.clear(); g_csz = 4; g_cf = true;
    std::vector<uint8_t> buf(1 << 20); size_t regions = 0;
    for (const MapR &m : memMaps(all)) {
        regions++;
        for (uintptr_t a = m.s; a < m.e;) {
            size_t n = std::min<size_t>(buf.size(), m.e - a);
            if (!guarded(buf.data(), (const void *)a, n)) { a += 4096; continue; }
            for (size_t i = 0; i + 4 <= n; i += 4) {
                uint32_t u; memcpy(&u, buf.data() + i, 4); float f; memcpy(&f, &u, 4);
                if (!(f == f)) continue;
                double d = (double)f - v; if (d < 0) d = -d;
                if (d > tol) continue;
                g_cand.push_back(a + i); g_prev.push_back(u);
                if (g_cand.size() > 2000000) { g_cand.clear(); g_prev.clear(); return "слишком много совпадений: уменьши допуск или возьми менее частое число\n"; }
            }
            a += n;
        }
    }
    return "областей: " + std::to_string(regions) + ", найдено: " + std::to_string(g_cand.size()) + "\n";
}
// off = 0: само значение; off != 0: float по соседнему адресу (для позиции: Z лежит через 8 байт от X)
static Str hKeepF(intptr_t off, double v, double tol) {
    std::vector<uintptr_t> ka; std::vector<unsigned long long> kp;
    for (uintptr_t c : g_cand) {
        bool ok; unsigned long long cur = memVal(c + off, 4, ok); if (!ok) continue;
        uint32_t u = (uint32_t)cur; float f; memcpy(&f, &u, 4); double d = (double)f - v; if (d < 0) d = -d;
        if (f == f && d <= tol) { ka.push_back(c); kp.push_back(off ? (unsigned long long)0 : cur); }
    }
    if (off) { for (size_t i = 0; i < ka.size(); i++) { bool ok; kp[i] = memVal(ka[i], 4, ok); } }
    g_cand.swap(ka); g_prev.swap(kp);
    return "осталось: " + std::to_string(g_cand.size()) + "\n";
}

// поиск ASCII-строки в памяти (имя моба, ник, id блока)
static Str hStr(const Str &s, bool all) {
    if (s.size() < 2) return "строка слишком короткая\n";
    std::vector<uint8_t> buf(1 << 20); size_t cnt = 0; Str o;
    for (const MapR &m : memMaps(all)) {
        for (uintptr_t a = m.s; a < m.e;) {
            size_t n = std::min<size_t>(buf.size(), m.e - a);
            if (!guarded(buf.data(), (const void *)a, n)) { a += 4096; continue; }
            for (size_t i = 0; i + s.size() <= n; i++) {
                if (buf[i] != (uint8_t)s[0] || memcmp(buf.data() + i, s.data(), s.size()) != 0) continue;
                if (a + i >= (uintptr_t)buf.data() && a + i < (uintptr_t)buf.data() + buf.size()) continue;      // собственный буфер
                size_t k = 0; while (i + k < n && k < 32 && buf[i + k] >= 32 && buf[i + k] < 127) k++;
                o += hx(a + i) + "\t" + Str((const char *)buf.data() + i, k) + "\n";
                if (++cnt >= 3000) return "#\tпоказаны первые 3000, уточни строку\n" + o;
            }
            size_t adv = n; if (a + n < m.e && n > s.size()) adv = n - (s.size() - 1);
            a += adv;
        }
    }
    return "#\tнайдено: " + std::to_string(cnt) + (cnt ? " (часть копий — от самой панели)" : "") + "\n" + o;
}

// слова вокруг адреса с расшифровкой: int, float, указатель в lib / в память / на строку, ASCII внутри слова
static Str hNear(uintptr_t a, size_t before, size_t after) {
    Img im; loadImg(im, MGG_TARGET_LIB);
    const size_t PS = sizeof(void *);
    if (before > 512) before = 512; if (after > 1024) after = 1024;
    a &= ~(uintptr_t)3; uintptr_t st = a - (before & ~(size_t)3); size_t n = ((before & ~(size_t)3) + after) & ~(size_t)3;
    std::vector<uint8_t> b(n + 8, 0);
    if (!guarded(b.data(), (const void *)st, n)) return "#\tпамять вокруг адреса не читается\n";
    std::vector<MapR> mr = memMaps(true);
    Str o = "#\tбаза " + Str(MGG_TARGET_LIB) + " = " + hx(im.base) + ", разрядность " + std::to_string(PS * 8) + "\n"; char t[128];
    for (size_t i = 0; i + 4 <= n; i += 4) {
        uintptr_t ad = st + i; uint32_t u; memcpy(&u, b.data() + i, 4); float f; memcpy(&f, &u, 4);
        intptr_t rel = (intptr_t)ad - (intptr_t)a;
        Str fs; if (f == f && ((f > -1e9f && f < 1e9f)) && (u == 0 || (f > 1e-4f || f < -1e-4f))) { snprintf(t, sizeof t, "%g", f); fs = t; }
        Str note;
        if (ad % PS == 0 && i + PS <= n) {
            uintptr_t p = 0; memcpy(&p, b.data() + i, PS);
            if (p >= 0x10000) {
                if (hInSeg(im, p)) { snprintf(t, sizeof t, "→ lib+0x%lX", (unsigned long)(p - im.base)); note = t; }
                else if (hInMaps(mr, p)) {
                    uint8_t sb[24]; Str tx;
                    if (guarded(sb, (const void *)p, sizeof sb)) { size_t k = 0; while (k < sizeof sb && sb[k] >= 32 && sb[k] < 127) k++; if (k >= 3) tx = " «" + Str((const char *)sb, k) + "»"; }
                    note = "→ память" + tx;
                }
            }
        }
        if (note.empty() && hPrint(b.data() + i, 4) && b[i] != ' ') note = "«" + Str((const char *)b.data() + i, 4) + "»";
        snprintf(t, sizeof t, "%s0x%lX", rel < 0 ? "-" : "+", (unsigned long)(rel < 0 ? -rel : rel));
        o += hx(ad) + "\t" + t + "\t";
        snprintf(t, sizeof t, "%08X", (unsigned)u); o += t; o += "\t" + std::to_string((int)u) + "\t" + fs + "\t" + note + "\n";
    }
    return o;
}

// ---- обратный поиск цепочки указателей: от адреса цели вверх, пока не дойдём до статики в libminecraftpe.so
// Цепочка «ГЛОБАЛ,о1,о2…» читается тем же wChain: адрес = база+ГЛОБАЛ, дальше на каждом шаге читаем указатель и прибавляем смещение.
struct PNode { uintptr_t addr, off; int par; };
static std::mutex g_pm; static bool g_prun = false, g_pcancel = false; static Str g_pstat, g_pres;

// .bss библиотеки лежит анонимной областью сразу за её сегментами (в maps без имени файла): для цепочек это тоже статика
static void addBss(Img &im) {
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f || im.segs.empty()) { if (f) fclose(f); return; }
    char line[1024]; uintptr_t end = 0;
    for (const Seg &g : im.segs) if (g.w && g.e > end) end = g.e;
    while (end && fgets(line, sizeof line, f)) {
        unsigned long s, e; char perms[8] = {0}; Str path;
        if (!mapLine(line, s, e, perms, path) || (uintptr_t)s != end || perms[1] != 'w') continue;
        if (!path.empty() && path != "[anon:.bss]") break;
        im.segs.push_back({(uintptr_t)s, (uintptr_t)e, true, true, false});
        end = (uintptr_t)e;
    }
    fclose(f);
}

static void hPtrWorker(uintptr_t T, int depth, size_t maxoff, bool all) {
    Img im; loadImg(im, MGG_TARGET_LIB); addBss(im);
    const size_t PS = sizeof(void *);
    auto setS = [](const Str &s) { std::lock_guard<std::mutex> lk(g_pm); g_pstat = s; };
    struct Res { int lvl; uintptr_t sum; Str line; };
    std::vector<Res> res;
    std::vector<PNode> nodes; nodes.reserve(400001); nodes.push_back({T, 0, -1});
    auto chainOf = [&](int id) {
        char t[32]; snprintf(t, sizeof t, "%lX", (unsigned long)(nodes[id].addr - im.base)); Str c = t; uintptr_t sum = 0;
        for (int k = id; k >= 0 && nodes[k].par >= 0; k = nodes[k].par) { snprintf(t, sizeof t, ",%lX", (unsigned long)nodes[k].off); c += t; sum += nodes[k].off; }
        return std::make_pair(c, sum);
    };
    if (hInSeg(im, T)) { auto c = chainOf(0); res.push_back({0, 0, c.first}); }
    std::vector<MapR> regs = memMaps(true);
    std::vector<uint8_t> buf(1 << 20);
    std::vector<int> cur{0}; std::vector<uintptr_t> visited{T}; bool trunc = false;
    for (int lvl = 1; lvl <= depth && res.size() < 40 && !trunc; lvl++) {
        std::vector<std::pair<uintptr_t, int>> tg; tg.reserve(cur.size());
        for (int ix : cur) tg.push_back({nodes[ix].addr, ix});
        std::sort(tg.begin(), tg.end());
        std::vector<int> next; size_t regIx = 0;
        for (const MapR &m : regs) {
            regIx++;
            { char t[96]; snprintf(t, sizeof t, "уровень %d из %d: область %zu из %zu, целей %zu", lvl, depth, regIx, regs.size(), tg.size()); setS(t); }
            { std::lock_guard<std::mutex> lk(g_pm); if (g_pcancel) break; }
            for (uintptr_t a = m.s; a < m.e && !trunc;) {
                size_t n = std::min<size_t>(buf.size(), m.e - a);
                if (!guarded(buf.data(), (const void *)a, n)) { a += 4096; continue; }
                for (size_t i = 0; i + PS <= n; i += PS) {
                    uintptr_t w = 0; memcpy(&w, buf.data() + i, PS); if (w < 0x10000) continue;
                    auto it = std::lower_bound(tg.begin(), tg.end(), std::make_pair(w, INT_MIN));
                    if (it == tg.end() || it->first - w > maxoff) continue;
                    uintptr_t A = a + i;
                    if ((A >= (uintptr_t)buf.data() && A < (uintptr_t)buf.data() + buf.size()) ||
                        (A >= (uintptr_t)nodes.data() && A < (uintptr_t)(nodes.data() + 400001)) ||
                        (A >= (uintptr_t)tg.data() && A < (uintptr_t)(tg.data() + tg.capacity()))) continue;      // собственные буферы помощника
                    if (std::binary_search(visited.begin(), visited.end(), A)) continue;
                    nodes.push_back({A, it->first - w, it->second}); int id = (int)nodes.size() - 1;
                    if (hInSeg(im, A)) { auto c = chainOf(id); res.push_back({lvl, c.second, c.first}); }
                    else next.push_back(id);
                    if (nodes.size() >= 400000) { trunc = true; break; }
                }
                a += n;
            }
        }
        { std::lock_guard<std::mutex> lk(g_pm); if (g_pcancel) break; }
        if (next.size() > 5000) { std::sort(next.begin(), next.end(), [&](int x, int y) { return nodes[x].off < nodes[y].off; }); next.resize(5000); }
        for (int ix : next) visited.push_back(nodes[ix].addr);
        std::sort(visited.begin(), visited.end());
        cur.swap(next);
        if (cur.empty()) break;
    }
    std::sort(res.begin(), res.end(), [](const Res &x, const Res &y) { return x.lvl != y.lvl ? x.lvl < y.lvl : x.sum < y.sum; });
    Str o; size_t k = 0;
    for (const Res &r : res) { if (k++ >= 20) break; o += r.line + "\t" + (r.lvl ? "уровней: " + std::to_string(r.lvl) : Str("сам адрес в lib")) + "\n"; }
    std::lock_guard<std::mutex> lk(g_pm);
    g_pres = o; g_prun = false;
    g_pstat = g_pcancel ? "остановлено" : res.empty() ? (trunc ? "слишком много совпадений: уменьши макс. смещение" : "цепочек до статики не найдено: увеличь глубину или смещение") : "найдено цепочек: " + std::to_string(res.size());
}

// ---- прямой поиск: как от начала объекта E добраться до поля A (смещения через запятую, формат полей mob.f / player.f / block.f)
static Str hPath(uintptr_t E, uintptr_t A, int depth, size_t n) {
    const size_t PS = sizeof(void *);
    if (n > 0x1000) n = 0x1000;
    std::vector<MapR> regs = memMaps(true);
    struct N { uintptr_t w; std::vector<uintptr_t> tk; };
    std::vector<N> cur, next; cur.push_back({E, {}});
    std::set<uintptr_t> seen; seen.insert(E);
    std::vector<std::vector<uintptr_t>> found; std::vector<uint8_t> b(n);
    for (int lvl = 0; lvl <= depth && found.size() < 20; lvl++) {
        for (const N &nd : cur) {
            if (!guarded(b.data(), (const void *)nd.w, n)) continue;
            if (A >= nd.w && A < nd.w + n) { std::vector<uintptr_t> t = nd.tk; t.push_back(A - nd.w); found.push_back(t); }
            for (size_t i = 0; i + PS <= n; i += PS) {
                uintptr_t x = 0; memcpy(&x, b.data() + i, PS);
                if (x < 0x10000 || !hInMaps(regs, x)) continue;
                if (A >= x && A < x + n) { std::vector<uintptr_t> t = nd.tk; t.push_back(i); t.push_back(A - x); found.push_back(t); }
                else if (lvl < depth && next.size() < 20000 && !seen.count(x)) { seen.insert(x); std::vector<uintptr_t> t = nd.tk; t.push_back(i); next.push_back({x, t}); }
            }
        }
        cur.swap(next); next.clear();
    }
    if (found.empty()) return "#\tпуть не найден: увеличь глубину / размер окна или проверь адрес объекта\n";
    std::sort(found.begin(), found.end(), [](const std::vector<uintptr_t> &x, const std::vector<uintptr_t> &y) { return x.size() < y.size(); });
    Str o = "#\tнайдено путей: " + std::to_string(found.size()) + "\n"; char t[32];
    for (const auto &f : found) { Str c; for (size_t k = 0; k < f.size(); k++) { snprintf(t, sizeof t, k ? ",%lX" : "%lX", (unsigned long)f[k]); c += t; } o += c + "\t" + std::to_string(f.size() == 1 ? 0 : (f.size() - 1) / 2 + 0) + "\n"; }
    return o;
}

// ---- запись строк в mgg_world.txt: одиночные ключи заменяются, поля (.f) добавляются
static Str wCfgAdd(const Str &line) {
    static const char *ok[] = {"player.chain|", "player.f|", "mob.list|", "mob.pos|", "mob.f|", "block.chain|", "block.f|", "bits|"};
    bool good = line.size() < 300 && line.find('\n') == Str::npos && line.find('\r') == Str::npos;
    Str key; bool multi = false;
    if (good) { good = false; for (const char *k : ok) if (line.compare(0, strlen(k), k) == 0) { good = true; key = k; multi = key.size() > 3 && key.compare(key.size() - 3, 3, ".f|") == 0; } }
    if (!good) return "строка не подходит для конфига\n";
    worldLoad();                                                  // создаст файл с подсказкой, если его ещё нет
    Str txt; readFile(worldFile(), txt); Str out; size_t i = 0;
    while (i < txt.size()) {
        size_t e = txt.find('\n', i); if (e == Str::npos) e = txt.size();
        Str ln = txt.substr(i, e - i); i = e + 1;
        Str tr = trimS(ln);
        if (tr == line) return "такая строка уже есть\n";
        if (!multi && tr.compare(0, key.size(), key) == 0) continue;     // заменяем прежнее значение ключа
        out += ln + "\n";
    }
    out += line + "\n";
    FILE *f = fopen(worldFile().c_str(), "w"); if (!f) return "не могу записать mgg_world.txt\n";
    fputs(out.c_str(), f); fclose(f);
    return "добавлено в mgg_world.txt: " + line + "\n";
}

// текущее значение по адресам (мониторинг «глазом»): адрес \t слово hex \t int \t float \t текст
static Str hVal(const Str &tk) {
    uintptr_t a = (uintptr_t)strtoull(tk.c_str(), nullptr, 16);
    uint8_t b[24] = {0}; size_t n = sizeof b;
    if (!guarded(b, (const void *)a, n)) { n = 4; memset(b, 0, sizeof b); if (!guarded(b, (const void *)a, 4)) return tk + "\t?\t\t\t\n"; }
    uint32_t u; memcpy(&u, b, 4); float f; memcpy(&f, &u, 4); char t[48];
    Str fs; if (f == f && f > -1e9f && f < 1e9f && (u == 0 || f > 1e-4f || f < -1e-4f)) { snprintf(t, sizeof t, "%g", f); fs = t; }
    size_t k = 0; while (k < n && b[k] >= 32 && b[k] < 127) k++;
    Str tx = k >= 2 ? Str((const char *)b, k) : Str();
    snprintf(t, sizeof t, "%08X", (unsigned)u);
    return tk + "\t" + t + "\t" + std::to_string((int)u) + "\t" + fs + "\t" + tx + "\n";
}
static bool helperRoute(const Str &path, const Params &q, Str &o) {
    if (path == "hval") {
        Str l = P(q, "a"); size_t i = 0, cnt = 0; o.clear();
        while (i <= l.size() && cnt < 80) { size_t j = l.find(',', i); if (j == Str::npos) j = l.size(); Str tk = trimS(l.substr(i, j - i)); i = j + 1; if (tk.empty()) continue; cnt++; o += hVal(tk); }
        return true;
    }
    if (path == "hscanf") { o = hScanF(strtod(P(q, "v").c_str(), nullptr), strtod(P(q, "tol", "0.01").c_str(), nullptr), P(q, "all") == "1"); return true; }
    if (path == "hnextf") { o = hKeepF(0, strtod(P(q, "v").c_str(), nullptr), strtod(P(q, "tol", "0.01").c_str(), nullptr)); return true; }
    if (path == "hrel") { o = hKeepF((intptr_t)strtol(P(q, "off", "0").c_str(), nullptr, 10), strtod(P(q, "v").c_str(), nullptr), strtod(P(q, "tol", "0.01").c_str(), nullptr)); return true; }
    if (path == "hstr") { o = hStr(P(q, "s"), P(q, "all") == "1"); return true; }
    if (path == "hnear") {
        uintptr_t a = 0; if (!hexNum(q, "a", a)) { o = "#\tнужен адрес a (hex)\n"; return true; }
        o = hNear(a, decNum(q, "b", 64), decNum(q, "n", 192)); return true;
    }
    if (path == "hpath") {
        uintptr_t e = 0, a = 0; if (!hexNum(q, "e", e) || !hexNum(q, "a", a)) { o = "#\tнужны адрес объекта e и адрес поля a (hex)\n"; return true; }
        int d = (int)decNum(q, "d", 2); if (d > 4) d = 4;
        o = hPath(e, a, d, decNum(q, "n", 512)); return true;
    }
    if (path == "hptr") {
        std::lock_guard<std::mutex> lk(g_pm);
        if (P(q, "c") == "1") { g_pcancel = true; o = "останавливаю…\n"; return true; }
        if (g_prun) { o = "поиск уже идёт\n"; return true; }
        uintptr_t a = 0; if (!hexNum(q, "a", a)) { o = "нужен адрес цели a (hex)\n"; return true; }
        int d = (int)decNum(q, "d", 3); if (d < 1) d = 1; if (d > 4) d = 4;
        size_t mo = decNum(q, "o", 1024); if (mo < 16) mo = 16; if (mo > 0x4000) mo = 0x4000;
        g_prun = true; g_pcancel = false; g_pres.clear(); g_pstat = "запускаю…";
        std::thread(hPtrWorker, a, d, mo, true).detach();
        o = "поиск запущен (глубина " + std::to_string(d) + ", смещение до " + hx(mo) + ")\n"; return true;
    }
    if (path == "hptrst") {
        std::lock_guard<std::mutex> lk(g_pm);
        o = Str("#\t") + (g_prun ? "идёт" : "готово") + "\t" + g_pstat + "\n" + g_pres; return true;
    }
    if (path == "wcfgadd") { o = wCfgAdd(P(q, "line")); return true; }
    return false;
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
        return "библиотека: " + g_lib + "\nпатчей в сессии: " + std::to_string(g_patches.size()) + "\nсохранённых: " + std::to_string(g_saved.size()) +
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


// ---------------------------------------------------------------- выбор библиотеки (вкладка Lib)
static const char *libInfo(const Str &n, const Str &path) {
    struct D { const char *k; const char *d; };
    static const D t[] = {
        {"libminecraftpe.so", "ЯДРО игры Minecraft Bedrock: логика, мир, рендер, UI. Основная для патчей"},
        {"libmggpanel.so", "эта панель MGG"},
        {"libc.so", "стандартная C: память, файлы, потоки"},
        {"libm.so", "математика (sin, sqrt и т.д.)"},
        {"libdl.so", "загрузка библиотек (dlopen/dlsym)"},
        {"liblog.so", "логи Android (logcat)"},
        {"libandroid.so", "NDK Android: окно, ввод, ассеты, сенсоры"},
        {"libEGL.so", "создаёт окно и контекст для графики OpenGL ES"},
        {"libGLESv1_CM.so", "OpenGL ES 1.x (старая графика)"},
        {"libGLESv2.so", "OpenGL ES 2/3: рисование картинки игры"},
        {"libGLESv3.so", "OpenGL ES 3: рисование картинки игры"},
        {"libvulkan.so", "Vulkan: современный API графики"},
        {"libOpenSLES.so", "звук OpenSL ES"},
        {"libaaudio.so", "звук AAudio (низкая задержка)"},
        {"libfmod.so", "звуковой движок FMOD"},
        {"libfmodstudio.so", "звуковой движок FMOD Studio"},
        {"libz.so", "сжатие zlib (zip/gzip)"},
        {"libstdc++.so", "рантайм C++ системный"},
        {"libc++.so", "рантайм C++ (STL)"},
        {"libc++_shared.so", "рантайм C++ (STL), общий"},
        {"libjnigraphics.so", "работа с картинками (Bitmap) из C++"},
        {"libnativewindow.so", "окна и буферы для графики"},
        {"libmediandk.so", "кодеки и медиа"},
        {"libnativehelper.so", "мост JNI между Java и C++"},
        {"libart.so", "виртуальная машина Android (Java/Kotlin)"},
        {"libandroid_runtime.so", "ядро Android runtime"},
        {"libhwui.so", "аппаратное рисование интерфейса Android"},
        {"libbinder.so", "связь между процессами Android"},
        {"libbinder_ndk.so", "связь между процессами Android (NDK)"},
        {"libcutils.so", "системные утилиты Android"},
        {"libutils.so", "системные утилиты Android"},
        {"libssl.so", "TLS/SSL шифрование"},
        {"libcrypto.so", "криптография"},
        {"libnetd_client.so", "сеть Android"},
        {"libsync.so", "синхронизация графики"},
        {"libvndksupport.so", "поддержка vendor-библиотек"},
        {"libicuuc.so", "ICU: юникод, языки, текст"},
        {"libicui18n.so", "ICU: локали, даты, числа"},
        {"libHttpClient.Android.so", "Xbox/сетевой клиент HTTP"},
        {"libMaesdk.Android.so", "телеметрия Microsoft"},
        {"linker", "загрузчик библиотек (32-bit)"},
        {"linker64", "загрузчик библиотек (64-bit)"},
    };
    for (const D &d : t) if (n == d.k) return d.d;
    if (n.compare(0, 8, "libVkLay") == 0) return "слой отладки Vulkan";
    if (n.find("adreno") != Str::npos || n.find("GLES_mali") != Str::npos || n.find("vulkan.") != Str::npos || n.compare(0, 6, "libEGL") == 0 || n.compare(0, 7, "libGLES") == 0 || n.find("glnext") != Str::npos) return "драйвер видеокарты (GPU)";
    if (n.compare(0, 8, "libcore_") == 0 || n.compare(0, 6, "libopenjdk") == 0 || n.compare(0, 8, "libjavacore") == 0) return "Java-часть Android";
    if (path.compare(0, 8, "/system/") == 0 || path.compare(0, 6, "/apex/") == 0 || path.compare(0, 8, "/vendor/") == 0 || path.compare(0, 9, "/product/") == 0) return "системная библиотека Android";
    if (path.compare(0, 10, "/data/app/") == 0 || path.compare(0, 11, "/data/data/") == 0) return "библиотека приложения/игры";
    return "нет описания";
}

static int elfBits(const Str &path) {            // 32 / 64 / 0 (не прочитать)
    FILE *f = fopen(path.c_str(), "rb");
    if (!f) return 0;
    unsigned char h[5] = {0};
    size_t n = fread(h, 1, 5, f); fclose(f);
    if (n < 5 || h[0] != 0x7f || h[1] != 'E' || h[2] != 'L' || h[3] != 'F') return 0;
    return h[4] == 2 ? 64 : h[4] == 1 ? 32 : 0;
}

static Str dirOf(const Str &p) { size_t k = p.rfind('/'); return k == Str::npos ? Str() : p.substr(0, k); }
static bool isMcKnown(const Str &n) {
    if (n == MGG_TARGET_LIB || n.find("minecraft") != Str::npos) return true;
    static const char *pre[] = {"libfmod", "libc++_shared", "libMaesdk", "libHttpClient", "libXal", "libxal", "libpairip", "libmojang"};
    for (const char *p : pre) if (n.compare(0, strlen(p), p) == 0) return true;
    return false;
}
// 'm' — библиотеки самой игры, 'c' — кастомные (лежат в папке библиотек игры / каталоге приложения, но не из игры), 'o' — остальное (система, графика, звук)
static char libGroup(const Str &n, const Str &path, const Str &gameDir) {
    if (isMcKnown(n)) return 'm';
    Str appDir = dirOf(dirOf(gameDir));
    if (!gameDir.empty() && (dirOf(path) == gameDir || (appDir.size() > 8 && path.compare(0, appDir.size(), appDir) == 0))) return 'c';
    if (gameDir.empty() && (path.compare(0, 10, "/data/app/") == 0 || path.compare(0, 11, "/data/data/") == 0 || path.compare(0, 11, "/data/user/") == 0)) return 'c';
    return 'o';
}

struct LibEnt { Str name, path; unsigned long lo, hi; int bits; };

static std::vector<LibEnt> listLibs() {
    std::vector<LibEnt> v;
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f) return v;
    char line[1024];
    int procBits = (int)sizeof(void *) * 8;
    while (fgets(line, sizeof line, f)) {
        unsigned long s, e; char perms[8] = {0}; Str path;
        if (!mapLine(line, s, e, perms, path)) continue;
        if (path.empty() || path[0] != '/') continue;
        Str bn = mapBase(path);
        if (bn.find(".so") == Str::npos && bn != "linker" && bn != "linker64") continue;
        LibEnt *x = nullptr;
        for (LibEnt &c : v) if (c.name == bn) { x = &c; break; }
        if (!x) { v.push_back({bn, path, s, e, 0}); x = &v.back(); }
        if (s < x->lo) x->lo = s;
        if (e > x->hi) x->hi = e;
    }
    fclose(f);
    for (LibEnt &c : v) { c.bits = elfBits(c.path); if (!c.bits) c.bits = procBits; }   // не прочиталась: процесс может грузить только свою разрядность
    std::sort(v.begin(), v.end(), [](const LibEnt &a, const LibEnt &b) {
        bool am = a.name == MGG_TARGET_LIB, bm = b.name == MGG_TARGET_LIB;
        if (am != bm) return am;
        return a.name < b.name;
    });
    return v;
}

// libs: строки "имя \t бит \t размер \t описание \t выбрана"; первая строка "#\t<бит процесса>\t<выбранная>\t<бит выбранной>"
static Str libRoute(const Str &path, const Params &q) {
    std::vector<LibEnt> v = listLibs();
    int procBits = (int)sizeof(void *) * 8;
    if (path == "libsel") {
        Str n = P(q, "n");
        if (n.empty()) return "нужно имя библиотеки\n";
        const LibEnt *hit = nullptr;
        for (const LibEnt &c : v) if (c.name == n) { hit = &c; break; }
        if (!hit) return "библиотека " + n + " не найдена в процессе игры\n";
        if (n != g_lib && !g_patches.empty()) return "сначала откати патчи сессии (Lib → Патчи → Список, или Safe → Откатить ВСЁ): они записаны в «" + g_lib + "»\n";
        g_lib = n;
        Str o = "выбрана: " + n + " (" + std::to_string(hit->bits) + " бит)\nбаза " + hx(hit->lo) + ", размер " + hx(hit->hi - hit->lo) + "\n" + libInfo(n, hit->path) + "\n";
        if (n != MGG_TARGET_LIB) o += "внимание: сохранение патчей на запуски и автоприменение работают только для " MGG_TARGET_LIB "\n";
        if (hit->bits == 64) o += "внимание: дизассемблер, xref, «кто вызывает», константы и «Функция → число / NOP» рассчитаны на 32-bit Thumb; для 64-bit работают Hex, сигнатуры, строки и патчи байтами\n";
        return o;
    }
    Str o = "#\t" + std::to_string(procBits) + "\t" + g_lib + "\t";
    int sb = procBits;
    for (const LibEnt &c : v) if (c.name == g_lib) sb = c.bits;
    o += std::to_string(sb) + "\n";
    Str gameDir; for (const LibEnt &c : v) if (c.name == MGG_TARGET_LIB) gameDir = dirOf(c.path);
    for (const LibEnt &c : v)
        o += c.name + "\t" + std::to_string(c.bits) + "\t" + hx(c.hi - c.lo) + "\t" + libInfo(c.name, c.path) + "\t" + (c.name == g_lib ? "1" : "0") + "\t" + libGroup(c.name, c.path, gameDir) + "\t1\n";
    if (!gameDir.empty()) {                                   // .so из папки игры, которые сейчас не загружены (видны, но выбрать нельзя)
        DIR *d = opendir(gameDir.c_str());
        if (d) {
            std::vector<Str> extra;
            while (struct dirent *e = readdir(d)) {
                Str n = e->d_name; if (n.size() < 4 || n.compare(n.size() - 3, 3, ".so") != 0) continue;
                bool loaded = false; for (const LibEnt &c : v) if (c.name == n) { loaded = true; break; }
                if (!loaded) extra.push_back(n);
            }
            closedir(d); std::sort(extra.begin(), extra.end());
            for (const Str &n : extra) {
                Str fp = gameDir + "/" + n; struct stat st; unsigned long sz = stat(fp.c_str(), &st) == 0 ? (unsigned long)st.st_size : 0;
                int b = elfBits(fp);
                o += n + "\t" + std::to_string(b ? b : procBits) + "\t" + hx(sz) + "\tне загружена в процесс\t0\t" + libGroup(n, fp, gameDir) + "\t0\n";
            }
        }
    }
    return o;
}

// ---------------------------------------------------------------- Dex: строки из classes.dex … classes8.dex внутри APK
// APK — это zip. Читаем центральный каталог, достаём classesN.dex (хранится как есть или сжат deflate), разбираем таблицу строк dex.
// Свой inflate (по мотивам puff.c, public domain), чтобы не зависеть от линковки с zlib.
struct InfState { const uint8_t *in; size_t inlen, incnt; long bitbuf; int bitcnt; uint8_t *out; size_t outlen, outcnt; bool err; };
struct InfHuff { short *count; short *symbol; };
static int infBits(InfState *s, int need) {
    long val = s->bitbuf;
    while (s->bitcnt < need) {
        if (s->incnt == s->inlen) { s->err = true; return 0; }
        val |= (long)(s->in[s->incnt++]) << s->bitcnt;
        s->bitcnt += 8;
    }
    s->bitbuf = (long)(val >> need); s->bitcnt -= need;
    return (int)(val & ((1L << need) - 1));
}
static int infDecode(InfState *s, const InfHuff *h) {
    int code = 0, first = 0, index = 0;
    for (int len = 1; len <= 15; len++) {
        code |= infBits(s, 1);
        if (s->err) return -1;
        int count = h->count[len];
        if (code - count < first) return h->symbol[index + (code - first)];
        index += count; first += count; first <<= 1; code <<= 1;
    }
    return -10;
}
static int infConstruct(InfHuff *h, const short *length, int n) {
    short offs[16]; int left = 1;
    for (int len = 0; len <= 15; len++) h->count[len] = 0;
    for (int sy = 0; sy < n; sy++) h->count[length[sy]]++;
    if (h->count[0] == n) return 0;
    for (int len = 1; len <= 15; len++) { left <<= 1; left -= h->count[len]; if (left < 0) return left; }
    offs[1] = 0;
    for (int len = 1; len < 15; len++) offs[len + 1] = offs[len] + h->count[len];
    for (int sy = 0; sy < n; sy++) if (length[sy] != 0) h->symbol[offs[length[sy]]++] = (short)sy;
    return left;
}
static int infCodes(InfState *s, const InfHuff *lc, const InfHuff *dc) {
    static const short lens[29] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258};
    static const short lext[29] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};
    static const short dists[30] = {1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577};
    static const short dext[30] = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13};
    int sy;
    do {
        sy = infDecode(s, lc);
        if (sy < 0) return sy;
        if (sy < 256) { if (s->outcnt == s->outlen) return 1; s->out[s->outcnt++] = (uint8_t)sy; }
        else if (sy > 256) {
            sy -= 257; if (sy >= 29) return -10;
            int len = lens[sy] + infBits(s, lext[sy]);
            sy = infDecode(s, dc); if (sy < 0) return sy;
            if (sy >= 30) return -10;
            size_t dist = (size_t)dists[sy] + infBits(s, dext[sy]);
            if (s->err) return -1;
            if (dist > s->outcnt) return -11;
            if (s->outcnt + len > s->outlen) return 1;
            while (len--) { s->out[s->outcnt] = s->out[s->outcnt - dist]; s->outcnt++; }
        }
    } while (sy != 256);
    return 0;
}
static int infStored(InfState *s) {
    s->bitbuf = 0; s->bitcnt = 0;
    if (s->incnt + 4 > s->inlen) return 2;
    unsigned len = s->in[s->incnt++]; len |= (unsigned)s->in[s->incnt++] << 8;
    unsigned nl = s->in[s->incnt++]; nl |= (unsigned)s->in[s->incnt++] << 8;
    if (nl != (~len & 0xFFFF)) return -2;
    if (s->incnt + len > s->inlen) return 2;
    if (s->outcnt + len > s->outlen) return 1;
    while (len--) s->out[s->outcnt++] = s->in[s->incnt++];
    return 0;
}
static int infFixed(InfState *s) {
    static bool built = false; static short lc[16], ls[288], dcn[16], ds[30]; static InfHuff lh = {lc, ls}, dh = {dcn, ds};
    if (!built) {
        short l[288]; int sy;
        for (sy = 0; sy < 144; sy++) l[sy] = 8;
        for (; sy < 256; sy++) l[sy] = 9;
        for (; sy < 280; sy++) l[sy] = 7;
        for (; sy < 288; sy++) l[sy] = 8;
        infConstruct(&lh, l, 288);
        for (sy = 0; sy < 30; sy++) l[sy] = 5;
        infConstruct(&dh, l, 30);
        built = true;
    }
    return infCodes(s, &lh, &dh);
}
static int infDynamic(InfState *s) {
    static const short order[19] = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};
    short lengths[320], lc[16], ls[288], dcn[16], ds[30]; InfHuff lh = {lc, ls}, dh = {dcn, ds};
    int nlen = infBits(s, 5) + 257, ndist = infBits(s, 5) + 1, ncode = infBits(s, 4) + 4;
    if (s->err) return -1;
    if (nlen > 286 || ndist > 30) return -3;
    int index;
    for (index = 0; index < ncode; index++) lengths[order[index]] = (short)infBits(s, 3);
    for (; index < 19; index++) lengths[order[index]] = 0;
    if (infConstruct(&lh, lengths, 19) != 0) return -4;
    index = 0;
    while (index < nlen + ndist) {
        int sy = infDecode(s, &lh); if (sy < 0) return sy;
        if (sy < 16) lengths[index++] = (short)sy;
        else {
            int len = 0, rep;
            if (sy == 16) { if (index == 0) return -5; len = lengths[index - 1]; rep = 3 + infBits(s, 2); }
            else if (sy == 17) rep = 3 + infBits(s, 3);
            else rep = 11 + infBits(s, 7);
            if (index + rep > nlen + ndist) return -6;
            while (rep--) lengths[index++] = (short)len;
        }
    }
    if (s->err) return -1;
    if (lengths[256] == 0) return -9;
    int err = infConstruct(&lh, lengths, nlen);
    if (err && (err < 0 || nlen != lh.count[0] + lh.count[1])) return -7;
    err = infConstruct(&dh, lengths + nlen, ndist);
    if (err && (err < 0 || ndist != dh.count[0] + dh.count[1])) return -8;
    return infCodes(s, &lh, &dh);
}
static bool inflateRaw(const uint8_t *in, size_t inlen, uint8_t *out, size_t outlen) {
    InfState s = {in, inlen, 0, 0, 0, out, outlen, 0, false};
    int last;
    do {
        last = infBits(&s, 1); int type = infBits(&s, 2);
        if (s.err) return false;
        int err = type == 0 ? infStored(&s) : type == 1 ? infFixed(&s) : type == 2 ? infDynamic(&s) : -1;
        if (err) return false;
    } while (!last);
    return s.outcnt == outlen;
}

static uint32_t zr16(const uint8_t *p) { return p[0] | (p[1] << 8); }
static uint32_t zr32(const uint8_t *p) { return p[0] | (p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24); }
struct ZEnt { Str name; uint32_t method, csize, usize, lho; };

static bool zipList(FILE *f, std::vector<ZEnt> &out) {
    if (fseek(f, 0, SEEK_END) != 0) return false;
    long fsz = ftell(f); if (fsz < 22) return false;
    long tail = fsz < 65557 ? fsz : 65557;
    std::vector<uint8_t> b(tail);
    if (fseek(f, fsz - tail, SEEK_SET) != 0 || fread(b.data(), 1, tail, f) != (size_t)tail) return false;
    long e = -1;
    for (long i = tail - 22; i >= 0; i--) if (zr32(&b[i]) == 0x06054b50) { e = i; break; }
    if (e < 0) return false;
    uint32_t cdSize = zr32(&b[e + 12]), cdOff = zr32(&b[e + 16]); uint32_t total = zr16(&b[e + 10]);
    if (cdOff == 0xFFFFFFFFu || cdSize > 64u * 1024 * 1024 || (long)cdOff + (long)cdSize > fsz) return false;
    std::vector<uint8_t> cd(cdSize);
    if (fseek(f, cdOff, SEEK_SET) != 0 || fread(cd.data(), 1, cdSize, f) != cdSize) return false;
    size_t p = 0;
    for (uint32_t i = 0; i < total && p + 46 <= cd.size(); i++) {
        if (zr32(&cd[p]) != 0x02014b50) break;
        ZEnt z; z.method = zr16(&cd[p + 10]); z.csize = zr32(&cd[p + 20]); z.usize = zr32(&cd[p + 24]);
        uint32_t nl = zr16(&cd[p + 28]), el = zr16(&cd[p + 30]), cl = zr16(&cd[p + 32]); z.lho = zr32(&cd[p + 42]);
        if (p + 46 + nl > cd.size()) break;
        z.name.assign((const char *)&cd[p + 46], nl);
        out.push_back(z); p += 46 + nl + el + cl;
    }
    return !out.empty();
}
static bool zipRead(FILE *f, const ZEnt &z, std::vector<uint8_t> &out) {
    if (z.usize > 96u * 1024 * 1024 || z.csize > 96u * 1024 * 1024) return false;
    uint8_t h[30];
    if (fseek(f, z.lho, SEEK_SET) != 0 || fread(h, 1, 30, f) != 30 || zr32(h) != 0x04034b50) return false;
    long data = (long)z.lho + 30 + zr16(h + 26) + zr16(h + 28);
    std::vector<uint8_t> c(z.csize);
    if (fseek(f, data, SEEK_SET) != 0 || fread(c.data(), 1, z.csize, f) != z.csize) return false;
    out.assign(z.usize, 0);
    if (z.method == 0) { if (z.csize != z.usize) return false; memcpy(out.data(), c.data(), z.usize); return true; }
    if (z.method == 8) return inflateRaw(c.data(), c.size(), out.data(), out.size());
    return false;
}

static bool dexNameOk(const Str &n) {                              // classes.dex, classes2.dex … classes99.dex в корне
    if (n.compare(0, 7, "classes") != 0 || n.size() < 11 || n.compare(n.size() - 4, 4, ".dex") != 0) return false;
    for (size_t i = 7; i + 4 < n.size(); i++) if (n[i] < '0' || n[i] > '9') return false;
    return true;
}
static int dexNum(const Str &n) { return n.size() == 11 ? 1 : atoi(n.substr(7, n.size() - 11).c_str()); }

// число строк и i-я строка таблицы строк dex
static bool dexHdr(const std::vector<uint8_t> &d, uint32_t &cnt, uint32_t &off) {
    if (d.size() < 0x70 || memcmp(d.data(), "dex\n", 4) != 0) return false;
    cnt = zr32(&d[0x38]); off = zr32(&d[0x3C]);
    return (uint64_t)off + (uint64_t)cnt * 4 <= d.size();
}
static bool dexStr(const std::vector<uint8_t> &d, uint32_t off, uint32_t i, size_t &st, size_t &len) {
    uint32_t so = zr32(&d[off + 4 * (size_t)i]); if (so >= d.size()) return false;
    size_t p = so; while (p < d.size() && (d[p] & 0x80)) p++;
    p++; if (p >= d.size()) return false;
    const uint8_t *z = (const uint8_t *)memchr(&d[p], 0, d.size() - p);
    st = p; len = z ? (size_t)(z - &d[p]) : d.size() - p; return true;
}
static Str dexClean(const uint8_t *s, size_t n) {
    if (n > 200) n = 200; Str o((const char *)s, n);
    for (char &c : o) if ((unsigned char)c < 32) c = '?';
    return o;
}

// APK игры: ищем в /proc/self/maps пути на .apk, затем рядом с libminecraftpe.so (…/lib/<abi>/lib.so → …/base.apk)
static std::vector<Str> dexApks() {
    std::vector<Str> v;
    auto add = [&](const Str &p) { if (!p.empty() && std::find(v.begin(), v.end(), p) == v.end() && access(p.c_str(), R_OK) == 0) v.push_back(p); };
    FILE *f = fopen("/proc/self/maps", "r");
    if (f) {
        char line[1024];
        while (fgets(line, sizeof line, f)) {
            unsigned long s, e; char perms[8] = {0}; Str path;
            if (!mapLine(line, s, e, perms, path) || path.empty() || path[0] != '/') continue;
            size_t k = path.find(".apk"); if (k == Str::npos) continue;
            Str p = path.substr(0, k + 4);
            if (p.find("base.apk") != Str::npos) add(p);
        }
        rewind(f);
        while (fgets(line, sizeof line, f)) {
            unsigned long s, e; char perms[8] = {0}; Str path;
            if (!mapLine(line, s, e, perms, path) || path.empty() || path[0] != '/') continue;
            size_t k = path.find(".apk"); if (k != Str::npos) add(path.substr(0, k + 4));
            if (path.size() > 4 && path.find("/lib/") != Str::npos && mapBase(path) == MGG_TARGET_LIB) {
                Str d = path.substr(0, path.rfind('/')); d = d.substr(0, d.rfind('/')); d = d.substr(0, d.rfind('/'));
                add(d + "/base.apk");
            }
        }
        fclose(f);
    }
    return v;
}
static Str g_dexApk; static std::vector<ZEnt> g_dexEnt;
static bool dexOpen(Str &err) {
    if (!g_dexEnt.empty()) return true;
    std::vector<Str> aks = dexApks();
    if (aks.empty()) { err = "APK игры не найден (нужен base.apk рядом с библиотеками)"; return false; }
    for (const Str &a : aks) {
        FILE *f = fopen(a.c_str(), "rb"); if (!f) continue;
        std::vector<ZEnt> all, dx;
        if (zipList(f, all)) for (const ZEnt &z : all) if (dexNameOk(z.name)) dx.push_back(z);
        fclose(f);
        if (!dx.empty()) { std::sort(dx.begin(), dx.end(), [](const ZEnt &x, const ZEnt &y) { return dexNum(x.name) < dexNum(y.name); }); g_dexApk = a; g_dexEnt = dx; return true; }
    }
    err = "в APK нет classes*.dex (или файл не читается)"; return false;
}
static Str g_dcName; static std::vector<uint8_t> g_dcData;
static bool dexLoad(const Str &name, std::vector<uint8_t> &out) {
    if (g_dcName == name) { out = g_dcData; return true; }
    for (const ZEnt &z : g_dexEnt) if (z.name == name) {
        FILE *f = fopen(g_dexApk.c_str(), "rb"); if (!f) return false;
        bool ok = zipRead(f, z, out); fclose(f);
        if (ok) { g_dcName = name; g_dcData = out; }
        return ok;
    }
    return false;
}

static bool dexMatch(const uint8_t *s, size_t n, const Str &nd, int mode, bool ci) {   // mode: 0 содержит, 1 начинается, 2 точно
    size_t m = nd.size(); if (m > n) return false;
    auto eq = [&](size_t at) { for (size_t k = 0; k < m; k++) { unsigned char a = s[at + k], b = (unsigned char)nd[k]; if (ci) { if (a >= 'A' && a <= 'Z') a += 32; if (b >= 'A' && b <= 'Z') b += 32; } if (a != b) return false; } return true; };
    if (mode == 2) return n == m && eq(0);
    if (mode == 1) return eq(0);
    for (size_t i = 0; i + m <= n; i++) if (eq(i)) return true;
    return false;
}

// dexlist | dexfind (q, f = classesN.dex или all, m = sub|start|exact, ci = 1) | dexctx (f, i, n)
static Str dexRoute(const Str &path, const Params &q) {
    Str err;
    if (!dexOpen(err)) return "#\t" + err + "\n";
    if (path == "dexlist") {
        Str o = "#\t" + g_dexApk + "\n";
        for (const ZEnt &z : g_dexEnt) o += z.name + "\t" + std::to_string(z.usize) + "\n";
        return o;
    }
    if (path == "dexctx") {
        Str f = P(q, "f"); size_t idx = decNum(q, "i", 0), n = decNum(q, "n", 6);
        std::vector<uint8_t> d; uint32_t cnt, off;
        if (!dexLoad(f, d) || !dexHdr(d, cnt, off)) return "не открыл " + f + "\n";
        Str o = f + ": строк " + std::to_string(cnt) + "\n";
        size_t lo = idx > n ? idx - n : 0;
        for (size_t i = lo; i <= idx + n && i < cnt; i++) {
            size_t st, len; if (!dexStr(d, off, (uint32_t)i, st, len)) continue;
            o += std::string(i == idx ? "> " : "  ") + "#" + std::to_string(i) + "  " + dexClean(&d[st], len) + "\n";
        }
        return o;
    }
    if (path == "dexfind") {
        Str nd = P(q, "q"); if (nd.empty()) return "#\tвведи, что искать\n";
        Str want = P(q, "f", "all"); Str m = P(q, "m", "sub"); int mode = m == "exact" ? 2 : m == "start" ? 1 : 0; bool ci = P(q, "ci", "1") == "1";
        Str o; size_t cnt = 0, files = 0; const size_t CAP = 3000;
        for (const ZEnt &z : g_dexEnt) {
            if (want != "all" && want != z.name) continue;
            std::vector<uint8_t> d; uint32_t n, off;
            if (!dexLoad(z.name, d) || !dexHdr(d, n, off)) { o += "#\tне открыл " + z.name + "\n"; continue; }
            files++;
            for (uint32_t i = 0; i < n && cnt < CAP; i++) {
                size_t st, len; if (!dexStr(d, off, i, st, len)) continue;
                if (!dexMatch(&d[st], len, nd, mode, ci)) continue;
                o += z.name + "\t" + std::to_string(i) + "\t" + dexClean(&d[st], len) + "\n"; cnt++;
            }
        }
        return "#\tсовпадений: " + std::to_string(cnt) + (cnt >= CAP ? " (лимит, уточни запрос)" : "") + ", файлов dex: " + std::to_string(files) + "\n" + o;
    }
    return "неизвестный маршрут\n";
}

// ---------------------------------------------------------------- маршруты
static const char *kPage = R"MGG(<!doctype html><html><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1,maximum-scale=1"><title>MGG</title>
<style>
:root{--bg:#12141c;--card:#1a1d29;--card2:#232736;--line:#2b3043;--tx:#e9eaf0;--dim:#8d92a6;--ac:#85775a;--acTx:#fff;--hl:#f0b429;--ok:#4cc38a;--er:#ff6b6b;--wr:#f0c040;--cf:#f0c040;--ci:#6cb6ff;--cl:#c792ea;--cp:#4dd0e1;--cs:#ffab70;--cz:#6b7088;--r:10px}
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
#top{position:sticky;top:0;z-index:5;background:var(--bg);padding:6px 8px 4px;display:flex;gap:6px;align-items:stretch}
.tb{display:flex;flex-direction:column;gap:5px;width:40px;flex:none}
.tb button{margin:0;padding:0;flex:1;width:100%}
#out{white-space:pre-wrap;word-break:break-all;background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:6px 9px;margin:0;flex:1;min-width:0;max-height:22vh;min-height:40px;overflow:auto;font:11px/1.35 ui-monospace,monospace;color:var(--tx)}
#out.big{max-height:60vh}
#out .ok{color:var(--ok)}#out .er{color:var(--er)}#out .wr{color:var(--wr)}
#out .ad{color:var(--cp)}#out .st{color:var(--cs)}#out .dm{color:var(--cz)}
#out .m1{color:var(--cl)}#out .m2{color:var(--cs)}#out .m3{color:var(--cp)}#out .m4{color:var(--ci)}#out .m5{color:var(--cf)}
#out div{min-height:1em}
.lgd{display:flex;flex-wrap:wrap;gap:4px 10px;font-size:10px;margin:4px 0}
.lgd i{font-style:normal;font-weight:600}
.row{display:flex;gap:5px;margin-top:5px}.row>*{flex:1;min-width:0}
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
button{font:inherit;color:var(--acTx);border:0;border-radius:var(--r);padding:8px 9px;margin:3px 0;background:var(--ac);width:100%;min-width:0;display:flex;align-items:center;justify-content:center;gap:7px;text-align:center;line-height:1.15;white-space:normal;overflow-wrap:anywhere}
button:active{filter:brightness(1.25)}button.s{background:var(--card2);border:1px solid var(--line);color:var(--tx)}
button.d{background:#8a3a40}button.g{background:#3f7a63}
.grid2,.grid3{display:grid;gap:5px}.grid2{grid-template-columns:repeat(2,minmax(0,1fr))}.grid3{grid-template-columns:repeat(3,minmax(0,1fr))}
.grid2>*,.grid3>*{min-width:0}
.grid2 button,.grid3 button{margin:0;height:100%}
.grid2 button{padding:8px 6px;font-size:12px}
.grid3 button{flex-direction:column;gap:3px;padding:8px 3px;font-size:11px}
.fn{display:flex;align-items:center;gap:8px;background:var(--ac);color:var(--acTx);border-radius:var(--r);padding:9px 10px;margin:5px 0}
.fn .nm{flex:1;font-weight:600}.fn .sub{opacity:.7;font-size:10px;font-weight:400}
.sw{width:38px;height:21px;border-radius:999px;background:rgba(0,0,0,.35);flex:none;position:relative}
.sw::after{content:"";position:absolute;top:2px;left:2px;width:17px;height:17px;border-radius:50%;background:#fff;transition:transform .15s}
.sw.on{background:var(--hl)}.sw.on::after{transform:translateX(17px);background:#22240f}
.sw.bad{background:#8a3a40}.sw.bad::after{background:#ffd9db}
.sw.mid{background:#6b6450}.sw.mid::after{background:#fff3cf}
.hr{margin-left:auto;display:flex;gap:4px;align-items:center;text-transform:none}.mini{width:auto;padding:3px 6px;margin:0;font-size:11px}.ib{width:28px;height:26px;padding:0;margin:0;border-radius:8px}
.fg{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:4px}.fg>div{grid-column:1/-1}
.fn.c{padding:5px 8px;margin:0;gap:6px;font-size:12px;border-radius:8px}.fn.c .nm{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;line-height:1.2}.fn.c .sub{font-size:9px;overflow:hidden;text-overflow:ellipsis}
.fn.c .sw{width:28px;height:16px}.fn.c .sw::after{width:12px;height:12px;top:2px;left:2px}.fn.c .sw.on::after{transform:translateX(12px)}
.fg>.fn.c{grid-column:auto}
.zr{display:flex;gap:4px;align-items:center;margin-top:4px}.zr b{font-size:10px;color:var(--dim);font-weight:600}.zr select{flex:1;padding:4px 6px;margin:0;min-width:0}
.tag{font-size:9px;background:rgba(0,0,0,.3);border-radius:5px;padding:1px 5px;margin-left:6px}
small{color:var(--dim);display:block;margin-top:4px}
.pre{display:flex;gap:5px;flex-wrap:wrap}.pre button{width:auto;flex:1 1 30%;min-width:0}
.pre.sm button{flex:1 1 20%;padding:6px 3px;font-size:11px;margin:0}
.lb{font-weight:600;font-size:10px;color:var(--dim);margin:7px 0 3px;display:block}
#ll .fn{cursor:pointer}
.seg{display:flex;gap:4px;background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:3px;margin:7px 0}
.seg button{margin:0;flex:1;background:none;color:var(--dim);padding:7px 4px;font-weight:600}
.seg button.on{background:var(--ac);color:var(--acTx)}
.qv{background:var(--card2);border:1px solid var(--line);border-radius:var(--r);padding:6px;margin:4px 0 6px}
.qv .seg{margin:0 0 6px;padding:2px}.qv .seg button{padding:5px 2px;font-size:11px}
.chips{display:flex;flex-wrap:wrap;gap:4px;align-items:center}
.chips button{width:auto;flex:none;margin:0;padding:5px 9px;font-size:11px}
.chips b{font-size:10px;color:var(--dim);margin:0 1px 0 5px;font-weight:600}
.rg{display:flex;align-items:center;gap:8px}.rg b{min-width:34px;text-align:right}
.kv{display:flex;align-items:center;gap:8px;padding:7px 2px;border-bottom:1px solid var(--line)}
.kv:last-child{border-bottom:0}.kv span{color:var(--dim);flex:1}.kv b{font:600 13px ui-monospace,monospace;text-align:right;word-break:break-all}
.kv b.no{color:var(--dim);font-weight:400}
.kv.wrap{flex-wrap:wrap}.lv{flex-basis:100%;font:11px/1.3 ui-monospace,monospace;color:var(--ok);padding:0 2px 2px}
.kv button{width:28px;height:28px;padding:0;margin:0;flex:none;border-radius:8px}
#pcf{position:fixed;left:0;top:0;width:100%;height:100%;border:0;z-index:50;display:none;background:#0d0f14}
</style></head><body>
<svg style="position:absolute;width:0;height:0" aria-hidden="true"><defs>
<symbol id="i-bolt" viewBox="0 0 24 24"><path class="fi" d="M13 2 4 14h6l-1 8 9-12h-6l1-8z"/></symbol>
<symbol id="i-mem" viewBox="0 0 24 24"><rect x="3" y="6" width="18" height="10" rx="1.5"/><path d="M7 10h2M11 10h2M15 10h2M6 16v3M10 16v3M14 16v3M18 16v3"/></symbol>
<symbol id="i-lib" viewBox="0 0 24 24"><rect x="6" y="6" width="12" height="12" rx="2"/><path d="M9 2v4M15 2v4M9 18v4M15 18v4M2 9h4M2 15h4M18 9h4M18 15h4"/></symbol>
<symbol id="i-file" viewBox="0 0 24 24"><path d="M3 6a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V6z"/></symbol>
<symbol id="i-safe" viewBox="0 0 24 24"><path d="M12 2 4 5v6c0 5 3.5 8.5 8 11 4.5-2.5 8-6 8-11V5l-8-3z"/></symbol>
<symbol id="i-palette" viewBox="0 0 24 24"><path d="M12 3a9 8 0 1 0 0 16c1.5 0 2-1 2-2s-.5-1.5-.5-2.5S14 13 15 13h2a4 4 0 0 0 4-4c0-3.5-4-6-9-6z"/><circle class="fi" cx="8" cy="12" r="1.3"/><circle class="fi" cx="9.5" cy="8" r="1.3"/><circle class="fi" cx="14.5" cy="8" r="1.3"/></symbol>
<symbol id="i-copy" viewBox="0 0 24 24"><rect x="8" y="8" width="12" height="12" rx="2"/><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"/></symbol>
<symbol id="i-expand" viewBox="0 0 24 24"><path d="M9 3H3v6M15 21h6v-6M21 3h-6v6M3 21h6v-6"/></symbol>
<symbol id="i-search" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><path d="M21 21l-4.3-4.3"/></symbol>
<symbol id="i-up" viewBox="0 0 24 24"><path d="M12 19V5M5 12l7-7 7 7"/></symbol>
<symbol id="i-down" viewBox="0 0 24 24"><path d="M12 5v14M5 12l7 7 7-7"/></symbol>
<symbol id="i-eq" viewBox="0 0 24 24"><path d="M5 9h14M5 15h14"/></symbol>
<symbol id="i-list" viewBox="0 0 24 24"><path d="M8 6h13M8 12h13M8 18h13M3 6h.01M3 12h.01M3 18h.01"/></symbol>
<symbol id="i-reset" viewBox="0 0 24 24"><path d="M3 12a9 9 0 1 0 3-6.7"/><path d="M3 3v5h5"/></symbol>
<symbol id="i-save" viewBox="0 0 24 24"><path d="M5 4h11l3 3v13H5z"/><path d="M8 4v6h8V4M8 14h8v6H8z"/></symbol>
<symbol id="i-snow" viewBox="0 0 24 24"><path d="M12 2v20M4.5 6.5l15 11M19.5 6.5l-15 11"/></symbol>
<symbol id="i-stop" viewBox="0 0 24 24"><rect x="6" y="6" width="12" height="12" rx="1.5"/></symbol>
<symbol id="i-link" viewBox="0 0 24 24"><path d="M10 14a4 4 0 0 0 6 0l3-3a4 4 0 0 0-6-6l-1.5 1.5"/><path d="M14 10a4 4 0 0 0-6 0l-3 3a4 4 0 0 0 6 6l1.5-1.5"/></symbol>
<symbol id="i-start" viewBox="0 0 24 24"><path d="M8 5l12 7-12 7z"/></symbol>
<symbol id="i-hex" viewBox="0 0 24 24"><path d="M9 3 3 7v10l6 4 6-4V7zM15 3l6 4v10l-6 4"/></symbol>
<symbol id="i-code" viewBox="0 0 24 24"><path d="M9 6 3 12l6 6M15 6l6 6-6 6"/></symbol>
<symbol id="i-undo" viewBox="0 0 24 24"><path d="M3 10h9a6 6 0 0 1 0 12h-3"/><path d="M8 5 3 10l5 5"/></symbol>
<symbol id="i-trash" viewBox="0 0 24 24"><path d="M4 7h16M9 7V5a2 2 0 0 1 2-2h2a2 2 0 0 1 2 2v2M6 7l1 13a2 2 0 0 0 2 2h6a2 2 0 0 0 2-2l1-13"/></symbol>
<symbol id="i-plug" viewBox="0 0 24 24"><path d="M9 2v6M15 2v6M6 8h12l-1 5a5 5 0 0 1-10 0z"/><path d="M12 17v5"/></symbol>
<symbol id="i-unlock" viewBox="0 0 24 24"><rect x="5" y="11" width="14" height="9" rx="2"/><path d="M8 11V7a4 4 0 0 1 7-2.6"/></symbol>
<symbol id="i-info" viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 11v5M12 8h.01"/></symbol>
<symbol id="i-plus" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></symbol>
<symbol id="i-flag" viewBox="0 0 24 24"><path d="M5 3v18M5 4h11l-2 4 2 4H5"/></symbol>
<symbol id="i-sun" viewBox="0 0 24 24"><path d="M12 5v2M12 17v2M5 12H3M21 12h-2M6.3 6.3l1.4 1.4M16.3 16.3l1.4 1.4M6.3 17.7l1.4-1.4M16.3 7.7l1.4-1.4"/><circle cx="12" cy="12" r="4"/></symbol>
<symbol id="i-look" viewBox="0 0 24 24"><path d="M2 12s3.6-7 10-7 10 7 10 7-3.6 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3.2"/><circle cx="12" cy="12" r=".9" class="fi"/></symbol>
<symbol id="i-dex" viewBox="0 0 24 24"><path d="M9 4C6 4 7.5 9 4 12c3.5 3 2 8 5 8M15 4c3 0 1.5 5 5 8-3.5 3-2 8-5 8"/></symbol>
<symbol id="i-globe" viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M3 12h18M12 3c3 3 3 15 0 18M12 3c-3 3-3 15 0 18"/></symbol>
<symbol id="i-eye" viewBox="0 0 24 24"><path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7-10-7-10-7z"/><circle cx="12" cy="12" r="3"/></symbol>
</defs></svg>
<div id=top><pre id=out>MGG готов. Открой вкладку «Функции».</pre>
<div class=tb><button class=s title="Копировать" onclick="cp()"><svg class=ic><use href="#i-copy"/></svg></button><button class=s title="Размер" onclick="document.getElementById('out').classList.toggle('big')"><svg class=ic><use href="#i-expand"/></svg></button></div></div>

<div class=pg id=pn>
<div class=seg id=fseg><button class=on onclick="fnTab('g')">Global</button><button onclick="fnTab('l')">Local world</button></div>
<div id=fgl>
<div id=sl></div>
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Функции<span class=hr><select id=fk2 class=mini><option value=0>сейчас</option><option value=1>запомнить</option></select><button class="s ib" title="Обновить" onclick="fnl()"><svg class=ic><use href="#i-reset"/></svg></button></span></h3><div id=fl class=fg>…</div></div>
</div>
<div id=fll style="display:none">
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Multiple destroy</h3>
<div class="fn c" onclick="azGo()"><div class=nm>Multiple destroy<div class=sub id=azs>выключено</div></div><div class=sw id=azsw></div></div>
<div class=zr><b>Ш</b><select id=azw><option>1</option><option>2</option><option selected>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option></select><b>В</b><select id=azh><option>1</option><option>2</option><option>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option></select><b>Г</b><select id=azd><option>1</option><option>2</option><option>3</option><option>4</option><option>5</option></select></div>
<div class="pre sm" style="margin-top:4px"><button class=s onclick="azP(1,1,1)">1x1</button><button class=s onclick="azP(3,2,1)">3x2</button><button class=s onclick="azP(3,3,1)">3x3</button><button class=s onclick="azP(5,5,1)">5x5</button><button class=s onclick="azP(3,3,3)">3x3x3</button></div>
<small>Работает только в локальном мире. Ш × В в плоскости грани, Г вглубь. Адрес destroyBlock ищется сам.</small></div>
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Multiple place</h3>
<div class="fn c" onclick="plGo()"><div class=nm>Multiple place<div class=sub id=pls>выключено</div></div><div class=sw id=plsw></div></div>
<div class=zr><b>Ш</b><select id=plw><option>1</option><option>2</option><option selected>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option></select><b>В</b><select id=plh><option>1</option><option>2</option><option selected>3</option><option>4</option><option>5</option><option>6</option><option>7</option><option>8</option><option>9</option></select></div>
<div class="pre sm" style="margin-top:4px"><button class=s onclick="plP(3,1)">3x1</button><button class=s onclick="plP(3,3)">3x3</button><button class=s onclick="plP(5,5)">5x5</button><button class=s onclick="plP(9,9)">9x9</button></div>
<details style="margin-top:6px"><summary style="cursor:pointer;color:var(--dim);font-size:11px">Если не ставит</summary>
<div class=row><b style="align-self:center">слот</b><select id=plsl><option>6</option><option selected>7</option><option>8</option></select></div>
<small>Слот vtable GameMode: 7 = buildBlock. Если блоки не ставятся, выключи, поменяй слот на 6 или 8 и включи снова.</small></details>
<small>Только локальный мир. Ставит пластину Ш × В вокруг блока, на который поставил, в плоскости грани. Блоки нужны в запасе (в выживании тратятся). Глубины нет: слой ставится не раньше, чем появится опора.</small></div>
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Заготовки (хуки)</h3>
<div id=prl><small>…</small></div>
<div class=grid3 style="margin-top:6px"><button class=s onclick="call('gmslots',{n:40})">Слоты GameMode</button><button class=s onclick="call('hooks',{})">Список хуков</button><button class=s onclick="call('hooksave',{})">Запомнить хуки</button></div>
<small>Включить = поставить хук в режиме «вернуть значение». Где слот известен (Reach), адрес находится сам, остальным нужен адрес функции: впиши hex и включи. Значение: float или целое, как в строке. Только одиночная игра.</small></div>
<div class=card><h3><svg class=ic><use href="#i-search"/></svg>Лимиты (константы)</h3>
<div class=row><input id=lf1 value=30 inputmode=decimal><input id=lf2 value=110 inputmode=decimal><select id=lt style="flex:.6"><option value=f>float</option><option value=i>int</option></select></div>
<button onclick="call('fpair',{f1:v('lf1'),f2:v('lf2'),t:v('lt')})"><svg class=ic><use href="#i-search"/></svg>Найти пару констант</button>
<div class=row style="margin-top:6px"><input id=la placeholder="адрес (hex)"><input id=ln placeholder="новое"></div>
<div class=grid3><button onclick="call('fset',{a:v('la'),f:v('ln'),t:v('lt'),k:0})">Применить</button><button class=s onclick="call('fset',{a:v('la'),f:v('ln'),t:v('lt'),k:1})">+ запомнить</button><button class=d onclick="call('undo',{a:v('la')})">Откат</button></div>
<small>По умолчанию ищет зажим FOV 30 и 110 (рядом лежащие константы). Для чанков: тип int и числа из твоих находок (например 5 и 13). Литерал в коде общий для всех мест, где он читается: смотри, что сломалось, и откатывай.</small></div>
</div>
</div>
<div class=pg id=pm style="display:none">
<div class=card><h3><svg class=ic><use href="#i-search"/></svg>Найти оффсет</h3>
<div class=row><input id=ov placeholder="значение сейчас (например 20)" inputmode=decimal><select id=ot style="flex:.6"><option value=f>float</option><option value=i>int</option></select></div>
<button id=ob1 onclick="ofStart()"><svg class=ic><use href="#i-search"/></svg>Найти оффсет</button>
<div id=ostep style="display:none">
<div class=grid2><button onclick="ofNext()">Изменил → сузить</button><button class=s onclick="ofSame()">Не менял → отсеять шум</button></div></div>
<div class=grid2 style="margin-top:5px"><button class=s onclick="ofChains()">Цепочки заново</button><button class=d onclick="ofReset()">Сброс</button></div>
<small id=omsg>Введи значение, как оно сейчас в игре. Дальше панель скажет, что делать.</small><div id=ores></div>
<small>Глубина и макс. смещение берутся из «Помощники поиска → Цепочка». Нажми на строку: цепочка скопируется.</small></div>
<details class=card id=wz><summary><svg class=ic><use href="#i-search"/></svg>Мастер: найти HP / позицию / броню / голод<svg class=ic><use href="#i-plus"/></svg></summary><div style="padding:0 9px 9px">
<select id=zf onchange="zSet()"><option value=hp>Здоровье</option><option value=pos>Позиция</option><option value=armor>Броня</option><option value=food>Голод</option></select>
<small id=zh></small>
<div class=row><input id=zx placeholder="значение (X)" inputmode=decimal><input id=zy placeholder="Y" inputmode=decimal style="display:none"><input id=zz placeholder="Z" inputmode=decimal style="display:none"></div>
<div class=grid2><button onclick="zFirst()">1. Искать</button><button class=s onclick="zNext()">2. Сузить</button></div>
<div class=row><input id=zn value=1 inputmode=numeric placeholder="№ в списке"><button class=g onclick="zBind()"><svg class=ic><use href="#i-link"/></svg>Привязать</button></div>
<pre id=zs style="white-space:pre-wrap;font:11px/1.35 ui-monospace,monospace;margin:6px 0 0"></pre></div></details>
<div class=card><h3><svg class=ic><use href="#i-search"/></svg>Поиск значения</h3>
<input id=mv placeholder="значение (например 13)" inputmode=decimal>
<div class=grid2><select id=mt><option value=4>int 4 байта</option><option value=f>float</option><option value=2>2 байта</option><option value=1>1 байт</option></select>
<select id=mall><option value=0>куча (безопасно)</option><option value=1>вся rw-память</option></select></div>
<button onclick="call('mscan',{v:v('mv'),...ty(),all:v('mall')})"><svg class=ic><use href="#i-search"/></svg>Первый поиск</button>
<div class=grid3 style="margin-top:6px"><button class=s onclick="call('mnext',{m:'eq',v:v('mv')})"><svg class=ic><use href="#i-eq"/></svg>= значение</button><button class=s onclick="call('mnext',{m:'inc'})"><svg class=ic><use href="#i-up"/></svg>выросло</button><button class=s onclick="call('mnext',{m:'dec'})"><svg class=ic><use href="#i-down"/></svg>уменьшилось</button>
<button class=s onclick="call('mnext',{m:'same'})"><svg class=ic><use href="#i-eq"/></svg>не менялось</button><button class=s onclick="call('mnext',{m:'chg'})"><svg class=ic><use href="#i-reset"/></svg>менялось</button><button class=s onclick="call('mreset',{})"><svg class=ic><use href="#i-trash"/></svg>сброс</button></div>
<button class=s style="margin-top:6px" onclick="mList()"><svg class=ic><use href="#i-list"/></svg>Список найденных</button>
<div class=lgd><i style="color:var(--cf)">■ float</i><i style="color:var(--ci)">■ int</i><i style="color:var(--cz)">■ 0</i><i style="color:var(--er)">■ не читается</i></div><small id=mlst></small><div id=mlres></div></div>
<div class=card><h3><svg class=ic><use href="#i-snow"/></svg>Запись и заморозка</h3>
<input id=ma placeholder="адрес (hex)"><input id=mw placeholder="новое значение">
<button class=s onclick="qvT()"><svg class=ic><use href="#i-bolt"/></svg>Быстрые значения<svg class=ic><use href="#i-plus"/></svg></button>
<div id=qvp class=qv style="display:none"><div class=seg id=qvm><button class=on onclick="qvM('0',this)">вставить</button><button onclick="qvM('w',this)">записать</button><button onclick="qvM('f',this)">заморозить</button></div>
<div class=chips><b>int</b><button class=s onclick="pv('0','4','0')">0</button><button class=s onclick="pv('1','4','1')">1</button><button class=s onclick="pv('-1','4','-1')">-1</button><button class=s onclick="pv('100','4','100')">100</button><button class=s onclick="pv('999','4','999')">999</button><button class=s onclick="pv('9999','4','9999')">9999</button><button class=s onclick="pv('2147483647','4','МАКС')">МАКС</button>
<b>float</b><button class=s onclick="pv('0','f','0.0')">0</button><button class=s onclick="pv('0.5','f','0.5')">.5</button><button class=s onclick="pv('1','f','1.0')">1</button><button class=s onclick="pv('2','f','2.0')">2</button><button class=s onclick="pv('10','f','10.0')">10</button><button class=s onclick="pv('100','f','100.0')">100</button>
<b>byte</b><button class=s onclick="pv('0','1','byte 0')">0</button><button class=s onclick="pv('1','1','byte 1')">1</button><button class=s onclick="pv('255','1','byte 255')">255</button></div></div>
<div class=grid2><button onclick="call('mset',{a:v('ma'),v:v('mw'),...ty()})"><svg class=ic><use href="#i-save"/></svg>Записать</button><button onclick="call('mset',{all:1,v:v('mw')})"><svg class=ic><use href="#i-save"/></svg>Во все найденные</button>
<button class=g onclick="call('mfreeze',{a:v('ma'),v:v('mw'),...ty()})"><svg class=ic><use href="#i-snow"/></svg>Заморозить</button><button class=g onclick="call('mfreeze',{all:1,v:v('mw')})"><svg class=ic><use href="#i-snow"/></svg>Все найденные</button>
<button class=s onclick="call('mfrlist',{})"><svg class=ic><use href="#i-list"/></svg>Список заморозок</button><button class=d onclick="call('munfreeze',{all:1})"><svg class=ic><use href="#i-sun"/></svg>Разморозить всё</button></div></div>
<div class=card><h3><svg class=ic><use href="#i-eye"/></svg>Монитор адреса</h3>
<div class=grid3><button onclick="call('mwatch',{a:v('ma'),...ty()})"><svg class=ic><use href="#i-start"/></svg>Старт</button><button class=s onclick="call('mwlog',{})"><svg class=ic><use href="#i-list"/></svg>Журнал</button><button class=d onclick="call('mwstop',{})"><svg class=ic><use href="#i-stop"/></svg>Стоп</button></div>
<small>Показывает, когда и как меняется значение по адресу из поля выше.</small>
<span class=lb>Авто-чекер</span>
<div class=seg id=acseg><button class=on onclick="acSet(0,this)">выкл</button><button onclick="acSet(1,this)">1с</button><button onclick="acSet(5,this)">5с</button></div>
<div id=acv class=lv></div><div id=aclog class=lv style="color:var(--dim);white-space:pre-wrap"></div>
<div class=row><input id=mn placeholder="байт (128)"><button class=s onclick="call('mdump',{a:v('ma'),n:v('mn')||128})"><svg class=ic><use href="#i-hex"/></svg>Hex</button></div></div>
<div class=card><h3><svg class=ic><use href="#i-search"/></svg>Помощники поиска</h3>
<div class=seg id=hseg><button class=on onclick="hs('s')">Строки</button><button onclick="hs('n')">Соседи</button><button onclick="hs('c')">Цепочка</button><button onclick="hs('p')">Путь</button></div>
<div id=hs_s><input id=hsq placeholder="текст, например zombie или ник"><div class=row><select id=hsa><option value=0>куча</option><option value=1>вся rw-память</option></select><button onclick="hStr()"><svg class=ic><use href="#i-search"/></svg>Найти</button></div>
<small>Ищет текст в памяти игры (ник, имя моба, id блока). Нажми на результат: адрес подставится в остальные вкладки. Глаз справа показывает значение по этому адресу вживую.</small></div>
<div id=hs_n style="display:none"><div class=lgd><i style="color:var(--cf)">■ float</i><i style="color:var(--ci)">■ int</i><i style="color:var(--cl)">→ lib</i><i style="color:var(--cp)">→ память</i><i style="color:var(--cs)">■ текст</i><i style="color:var(--cz)">■ 0</i></div><input id=hna placeholder="адрес (hex), пусто = из поля адреса выше"><div class=row><input id=hnb value=64 inputmode=numeric placeholder="назад, байт"><input id=hnc value=192 inputmode=numeric placeholder="вперёд, байт"><button onclick="hNear()">Показать</button></div>
<small>Показывает, что лежит в памяти вокруг адреса: числа (int / float), ссылки на другие места и текст. Так видно, где рядом HP, координаты и т.д. Жёлтые строки — ссылки внутрь libminecraftpe.so (часто это начало объекта). Нажми на строку: адрес уйдёт в «Путь».</small></div>
<div id=hs_c style="display:none"><input id=hca placeholder="адрес цели (hex)"><div class=grid3><select id=hcd><option>1</option><option>2</option><option selected>3</option><option>4</option></select><select id=hco><option value=256>смещ. до 0x100</option><option value=1024 selected>до 0x400</option><option value=4096>до 0x1000</option><option value=16384>до 0x4000</option></select><button onclick="hChain()">Искать</button></div>
<div class=row><select id=hck><option value="player.chain">→ player.chain</option><option value="mob.list">→ mob.list</option><option value="block.chain">→ block.chain</option></select><button class=d onclick="api('hptr',{c:1})">Стоп</button></div>
<small>Адрес в памяти меняется при каждом запуске игры, а «постоянный путь» к нему — нет. Это поиск такого пути: от неподвижной точки внутри libminecraftpe.so до твоего значения. Идёт в фоне. Кнопка «в конфиг» запишет путь в настройки World. Для mob.list цель — ячейка списка с указателем на моба.</small></div>
<div id=hs_p style="display:none"><input id=hpe placeholder="адрес начала объекта (hex)"><input id=hpa placeholder="адрес поля, которое нужно (hex)">
<div class=grid3><select id=hpd><option>1</option><option selected>2</option><option>3</option><option>4</option></select><select id=hpn><option value=256>окно 0x100</option><option value=512 selected>окно 0x200</option><option value=1024>окно 0x400</option></select><button onclick="hPath()">Искать</button></div>
<div class=grid3><select id=hpk><option value="mob.f">mob.f</option><option value="block.f">block.f</option><option value="player.f">player.f</option></select><input id=hpl placeholder="название"><select id=hpt><option>float</option><option>int</option><option>byte</option><option>bool</option><option>str</option><option>hex</option></select></div>
<small>Если знаешь адрес, где начинается моб, и адрес его HP, эта вкладка найдёт, через какие ссылки и смещения от первого дойти до второго. Результат пишется в настройки World кнопкой у строки.</small></div>
<small id=hst></small><div id=hres></div></div>

</div>

<div class=pg id=pd style="display:none">
<div class=card><h3><svg class=ic><use href="#i-dex"/></svg>Dex: строки из classes1–8</h3>
<small id=dxi>…</small>
<input id=dxq placeholder="что искать, например MainActivity">
<div class=grid3><select id=dxf><option value=all>все classes</option></select><select id=dxm><option value=sub>содержит</option><option value=start>начинается</option><option value=exact>точно</option></select><select id=dxc><option value=1>Aa = aa</option><option value=0>Aa ≠ aa</option></select></div>
<button onclick="dexFind()"><svg class=ic><use href="#i-search"/></svg>Найти</button>
<small id=dxs></small><div id=dxr></div>
<small>Ищет в Java-части игры (внутри APK): имена классов и методов, текстовые константы. Нажми на результат: покажет соседние строки.</small></div></div>

<div class=pg id=pl style="display:none">
<div class=card><h3><svg class=ic><use href="#i-lib"/></svg>Библиотека для патчинга</h3>
<div class=fn onclick="libOpen()"><div class=nm><span id=lnm>…</span><div class=sub id=lsub></div></div><svg class=ic><use href="#i-list"/></svg></div>
<div id=lpick style="display:none">
<div class=seg style="margin:5px 0"><button id=lgm class=on onclick="libGrp('m')">Minecraft</button><button id=lgc onclick="libGrp('c')">Кастомные</button><button id=lgo onclick="libGrp('o')">Другое</button></div>
<small id=lnote></small><div id=ll></div></div>
<small>«Minecraft» — библиотеки самой игры, «Кастомные» — чужие .so из папки игры (моды, загрузчики, эта панель), «Другое» — система, графика, звук. Все вкладки Lib (хекс, патчи, сигнатуры, строки) работают с выбранной библиотекой.</small></div>
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
<span class=lb>Заготовки (в начало функции: она сразу вернёт значение)</span>
<div class="pre sm" id=pbs32><button class=s onclick="pbv('00 20 70 47','OFF: вернуть 0')">OFF (0)</button><button class=s onclick="pbv('01 20 70 47','ON: вернуть 1')">ON (1)</button><button class=s onclick="pbv('64 20 70 47','вернуть 100')">100</button><button class=s onclick="pbv('70 47','return: выйти сразу')">RET</button><button class=s onclick="pbv('00 BF','NOP (2 байта)')">NOP</button></div>
<div class="pre sm" id=pbs64 style="display:none"><button class=s onclick="pbv('00 00 80 D2 C0 03 5F D6','OFF: вернуть 0')">OFF (0)</button><button class=s onclick="pbv('20 00 80 D2 C0 03 5F D6','ON: вернуть 1')">ON (1)</button><button class=s onclick="pbv('80 0C 80 D2 C0 03 5F D6','вернуть 100')">100</button><button class=s onclick="pbv('C0 03 5F D6','ret: выйти сразу')">RET</button><button class=s onclick="pbv('1F 20 03 D5','NOP (4 байта)')">NOP</button></div>
<select id=pk><option value=0>только сейчас</option><option value=1>сохранять на запуски</option></select>
<button onclick="call('patch',{a:v('pa'),b:v('pb'),k:v('pk')})"><svg class=ic><use href="#i-save"/></svg>Записать</button>
<div class=grid2><button class=s onclick="call('undo',{a:v('pa')})"><svg class=ic><use href="#i-undo"/></svg>Откатить</button><button class=s onclick="call('patches',{})"><svg class=ic><use href="#i-list"/></svg>Список (сессия)</button><button class=s onclick="call('saved',{})"><svg class=ic><use href="#i-list"/></svg>Сохранённые</button><button class=d onclick="call('clearsaved',{})"><svg class=ic><use href="#i-trash"/></svg>Удалить сохранённые</button></div>
<input id=qa placeholder="начало функции, hex"><input id=qv placeholder="число для ret, hex (0-FF)"><input id=qn placeholder="сколько NOP (1)">
<div class=grid2><button onclick="call('quick',{a:v('qa'),m:'ret',v:v('qv')||'0',k:v('pk')})"><svg class=ic><use href="#i-save"/></svg>Функция → число</button><button onclick="call('quick',{a:v('qa'),m:'nop',n:v('qn')||1,k:v('pk')})"><svg class=ic><use href="#i-stop"/></svg>Забить NOP</button></div></div></details>
<details class=card><summary><svg class=ic><use href="#i-search"/></svg>Символы: имя → смещение<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=sq placeholder="часть имени, например destroyBlock или attack">
<div class=row><select id=sk><option value=0>только функции</option><option value=1>и переменные</option></select><button onclick="symFind()"><svg class=ic><use href="#i-search"/></svg>Найти</button></div>
<small id=sys></small><div id=syr></div>
<small>Работает, если библиотека экспортирует имена функций. Нажми на результат: смещение подставится в поля хука, патча и дизассемблера. T — Thumb, A — ARM (хукаются оба, режим выбирается в блоке «Хуки»), D — переменная.</small></div></details>
<details class=card><summary><svg class=ic><use href="#i-plug"/></svg>Хуки (нужен Dobby)<svg class=ic><use href="#i-plus"/></svg></summary><div>
<input id=ka placeholder="смещение функции, hex"><select id=kt><option value=auto>Thumb/ARM: авто</option><option value=thumb>Thumb</option><option value=arm>ARM</option></select><select id=km><option value=log>лог вызовов</option><option value=ret>вернуть значение</option><option value=set>подменить результат</option><option value=arg>подменить аргумент</option><option value=area>слом вокруг (на destroyBlock)</option></select>
<div class=row><input id=kv placeholder="значение, hex"><input id=kn placeholder="№ аргумента 0–7" inputmode=numeric></div>
<button onclick="call('hook',{a:v('ka'),t:v('kt'),m:v('km'),v:v('kv'),n:v('kn')||0})"><svg class=ic><use href="#i-plug"/></svg>Поставить</button>
<input id=ki placeholder="номер хука"><div class=grid3><button class=s onclick="call('hookset',{id:v('ki'),m:v('km'),v:v('kv'),n:v('kn')||0})"><svg class=ic><use href="#i-reset"/></svg>Режим</button><button class=s onclick="call('unhook',{id:v('ki')})"><svg class=ic><use href="#i-stop"/></svg>Снять</button><button class=s onclick="call('hooks',{})"><svg class=ic><use href="#i-list"/></svg>Список</button></div>
<div class=grid2><button class=s onclick="hkLive(this)"><svg class=ic><use href="#i-look"/></svg>Живой список</button><button class=s onclick="call('hookset',{id:v('ki'),reset:1})"><svg class=ic><use href="#i-reset"/></svg>Сбросить счётчики</button></div>
<div id=hkl class=lv style="white-space:pre-wrap;display:none;color:var(--dim)"></div>
<div class=grid3><button class=s onclick="call('hooksave',{})">Сохранить</button><button class=s onclick="call('hookload',{})">Применить сохр.</button><button class=d onclick="call('hookclear',{})">Удалить сохр.</button></div>
<small>лог — считает вызовы, показывает аргументы a0–a7 и разные «this» (a0): так находятся адреса объектов, потом Mem → Соседи. ret — функция сразу возвращает значение. set — результат оригинала заменяется. арг — оригинал вызывается, но аргумент № заменяется на значение (float как hex: 170.0 = 432A0000). слом вокруг — ставь на GameMode::destroyBlock, в «значение» пиши радиус: 1 (3×3×3) или 2 (5×5×5). Сломал один блок — оригинал вызывается ещё для соседних. Сохранённые хуки ставятся при старте, только если байты функции те же.</small></div></details>
</div>

<div class=pg id=pf style="display:none">
<div class=card><h3><svg class=ic><use href="#i-file"/></svg>Быстрые настройки (options.txt)</h3>
<button class=s onclick="findopt()"><svg class=ic><use href="#i-search"/></svg>Найти options.txt</button>
<input id=op placeholder="путь к options.txt (заполнится сам)">
<div class=grid2><input id=ok1 placeholder="ключ" value="gfx_viewdistance"><input id=ov1 placeholder="значение" value="32"></div>
<button onclick="call('setkey',{p:v('op'),k:v('ok1'),v:v('ov1')})"><svg class=ic><use href="#i-save"/></svg>Задать</button>
<div class=grid3><button class=s onclick="q('gfx_gamma',v('ov1'))">яркость</button></div>
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
<div class=card><h3><svg class=ic><use href="#i-bolt"/></svg>Functions second menu</h3>
<div class=seg id=pcseg><button class=on onclick="pcSet('off')">OFF</button><button onclick="pcSet('pc')">pc</button></div>
<small>OFF: только обычная вкладка «Функции» (Classic). pc: отдельное меню в стиле читклиента. Категории — красные окна, которые можно двигать, клик по функции включает её, стрелка справа открывает настройки. В левой колонке появится вкладка F; оверлей-кнопка F поверх игры включается через FMenu.java.</small></div>
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
<button id=bd class=nav onclick="tab('d')"><span class=bx><svg class=ic><use href="#i-dex"/></svg></span>Dex</button>
<button id=bf class=nav onclick="tab('f')"><span class=bx><svg class=ic><use href="#i-file"/></svg></span>File</button>
<button id=bs class=nav onclick="tab('s')"><span class=bx><svg class=ic><use href="#i-safe"/></svg></span>Safe</button>
<button id=bt class=nav onclick="tab('t')"><span class=bx><svg class=ic><use href="#i-palette"/></svg></span>Тема</button>
<button id=bF class=nav style="display:none" onclick="pcOpen()"><span class=bx><b style="font-size:15px">F</b></span>PC</button></aside>
<iframe id=pcf></iframe>
<script>
const T=new URLSearchParams(location.search).get('t')||'';const out=document.getElementById('out');
const ERR=/не найден|не найдено|не найдена|ошибк|не удал|не читается|не могу|нужен |нужно |нужны |неверн|неизвестн|вне читаем|вне сегмент|не подход|слишком|нет такого|не совпал|не нашёл|ненадёжна|не привязано|не запускался|список пуст|нет привязки|нет ответа|ссылок не найдено|вызовов не найдено|заморозок нет|хуков нет|нет в процессе|патчей в этой сессии нет|сохранённых патчей нет|отключённых патчей нет|нет доступа|не папка|путь вне|не обычный|заморозка снята|запись не удалась|занят|сначала|нет описания|найдено: 0\b|осталось: 0\b|совпадений: 0\b|кандидатов: 0\b|только GET|bad request|mprotect|остановлено: |неправиль/i;
const WRN=/внимание|лимит|частично|эвристик|опасно|устарел|другая версия|осторожн|только сейчас/i;
const OKK=/^ok\b|включено:|выключено:|записано|заморожено|сохранён|сохранена|сохранены|привязано|откат|удален|снято|снят\b|заменено|добавлено|восстановлен|остановлен|слежу|выбрана:|создан|возвращены|блокировка снята|вставлен|в поля помощников|найдено: [1-9]|совпадений: [1-9]|осталось: [1-9]|поиск запущен|найдено путей|найдено цепочек|автопатч|готово|копия:|вхождений [^:]*: [1-9]/i;
function cls(l){if(ERR.test(l))return 'er';if(WRN.test(l))return 'wr';if(OKK.test(l))return 'ok';return ''}
const esc=s=>s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
function tok(l){return esc(l).replace(/(0x[0-9A-Fa-f]+)/g,'<span class=ad>$1</span>').replace(/("[^"]*"|«[^»]*»)/g,'<span class=st>$1</span>')}
function mnc(x){x=x.replace(/\.w$/,'');
if(/^(bl|blx)$/.test(x)||x=='b')return x=='b'?'m2':'m1';
if(/^b(eq|ne|hs|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)$/.test(x)||/^cbn?z$/.test(x)||/^t(bb|bh)/.test(x))return 'm2';
if(/^(push|pop|ldm|stm|ldmdb|stmdb)/.test(x))return 'm3';
if(/^(ldr|str|vldr|vstr)/.test(x))return 'm4';
if(/^(cmp|cmn|tst|teq|it[te]*|vcmp)/.test(x))return 'm5';
if(/^(nop|bx|udf|bkpt|svc|\.hword|\.inst)/.test(x))return 'dm';
return ''}
function paintLine(l){
let m;
if((m=l.match(/^(0x[0-9a-f]{8})(\s+)([0-9a-f]{4}|[0-9a-f]{8})(\s+)(\S+)(.*)$/))&&!ERR.test(l)){const c=mnc(m[5]);
return '<div><span class=ad>'+m[1]+'</span>'+m[2]+'<span class=dm>'+m[3]+'</span>'+m[4]+'<span class="'+c+'">'+esc(m[5])+'</span>'+tok(m[6]).replace(/(; \[0x[0-9a-f]+\]=0x[0-9a-f]+)/,'<span class=dm>$1</span>')+'</div>'}
if((m=l.match(/^(0x[0-9A-Fa-f]+): ((?:[0-9A-F]{2} ?)+)$/))){
return '<div><span class=ad>'+m[1]+'</span>: '+m[2].replace(/([0-9A-F]{2})/g,x=>x=='00'?'<span class=dm>00</span>':x)+'</div>'}
const c=cls(l);if(c)return '<div class='+c+'>'+esc(l)+'</div>';
return '<div>'+tok(l)+'</div>'}
let RAW='';
function paint(t){out.innerHTML=t.replace(/\n$/,'').split('\n').map(paintLine).join('')}
Object.defineProperty(out,'textContent',{configurable:true,get(){return RAW},set(v){RAW=String(v);paint(RAW)}});
async function symFind(){document.getElementById('sys').textContent='ищу…';const t=await api('sym',{s:v('sq'),all:v('sk'),max:300});
hRender('syr','sys',t,(r,c)=>{hTx(r,c[0]+'  '+(c[4]||c[3])+'  ['+c[2]+', '+c[1]+' Б]','var(--cl)');r.style.cursor='pointer';r.onclick=()=>{for(const i of ['ka','pa','da','ha','fa','ca'])document.getElementById(i).value=c[0].replace('0x','');out.textContent='смещение '+c[0]+' → в поля хука, патча, дизассемблера и hex'}},40)}
let HKT=null;
function hkLive(b){const d=document.getElementById('hkl');if(HKT){clearInterval(HKT);HKT=null;d.style.display='none';b.className='s';return}
d.style.display='';b.className='g';const tick=async()=>{if(document.getElementById('pl').style.display=='none'){clearInterval(HKT);HKT=null;d.style.display='none';b.className='s';return}d.textContent=(await api('hooks')).trim()};tick();HKT=setInterval(tick,1000)}
function paintEl(el,t){el.textContent=t;const c=cls(t);el.style.color=c=='er'?'var(--er)':c=='ok'?'var(--ok)':c=='wr'?'var(--wr)':''}
function tab(x){for(const k of ['n','m','l','d','f','s','t']){document.getElementById('p'+k).style.display=x==k?'':'none';document.getElementById('b'+k).className=x==k?'nav on':'nav'}
if(x=='n'){fnl();slRefresh()}if(x=='l')libLoad();if(x=='d'&&!window.dxOnce){window.dxOnce=1;dexList()}if(x=='f'&&!window.fOnce){window.fOnce=1;findopt()}window.scrollTo(0,0)}
function v(i){return document.getElementById(i).value.trim()}
function ty(){const t=v('mt');return t=='f'?{sz:4,f:1}:{sz:t,f:0}}
async function api(p,o){const q=new URLSearchParams(o||{});q.set('t',T);try{return await(await fetch('/api/'+p+'?'+q)).text()}catch(e){return ''}}
async function call(p,o){const q=new URLSearchParams(o);q.set('t',T);out.textContent='…';
try{const r=await fetch('/api/'+p+'?'+q);const t=await r.text();out.textContent=t;return t}catch(e){out.textContent='ошибка: '+e;return ''}}
function cp(){const t=out.textContent;if(window.MGGJ){MGGJ.copy(t)}else if(navigator.clipboard){navigator.clipboard.writeText(t)}}
async function fnl(){const q=new URLSearchParams({t:T});let r='';try{r=await(await fetch('/api/fnlist?'+q)).text()}catch(e){r='ошибка'}
const d=document.getElementById('fl');d.textContent='';
if(r.startsWith('пусто')||r.indexOf('\t')<0){const m=document.createElement('div');m.style.color='var(--dim)';m.textContent=r.startsWith('пусто')?'Функций пока нет.':r;d.appendChild(m);return}
for(const ln of r.trim().split('\n')){const [n,st,c]=ln.split('\t');const prof=st[0]=='P';const s=prof?st[1]:st;const on=s=='1';
const row=document.createElement('div');row.className='fn c';
const nm=document.createElement('div');nm.className='nm';nm.textContent=n;const sub=document.createElement('div');sub.className='sub';
sub.textContent=(prof?'набор ':'')+c+(prof?'':' п.')+(s=='3'?' · др. версия':s=='2'?' · частично':'');nm.appendChild(sub);
const sw=document.createElement('div');sw.className='sw '+(on?'on':s=='3'?'bad':s=='2'?'mid':'');
row.onclick=async()=>{if(s=='3'){out.textContent='байты не совпали: функция для другой версии игры';return}
await call(on?'fnoff':'fnon',{n:n,k:v('fk2')});fnl()};row.appendChild(nm);row.appendChild(sw);d.appendChild(row)}}
async function findopt(){const t=await call('findopt',{});const m=t.split('\n').find(l=>l.endsWith('options.txt'));if(m)document.getElementById('op').value=m.trim()}
const LB={proc:32,sel:'',selBits:32,grp:'',list:[]};
async function libLoad(){let r='';try{r=await(await fetch('/api/libs?'+new URLSearchParams({t:T}))).text()}catch(e){document.getElementById('lnm').textContent='ошибка';return}
const ls=r.trim().split('\n');const h=ls.shift().split('\t');if(h[0]!='#'){document.getElementById('lnm').textContent=r;return}
LB.proc=+h[1];LB.sel=h[2];LB.selBits=+h[3];
LB.list=ls.map(l=>{const a=l.split('\t');return{n:a[0],b:+a[1],sz:a[2],d:a[3],on:a[4]=='1',g:a[5]||'o',ld:a[6]!='0'}});
if(!LB.grp){const c=LB.list.find(x=>x.on);LB.grp=c?c.g:'m'}libRender()}
function libRender(){const cur=LB.list.find(x=>x.on);document.getElementById('lnm').textContent=LB.sel||'не найдена';
document.getElementById('lsub').textContent=cur?(cur.b+' bit · '+cur.d):'нет в процессе игры';
for(const k of ['m','c','o'])document.getElementById('lg'+k).className=LB.grp==k?'on':'';
const d=document.getElementById('ll');d.textContent='';const L=LB.list.filter(x=>x.g==LB.grp);
const nm={m:'Minecraft',c:'Кастомные',o:'Другое'}[LB.grp];
document.getElementById('lnote').innerHTML='<span class=lgd><i style="color:var(--cf)">■ Minecraft</i><i style="color:var(--cl)">■ кастомные</i><i style="color:var(--cz)">■ другое / не загружена</i><i style="color:var(--ci)">■ 32 bit</i><i style="color:var(--er)">■ 64 bit</i></span><br>'+nm+': '+L.length+(LB.grp=='c'?' (не из игры, но лежат в её папке библиотек)':LB.grp=='m'?' (игра и её библиотеки)':' (система, графика, звук)');
for(const x of L){const row=document.createElement('div');row.className='fn';const n=document.createElement('div');n.className='nm';const ttl=document.createElement('span');ttl.textContent=x.n;n.appendChild(ttl);
const sub=document.createElement('div');sub.className='sub';sub.textContent=x.b+' bit · '+x.d+' · '+x.sz;n.appendChild(sub);
const sw=document.createElement('div');sw.className='sw'+(x.on?' on':'');
const gc={m:'var(--cf)',c:'var(--cl)',o:'var(--cz)'}[x.g]||'var(--cz)';row.style.borderLeft='4px solid '+(x.ld?gc:'var(--cz)');n.firstChild.style.color=x.ld?gc:'var(--cz)';
if(x.b==64){sub.style.color='var(--er)'}else if(x.ld){sub.style.color='var(--ci)'}
if(x.ld)row.onclick=()=>libSel(x.n);else{row.style.opacity='.55';sw.style.display='none'}
row.appendChild(n);row.appendChild(sw);d.appendChild(row)}
document.getElementById('pbs32').style.display=LB.selBits==64?'none':'';document.getElementById('pbs64').style.display=LB.selBits==64?'':'none'}
function libGrp(g){LB.grp=g;libRender()}
function libOpen(){const p=document.getElementById('lpick');p.style.display=p.style.display=='none'?'':'none';if(p.style.display=='')libLoad()}
async function libSel(n){await call('libsel',{n:n});await libLoad();document.getElementById('lpick').style.display='none'}
function pbv(b,t){document.getElementById('pb').value=b;out.textContent=t+'\nбайты вставлены. Впиши смещение функции и нажми «Записать».'}
let QM='0';function qvT(){const p=document.getElementById('qvp');p.style.display=p.style.display=='none'?'':'none'}
function qvM(m,b){QM=m;for(const x of document.querySelectorAll('#qvm button'))x.className=x==b?'on':''}
async function pv(val,t,name){document.getElementById('mw').value=val;document.getElementById('mt').value=t;const m=QM;document.getElementById('qvp').style.display='none';
if(m=='0'){out.textContent='значение '+name+' ('+val+') вставлено в поле'+(t=='f'?' · тип float':t=='1'?' · тип 1 байт':'')+'\nнажми «Записать» или «Заморозить»';return}
if(!v('ma')){out.textContent='сначала впиши адрес';return}
call(m=='w'?'mset':'mfreeze',{a:v('ma'),v:val,...ty()})}
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
const SL=[{s:'fov',t:'Fov changer',min:30,max:150,def:70,opt:'gfx_field_of_view',h:'Mem: найди текущий FOV как float (например 70), смени в настройках, сузь → «Привязать».'}];
function slotInit(){const d=document.getElementById('sl');d.textContent='';for(const x of SL){const c=document.createElement('div');c.className='card';
c.innerHTML=`<h3><svg class=ic><use href="#i-eye"/></svg>${x.t}</h3><div class=rg><input type=range id=r_${x.s} min=${x.min} max=${x.max} value=${x.def} oninput="document.getElementById('rv_${x.s}').textContent=this.value"><b id=rv_${x.s}>${x.def}</b></div>
<div class=grid3><button onclick="slA('${x.s}')">Применить</button><button class=s onclick="slS('${x.s}')">Снять</button><button class=s onclick="slO('${x.s}')">options.txt</button></div>
<button class=s style="margin-top:5px" id=zmb onclick="zoomT()">Зум: выкл</button>
<small id=st_${x.s}>…</small>
<details style="margin-top:6px"><summary style="cursor:pointer;color:var(--dim);font-size:11px">Адрес и привязка</summary>
<div class=row><input id=ba_${x.s} placeholder="адрес (hex) или пусто"><button class=s onclick="slB('${x.s}')"><svg class=ic><use href="#i-link"/></svg>Привязать</button></div>
<button class=s style="margin-top:5px" onclick="call('csexport',{s:'${x.s}'})">Экспорт привязки</button><small>${x.h}</small></details>`;d.appendChild(c)}slRefresh()}
async function slRefresh(){for(const x of SL){const e=document.getElementById('st_'+x.s);if(e)paintEl(e,(await api('csst',{s:x.s})).trim())}}
async function slA(s){const st=document.getElementById('st_'+s).textContent;if(st.startsWith('не привязано')&&v('ba_'+s))await call('csbind',{s:s,a:v('ba_'+s)});await call('csapply',{s:s,v:v('r_'+s)});slRefresh()}
async function slS(s){await call('csstop',{s:s});slRefresh()}
async function slB(s){await call('csbind',{s:s,a:v('ba_'+s)||v('ma')});slRefresh()}
async function optPath(){let p=v('op');if(p)return p;const t=await call('findopt',{});const m=t.split('\n').find(l=>l.endsWith('options.txt'));if(m){document.getElementById('op').value=m.trim();return m.trim()}return''}
async function slO(s){const x=SL.find(y=>y.s==s);const p=await optPath();if(!p)return;call('setkey',{p:p,k:x.opt,v:v('r_'+s)})}
let HS='s';
function hs(x){HS=x;const ks=['s','n','c','p'];for(const k of ks)document.getElementById('hs_'+k).style.display=k==x?'':'none';document.querySelectorAll('#hseg button').forEach((b,i)=>b.className=ks[i]==x?'on':'');document.getElementById('hres').textContent='';document.getElementById('hst').textContent=''}
function hRender(box,stId,t,mk,per){per=per||40;const d=document.getElementById(box);d.textContent='';const st=document.getElementById(stId);st.textContent='';const rows=[];
for(const l of t.split('\n')){if(!l)continue;const c=l.split('\t');if(c[0]=='#'){st.textContent=c.slice(1).join(' · ');continue}rows.push(c)}
let shown=0;const more=document.createElement('div');more.className='row';d.appendChild(more);
function draw(n){const e=Math.min(rows.length,shown+n);for(;shown<e;shown++){const r=document.createElement('div');r.className='kv';mk(r,rows[shown]);d.insertBefore(r,more)}
more.textContent='';const left=rows.length-shown;if(left>0){const b=document.createElement('button');b.className='s';b.textContent='Ещё '+Math.min(per,left)+' (осталось '+left+')';b.onclick=()=>draw(per);more.appendChild(b);
const a=document.createElement('button');a.className='s';a.textContent='Показать все';a.onclick=()=>draw(rows.length);more.appendChild(a)}}
draw(per)}
function hRows(t,mk){hRender('hres','hst',t,mk)}
const EY={};let EYT=null;
function hEye(r,a){const b=document.createElement('button');b.className='s';b.title='Показать значение вживую';b.innerHTML='<svg class=ic><use href="#i-look"/></svg>';
const lv=document.createElement('div');lv.className='lv';lv.style.display='none';r.classList.add('wrap');
b.onclick=e=>{e.stopPropagation();if(EY[a]){delete EY[a];lv.style.display='none';b.className='s'}else{EY[a]=lv;lv.style.display='';lv.textContent='…';b.className='g';if(!EYT)EYT=setInterval(eyTick,900);eyTick()}};
r.appendChild(b);r.appendChild(lv)}
async function eyTick(){for(const k of Object.keys(EY))if(!document.body.contains(EY[k]))delete EY[k];const ks=Object.keys(EY);
if(!ks.length){clearInterval(EYT);EYT=null;return}
const t=await api('hval',{a:ks.slice(0,80).join(',')});for(const l of t.split('\n')){const c=l.split('\t');if(EY[c[0]])EY[c[0]].textContent=c[1]=='?'?'не читается':'0x'+c[1]+'   int '+c[2]+(c[3]?'   float '+c[3]:'')+(c[4]?'   «'+c[4]+'»':'')}}
async function mList(){document.getElementById('mlst').textContent='читаю…';const t=await api('mlist',{n:1000});const o=[];
for(const l of t.split('\n')){if(!l)continue;const m=l.match(/^(0x[0-9A-Fa-f]+)\s+=\s+(.*)$/);o.push(m?m[1]+'\t'+m[2]:'#\t'+l)}
const isf=/float/.test(t.split('\n')[0]);
hRender('mlres','mlst',o.join('\n'),(r,c)=>{hTx(r,c[0]+'   =   '+c[1],c[1]=='?'?'var(--er)':isf?'var(--cf)':(c[1]=='0'?'var(--cz)':'var(--ci)'));r.style.cursor='pointer';r.onclick=()=>hSet(c[0]);hEye(r,c[0])},50)}
async function dexList(){const t=await api('dexlist');const ls=t.split('\n').filter(x=>x);const sel=document.getElementById('dxf');const inf=document.getElementById('dxi');
if(!ls.length){inf.textContent='нет ответа';return}
const h=ls[0].split('\t');if(h[0]!='#'||ls.length==1){inf.textContent=h[1]||'';return}
inf.textContent='APK: '+h[1];sel.textContent='';const al=document.createElement('option');al.value='all';al.textContent='все classes';sel.appendChild(al);
for(const l of ls.slice(1)){const c=l.split('\t');const o=document.createElement('option');o.value=c[0];o.textContent=c[0]+' ('+Math.round(c[1]/1024)+' КБ)';sel.appendChild(o)}}
async function dexFind(){document.getElementById('dxs').textContent='ищу…';const t=await api('dexfind',{q:v('dxq'),f:v('dxf'),m:v('dxm'),ci:v('dxc')});
hRender('dxr','dxs',t,(r,c)=>{hTx(r,c[0].replace('.dex','')+'  #'+c[1]+'   '+c[2],'var(--cs)');r.style.cursor='pointer';r.onclick=async()=>{out.textContent=await api('dexctx',{f:c[0],i:c[1],n:6})}},50)}
function hTx(r,txt,col){const b=document.createElement('b');b.textContent=txt;b.style.textAlign='left';b.style.flex='1';b.style.fontSize='11px';if(col)b.style.color=col;r.appendChild(b);return b}
function hBtn(r,txt,fn){const b=document.createElement('button');b.className='s';b.textContent=txt;b.style.width='auto';b.style.padding='0 8px';b.onclick=fn;r.appendChild(b)}
function hSet(a){for(const i of ['ma','hna','hca','hpa'])document.getElementById(i).value=a;out.textContent='адрес '+a+' → в поля помощников'}
async function hStr(){document.getElementById('hst').textContent='ищу…';const t=await api('hstr',{s:v('hsq'),all:v('hsa')});
hRows(t,(r,c)=>{hTx(r,c[0]+'  '+c[1],'var(--cs)');r.style.cursor='pointer';r.onclick=()=>hSet(c[0]);hEye(r,c[0])})}
function nearCol(c){const note=c[5]||'',fl=c[4],hw=c[2];
if(note.startsWith('→ lib'))return 'var(--cl)';
if(note.startsWith('→ память'))return note.indexOf('«')>=0?'var(--cs)':'var(--cp)';
if(note.startsWith('«'))return 'var(--cs)';
if(hw=='00000000')return 'var(--cz)';
if(fl)return 'var(--cf)';
return 'var(--ci)'}
async function hNear(){const a=v('hna')||v('ma');document.getElementById('hst').textContent='читаю…';const t=await api('hnear',{a:a,b:v('hnb'),n:v('hnc')});
hRows(t,(r,c)=>{hTx(r,c[1]+'  '+c[2]+'  i='+c[3]+(c[4]?'  f='+c[4]:'')+(c[5]?'  '+c[5]:''),nearCol(c));r.style.cursor='pointer';r.onclick=()=>{document.getElementById('hpa').value=c[0];document.getElementById('ma').value=c[0];out.textContent='поле '+c[0]}})}
let HT=null;
async function hChain(){const a=v('hca');if(!a)return;clearInterval(HT);out.textContent=await api('hptr',{a:a,d:v('hcd'),o:v('hco')});
const tick=async()=>{const t=await api('hptrst');const run=t.startsWith('#\tидёт');
hRows(t,(r,c)=>{hTx(r,c[0]+'  ('+c[1]+')','var(--cl)');hBtn(r,'в конфиг',async()=>{let ch=c[0];const key=v('hck');if(key=='mob.list'){const k=ch.split(',');if(k.length>1)ch=k.slice(0,-1).join(',')}out.textContent=await api('wcfgadd',{line:key+'|'+ch})})});
if(!run)clearInterval(HT)};HT=setInterval(tick,1200);tick()}
async function hPath(){document.getElementById('hst').textContent='ищу…';const t=await api('hpath',{e:v('hpe'),a:v('hpa'),d:v('hpd'),n:v('hpn')});
hRows(t,(r,c)=>{hTx(r,c[0],'var(--cp)');hBtn(r,'в конфиг',async()=>{out.textContent=await api('wcfgadd',{line:v('hpk')+'|'+(v('hpl')||'поле')+'|'+c[0]+'|'+v('hpt')})})})}
const ZK={hp:['p_hp','Введи текущее HP как в игре (например 20) → «Искать». Получи урон или вылечись, введи новое → «Сузить». Повторяй, пока адресов 1–3.'],
pos:['p_pos','В настройках мира включи «Показывать координаты». Введи X, Y, Z с экрана → «Искать» (поиск по X и Z). Пройди несколько шагов, введи новые → «Сузить».'],
armor:['p_armor','Введи число очков брони (например 5) → «Искать». Надень или сними часть брони, введи новое → «Сузить».'],
food:['p_food','Введи текущий голод (например 20) → «Искать». Проголодайся или поешь, введи новое → «Сузить».']};
function zSet(){const k=v('zf');document.getElementById('zh').textContent=ZK[k][1];document.getElementById('zy').style.display=document.getElementById('zz').style.display=k=='pos'?'':'none'}
async function zList(){document.getElementById('zs').textContent=(await api('mlist',{n:8})).trim()}
async function zFirst(){const k=v('zf');document.getElementById('zs').textContent='ищу…';
if(k=='pos'){await api('hscanf',{v:v('zx'),tol:0.02,all:0});await api('hrel',{off:8,v:v('zz'),tol:0.02})}else await api('hscanf',{v:v('zx'),tol:0.01,all:0});zList()}
async function zNext(){const k=v('zf');if(k=='pos'){await api('hnextf',{v:v('zx'),tol:0.02});await api('hrel',{off:8,v:v('zz'),tol:0.02})}else await api('hnextf',{v:v('zx'),tol:0.01});zList()}
async function zBind(){const k=v('zf');const l=(await api('mlist',{n:60})).split('\n').filter(x=>x.startsWith('0x'));const a=(l[(+v('zn')||1)-1]||'').split(/\s/)[0];
if(!a){document.getElementById('zs').textContent='нет такого номера в списке';return}await call('csbind',{s:ZK[k][0],a:a});zList()}
const OF={gen:0,n:0,busy:false,t:'f'};
const sleepMs=ms=>new Promise(r=>setTimeout(r,ms));
function ofMsg(t){paintEl(document.getElementById('omsg'),t)}
function ofShowStep(on){document.getElementById('ostep').style.display=on?'':'none'}
async function ofList(){const t=await api('mlist',{n:3});const m=t.match(/кандидатов: (\d+)/);
return{n:m?+m[1]:0,a:t.split('\n').filter(x=>x.startsWith('0x')).map(x=>x.split(/\s/)[0])}}
async function ofRun(fn){if(OF.busy)return;OF.busy=true;try{await fn()}finally{OF.busy=false}}
function ofVal(){const x=v('ov').replace(',','.');if(x===''||!isFinite(+x)){ofMsg('нужно число');return null}
if(OF.t=='i'&&!Number.isInteger(+x)){ofMsg('нужно целое число или выбери float');return null}return x}
async function ofStart(){await ofRun(async()=>{OF.t=v('ot');const x=ofVal();if(x===null)return;const g=++OF.gen;
await api('hptr',{c:1});document.getElementById('ores').textContent='';ofShowStep(false);ofMsg('ищу…');
const r=OF.t=='f'?await api('hscanf',{v:x,tol:0.01,all:0}):await api('mscan',{v:x,sz:4,f:0,all:0});
if(g!=OF.gen)return;if(!r){ofMsg('нет ответа от панели');return}if(r.startsWith('слишком')){ofMsg(r.trim());return}
await ofAfter(g)})}
async function ofNext(){await ofRun(async()=>{const x=ofVal();if(x===null)return;const g=OF.gen;ofMsg('сужаю…');
const r=OF.t=='f'?await api('hnextf',{v:x,tol:0.01}):await api('mnext',{m:'eq',v:x});
if(g!=OF.gen)return;if(!r){ofMsg('нет ответа от панели');return}await ofAfter(g)})}
async function ofSame(){await ofRun(async()=>{const g=OF.gen;ofMsg('отсеиваю…');const r=await api('mnext',{m:'same'});
if(g!=OF.gen)return;if(!r){ofMsg('нет ответа от панели');return}await ofAfter(g)})}
async function ofAfter(g){const l=await ofList();if(g!=OF.gen)return;OF.n=l.n;
if(!l.n){ofShowStep(false);ofMsg('найдено: 0. Проверь значение и тип (float / int), потом «Найти оффсет» заново');return}
if(l.n>3){ofShowStep(true);ofMsg('осталось: '+l.n+'. Измени значение в игре (получи урон, поешь, сними броню), впиши новое и нажми «Изменил → сузить»');return}
ofShowStep(true);await ofSearch(g,l.a)}
async function ofChains(){await ofRun(async()=>{const g=OF.gen;const l=await ofList();
if(!l.n||l.n>3){ofMsg('сначала сузь поиск до 1–3 адресов (сейчас '+l.n+')');return}await ofSearch(g,l.a)})}
function ofRow(txt,col,copy){const r=document.createElement('div');r.className='kv';hTx(r,txt,col);
if(copy){r.style.cursor='pointer';r.onclick=()=>{document.getElementById('ma').value=copy.a;out.textContent=copy.c;cp();out.textContent='скопировано: '+copy.c}}
document.getElementById('ores').appendChild(r);return r}
async function ofSearch(g,addrs){document.getElementById('ores').textContent='';let total=0;
for(let i=0;i<addrs.length;i++){const a=addrs[i];let s='';
for(let k=0;k<40;k++){s=await api('hptr',{a:a,d:v('hcd'),o:v('hco')});if(g!=OF.gen)return;if(!s.startsWith('поиск уже идёт'))break;ofMsg('жду, пока закончится другой поиск…');await sleepMs(500)}
if(!s.startsWith('поиск запущен')){ofMsg('ошибка: '+(s.trim()||'нет ответа'));return}
let t='';let miss=0;
for(;;){await sleepMs(1000);t=await api('hptrst');if(g!=OF.gen)return;
if(!t){if(++miss>10){ofMsg('нет ответа от панели');return}continue}miss=0;
const h=t.split('\n')[0].split('\t');if(h[1]!='идёт')break;ofMsg('ищу цепочку '+(i+1)+' из '+addrs.length+': '+(h[2]||''))}
const ls=t.split('\n');const st=(ls[0].split('\t')[2]||'');const ch=ls.slice(1).filter(x=>x);
hEye(ofRow('адрес '+a,'var(--cp)'),a);
if(!ch.length)ofRow(st,'var(--wr)');
for(const l of ch.slice(0,8)){const c=l.split('\t');const p=c[0].split(',');total++;
ofRow(c[0]+(p.length>1?'   поле +0x'+p[p.length-1]:'')+'   ('+c[1]+')','var(--cl)',{a:a,c:c[0]})}}
ofMsg(total?'найдено цепочек: '+total+'. Это кандидаты: перезапусти игру и проверь, какая всё ещё ведёт к значению':'цепочек до статики не найдено: увеличь глубину или смещение в «Цепочка» и нажми «Цепочки заново»')}
async function ofReset(){OF.gen++;ofShowStep(false);document.getElementById('ores').textContent='';
await api('hptr',{c:1});await api('mreset');ofMsg('сброшено')}

const AC={sec:0,timer:null,gen:0,a:'',prev:null,log:[]};
function acSet(sec,btn){for(const b of document.querySelectorAll('#acseg button'))b.className=b==btn?'on':'';
clearTimeout(AC.timer);AC.sec=sec;AC.gen++;AC.a='';AC.prev=null;AC.log=[];
document.getElementById('aclog').textContent='';document.getElementById('acv').textContent='';if(sec)acTick(AC.gen)}
function acFmt(c){const t=v('mt');const u=parseInt(c[1],16);if(t=='f')return c[3]||'0x'+c[1];
if(t=='1')return String(u&255);if(t=='2')return String(u<<16>>16);return c[2]}
async function acTick(g){const a=v('ma');const box=document.getElementById('acv');
if(!a)box.textContent='впиши адрес в поле «адрес (hex)»';
else{const t=await api('hval',{a:a});if(g!=AC.gen)return;const c=t.split('\n')[0].split('\t');
if(c.length<4||c[1]=='?')box.textContent=a+': не читается';
else{const key=a+'|'+v('mt');if(key!=AC.a){AC.a=key;AC.prev=null;AC.log=[]}
const x=acFmt(c);const now=new Date().toLocaleTimeString();
if(AC.prev!==null&&x!==AC.prev){AC.log.unshift(now+'  '+AC.prev+' → '+x);AC.log.length=Math.min(AC.log.length,8)}
AC.prev=x;box.textContent=a+' = '+x+'   ('+now+')';document.getElementById('aclog').textContent=AC.log.join('\n')}}
AC.timer=setTimeout(()=>acTick(g),AC.sec*1000)}
function fnTab(x){document.getElementById('fgl').style.display=x=='g'?'':'none';document.getElementById('fll').style.display=x=='l'?'':'none';document.querySelectorAll('#fseg button').forEach((b,i)=>b.className=(i==0)==(x=='g')?'on':'')}
let AZ=0;
function azUi(t){AZ=t.startsWith('1')?1:0;const a=t.trim().split(' ');if(AZ){document.getElementById('azw').value=a[1];document.getElementById('azh').value=a[2];document.getElementById('azd').value=a[3]}document.getElementById('azs').textContent=AZ?'включено: '+a[1]+'x'+a[2]+'x'+a[3]:'выключено';document.getElementById('azsw').className='sw '+(AZ?'on':'')}
async function azInit(){azUi(await api('zone',{on:2}))}
async function azSend(on){await call('zone',{on:on,w:v('azw'),h:v('azh'),d:v('azd')});azUi(await api('zone',{on:2}))}
function azGo(){azSend(AZ?0:1)}
function plUi(t){PL=t.startsWith('1')?1:0;const a=t.trim().split(' ');if(PL){document.getElementById('plw').value=a[1];document.getElementById('plh').value=a[2]}document.getElementById('pls').textContent=PL?'включено: '+a[1]+'x'+a[2]:'выключено';document.getElementById('plsw').className='sw '+(PL?'on':'')}
let PL=0;
async function plInit(){plUi(await api('place',{on:2}))}
async function plSend(on){await call('place',{on:on,w:v('plw'),h:v('plh'),s:v('plsl')});plUi(await api('place',{on:2}))}
function plGo(){plSend(PL?0:1)}
let ZM=0;
async function zoomT(){ZM=ZM?0:1;await call('csapply',{s:'fov',v:ZM?30:(v('r_fov')||70)});document.getElementById('zmb').textContent='Зум: '+(ZM?'вкл (30)':'выкл');slRefresh()}
const PRV={};
async function prl(){const r=await api('prelist',{});const d=document.getElementById('prl');d.textContent='';
for(const ln of r.trim().split('\n')){const c=ln.split('\t');if(c.length<7)continue;const id=c[0],nm=c[1],on=c[2]=='1',ds=c[3],dv=c[4],off=c[5],hint=c[6],pv=PRV[id]||{};
const w=document.createElement('div');w.style.marginBottom='8px';
w.innerHTML='<div class="fn c" onclick="preGo(\''+id+'\','+(on?0:1)+')"><div class=nm>'+nm+'<div class=sub>'+(on?'включено · '+off:ds!='-'?'слот '+ds+' по умолчанию':'заготовка: нужен адрес')+'</div></div><div class="sw '+(on?'on':'')+'"></div></div>'
+'<div class=row><input id=pa_'+id+' placeholder="адрес hex" value="'+(pv.a||'')+'"><input id=ps_'+id+' placeholder="слот" style="flex:.4" value="'+(pv.s||'')+'"><input id=pv_'+id+' style="flex:.6" value="'+(pv.v||dv)+'"></div><small>'+hint+'</small>';
d.appendChild(w)}}
async function preGo(id,on){PRV[id]={a:v('pa_'+id),s:v('ps_'+id),v:v('pv_'+id)};await call('pre',{id:id,on:on,a:PRV[id].a,s:PRV[id].s,v:PRV[id].v});prl()}
let PCM='off';
function pcUi(m){PCM=m;document.getElementById('bF').style.display=m=='pc'?'':'none';document.querySelectorAll('#pcseg button').forEach((b,i)=>b.className=(i==1)==(m=='pc')?'on':'')}
async function pcSet(m){await call('uimode',{m:m});pcUi(m)}
async function pcInit(){pcUi((await api('uimode',{})).trim()=='pc'?'pc':'off')}
function pcOpen(){if(window.MGGJ&&MGGJ.openF){MGGJ.openF();return}const f=document.getElementById('pcf');if(!f.getAttribute('src'))f.src='/pc?t='+encodeURIComponent(T)+'&embed=1';f.style.display='block'}
function pcClose(){document.getElementById('pcf').style.display='none'}
window.addEventListener('message',e=>{if(e.data==='pcclose')pcClose()});
function plP(w,h){document.getElementById('plw').value=w;document.getElementById('plh').value=h;if(PL)plSend(1)}
function azP(w,h,d){document.getElementById('azw').value=w;document.getElementById('azh').value=h;document.getElementById('azd').value=d;if(AZ)azSend(1)}
fnl();libLoad();slotInit();zSet();azInit();plInit();prl();pcInit();
</script></body></html>)MGG";

// PC-меню функций: отдельная страница /pc (открывается из панели во вкладке F и из оверлей-кнопки F)
static const char *kPcPage = R"MGP(<!doctype html><html><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no"><title>MGG PC</title>
<style>
:root{--hd:#c4262e;--bg:#0d0f14;--w2:#20242f;--tx:#eceef4;--dim:#8d93a6;--a:.88;--zm:1;--lh:26px}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
[hidden]{display:none!important}
html,body{margin:0;height:100%;background:var(--bg);color:var(--tx);font:13px/1.25 system-ui,sans-serif;overflow:hidden}
body.lb{--lh:40%}
#bar{height:38px;display:flex;align-items:center;gap:5px;padding:0 6px;background:#12141b;border-bottom:1px solid #262a37;overflow-x:auto;white-space:nowrap}
#bar b{font-size:13px;letter-spacing:.4px;color:#fff;background:var(--hd);border-radius:6px;padding:3px 8px}
#bar button,#bar input[type=search]{height:28px;border-radius:7px;border:1px solid #2b3040;background:var(--w2);color:var(--tx);font:12px system-ui;flex:none}
#bar button{min-width:30px;padding:0 7px}
#q{width:110px;padding:0 8px}
#bar label{font-size:11px;color:var(--dim);display:flex;align-items:center;gap:3px;flex:none}
#hdc{width:28px;height:28px;padding:0;border:0;background:none;flex:none}
#cv{position:absolute;left:0;right:0;top:38px;bottom:var(--lh);overflow:auto}
#pl{position:relative;width:2400px;height:1600px;transform:scale(var(--zm));transform-origin:0 0}
.win{position:absolute;width:150px;background:rgba(18,24,38,var(--a));border-radius:3px;overflow:hidden;box-shadow:0 2px 8px #0009}
.hd{position:relative;height:26px;background:var(--hd);display:flex;align-items:center;justify-content:center;padding:0 22px;font-weight:700;font-size:12.5px;letter-spacing:.3px;touch-action:none;user-select:none;color:#fff}
.hd i{position:absolute;right:6px;font-style:normal;opacity:.8;font-size:10px;font-weight:400}
.mod{position:relative;display:flex;align-items:center;justify-content:center;min-height:26px;padding:0 22px;color:#e6e9f2;font-size:12px;border-top:1px solid #ffffff0d;user-select:none}
.mod:active{background:#ffffff14}
.mod .n{flex:0 1 auto;text-align:center;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.mod .sb{color:inherit;opacity:.6;font-size:9px;max-width:40px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;margin-left:4px}
.mod.on{background:var(--hd);color:#fff}
.mod.mid{background:linear-gradient(90deg,#8a6a1f,#3a2f12);color:#fff}
.mod.act .n::before{content:"▸ ";opacity:.6}
.ar{position:absolute;right:0;top:0;width:24px;height:100%;display:flex;align-items:center;justify-content:center;opacity:.7;font-size:14px;transition:transform .12s}
.ar.o{transform:rotate(90deg)}
.set{background:rgba(0,0,0,.3);padding:6px 7px 8px;border-top:1px solid #ffffff12}
.set label{display:flex;align-items:center;gap:5px;margin:3px 0;color:var(--dim);font-size:11px}
.set label span{width:46px;flex:none}
.set input,.set select{flex:1;min-width:0;height:26px;background:#10121a;border:1px solid #2d3242;border-radius:5px;color:var(--tx);padding:0 5px;font:12px system-ui}
.set .bt{display:flex;flex-wrap:wrap;gap:4px;margin:5px 0}
.set button{flex:1 1 auto;min-width:0;height:26px;border:0;border-radius:5px;background:#2a2f3f;color:var(--tx);font:11px system-ui;padding:0 7px}
.set button:active{background:var(--hd)}
.set small{display:block;color:var(--dim);font-size:10.5px;margin-top:4px;line-height:1.3}
#log{position:absolute;left:0;right:0;bottom:0;height:var(--lh);background:#0a0b0f;border-top:1px solid #262a37;font:11px/1.35 ui-monospace,monospace;color:#9fe3b9;white-space:pre-wrap;word-break:break-all;padding:4px 8px;overflow:auto}
#gear{display:none}
html.fm,html.fm body{background:transparent}
html.fm #log,html.fm #bar{display:none}
html.fm.tb #bar{display:flex}
html.fm #cv{top:0;bottom:0;overflow:hidden}
html.fm.tb #cv{top:38px}
html.fm #gear{display:flex;position:fixed;right:8px;top:8px;width:32px;height:32px;border-radius:50%;background:var(--hd);color:#fff;align-items:center;justify-content:center;font-size:17px;opacity:.85;z-index:99999}
html.fm.tb #gear{top:44px}
</style></head><body>
<div id=gear>⚙</div>
<div id=bar><b>F</b><input id=q type=search placeholder="поиск">
<button id=zm1>A−</button><button id=zm2>A+</button><button id=op title="прозрачность">◐</button><input type=color id=hdc title="цвет вкладок">
<label><input type=checkbox id=keep>запом.</label><button id=rst title="сбросить окна">⟲</button><button id=cpy title="копировать журнал">⎘</button><button id=lg title="журнал">▤</button><button id=cls hidden>✕</button></div>
<div id=cv><div id=pl></div></div>
<pre id=log>MGG PC готов</pre>
<script>
const QS=new URLSearchParams(location.search),T=QS.get('t')||'',EMB=QS.get('embed')=='1',FM=QS.get('fm')=='1';
if(FM)document.documentElement.classList.add('fm');
function rep(){if(!(FM&&window.MGGJ&&MGGJ.rects))return;const r=[],k=window.devicePixelRatio||1,add=el=>{if(!el)return;const b=el.getBoundingClientRect();if(b.width>0&&b.height>0)r.push((b.left*k).toFixed(1),(b.top*k).toFixed(1),(b.width*k).toFixed(1),(b.height*k).toFixed(1))};
 for(const c in WINS)add(WINS[c].w);add($('gear'));if(document.documentElement.classList.contains('tb'))add($('bar'));MGGJ.rects(r.join(','))}
const $=id=>document.getElementById(id);
const LS=(k,d)=>{try{const x=JSON.parse(localStorage.getItem(k));return x==null?d:x}catch(e){return d}};
const SV=(k,x)=>{try{localStorage.setItem(k,JSON.stringify(x))}catch(e){}};
let UI=Object.assign({zm:innerWidth<520?.7:1,a:.88,hd:'#c4262e',keep:0},LS('mggPcUi',{}));
let POS=LS('mggPcPos',{}),COL=LS('mggPcCol',{}),OPN=LS('mggPcOpen',{}),VAL=LS('mggPcVal',{});
const S={zone:'0',place:'0',fov:'',chunk:'',pre:{},fn:[]};
let ZM=0,FNSIG='',ROW={},NOTES=[],WINS={},ZI=1;
async function api(p,o){const q=new URLSearchParams(o||{});q.set('t',T);try{return await(await fetch('/api/'+p+'?'+q)).text()}catch(e){return 'ошибка связи'}}
function log(t){$('log').textContent=String(t).trim()}
async function call(p,o){const t=await api(p,o);log(t);return t}
const gv=(m,f)=>{const v=(VAL[m]||{})[f];return v==null?(DEF[m]||{})[f]:v};
const N19=[1,2,3,4,5,6,7,8,9];
function preMod(c,id,n,def){return{c,id,n,
 st:()=>S.pre[id]&&S.pre[id].on?1:0,
 sub:()=>{const p=S.pre[id];return p&&p.on?'вкл':p&&p.ds=='-'?'нужен адрес':''},
 tg:on=>call('pre',{id,on:on?1:0,a:gv(id,'a'),s:gv(id,'s'),v:gv(id,'v')}),live:1,
 set:[{id:'a',l:'адрес',t:'in',d:'',ph:'hex функции'},{id:'s',l:'слот',t:'in',d:'',ph:'vtable GameMode'},{id:'v',l:'значение',t:'in',d:def},{t:'note',f:()=>(S.pre[id]||{}).hint||''}]}}
const MODS=[
{c:'Мир',id:'md',n:'Multiple destroy',st:()=>S.zone.startsWith('1')?1:0,sub:()=>S.zone.startsWith('1')?S.zone.trim().split(' ').slice(1).join('x'):'',
 tg:on=>call('zone',on?{on:1,w:gv('md','w'),h:gv('md','h'),d:gv('md','d')}:{on:0}),live:1,
 set:[{id:'w',l:'Ш',t:'sel',o:N19,d:3},{id:'h',l:'В',t:'sel',o:N19,d:3},{id:'d',l:'Г',t:'sel',o:[1,2,3,4,5],d:1},
 {t:'btns',b:[['1x1',{w:1,h:1,d:1}],['3x2',{w:3,h:2,d:1}],['3x3',{w:3,h:3,d:1}],['5x5',{w:5,h:5,d:1}],['3x3x3',{w:3,h:3,d:3}]]},
 {t:'note',x:'Только локальный мир. Ш × В в плоскости грани, Г вглубь. Адрес destroyBlock ищется сам.'}]},
{c:'Мир',id:'mp',n:'Multiple place',st:()=>S.place.startsWith('1')?1:0,sub:()=>S.place.startsWith('1')?S.place.trim().split(' ').slice(1).join('x'):'',
 tg:on=>call('place',on?{on:1,w:gv('mp','w'),h:gv('mp','h'),s:gv('mp','s')}:{on:0}),live:1,
 set:[{id:'w',l:'Ш',t:'sel',o:N19,d:3},{id:'h',l:'В',t:'sel',o:N19,d:3},{id:'s',l:'слот',t:'sel',o:[6,7,8],d:7},
 {t:'btns',b:[['3x1',{w:3,h:1}],['3x3',{w:3,h:3}],['5x5',{w:5,h:5}],['9x9',{w:9,h:9}]]},
 {t:'note',x:'Ставит пластину вокруг блока. Если не ставит: слот 6 или 8. Глубины нет.'}]},
preMod('Мир','timefreeze','Заморозка времени','0'),
preMod('Мир','weather','Погода: заморозка','0'),
preMod('Игрок','reach','Reach','7.0'),
preMod('Игрок','breakspd','Скорость слома','1000.0'),
preMod('Игрок','fly','Полёт','1'),
preMod('Игрок','noclip','Noclip','1'),
{c:'Камера',id:'fov',n:'FOV changer',st:()=>S.fov.includes('заморожено')&&!ZM?1:0,sub:()=>S.fov.startsWith('не привязано')?'не привязано':'',
 tg:on=>call(on?'csapply':'csstop',{s:'fov',v:gv('fov','v')}),live:1,
 set:[{id:'v',l:'FOV',t:'in',d:'70'},{id:'a',l:'адрес',t:'in',d:'',ph:'hex для привязки'},
 {t:'btns',b:[['Привязать',()=>call('csbind',{s:'fov',a:gv('fov','a')})],['Статус',()=>call('csinfo',{s:'fov'})]]},
 {t:'note',x:'Mem: найди FOV как float, смени в настройках, сузь, впиши адрес и «Привязать». Зажим 30–110 снимается в «Лимиты».'}]},
{c:'Камера',id:'zoom',n:'Зум',st:()=>ZM?1:0,sub:()=>ZM?gv('zoom','v'):'',
 tg:async on=>{ZM=on?1:0;return call('csapply',{s:'fov',v:on?gv('zoom','v'):gv('fov','v')})},live:1,
 set:[{id:'v',l:'FOV зума',t:'in',d:'30'},{t:'note',x:'Игра зажимает FOV снизу на 30. Ниже получится после снятия лимита. Нужна привязка FOV.'}]},
{c:'Камера',id:'chunk',n:'Чанки',st:()=>S.chunk.includes('заморожено')?1:0,sub:()=>S.chunk.startsWith('не привязано')?'не привязано':'',
 tg:on=>call(on?'csapply':'csstop',{s:'chunk',v:gv('chunk','v')}),live:1,
 set:[{id:'v',l:'чанков',t:'in',d:'16'},{id:'a',l:'адрес',t:'in',d:'',ph:'hex для привязки'},
 {t:'btns',b:[['Привязать',()=>call('csbind',{s:'chunk',a:gv('chunk','a')})],['Статус',()=>call('csinfo',{s:'chunk'})]]},
 {t:'note',x:'1–96. В настройках UI может показывать другое число, а в игре дальность будет такой.'}]},
preMod('Камера','vibrant','Vibrant Visuals','1'),
preMod('Камера','viewdist','Лимит чанков (хук)','96'),
{c:'Система',id:'lim',n:'Лимиты (константы)',k:'set',
 set:[{id:'f1',l:'число 1',t:'in',d:'30'},{id:'f2',l:'число 2',t:'in',d:'110'},{id:'t',l:'тип',t:'sel',o:[['f','float'],['i','int']],d:'f'},
 {t:'btns',b:[['Найти пару',()=>call('fpair',{f1:gv('lim','f1'),f2:gv('lim','f2'),t:gv('lim','t')})],['Только число 1',()=>call('fpair',{f1:gv('lim','f1'),t:gv('lim','t')})]]},
 {id:'a',l:'адрес',t:'in',d:'',ph:'hex из списка'},{id:'n',l:'новое',t:'in',d:''},
 {t:'btns',b:[['Применить',()=>call('fset',{a:gv('lim','a'),f:gv('lim','n'),t:gv('lim','t'),k:0})],['Запомнить',()=>call('fset',{a:gv('lim','a'),f:gv('lim','n'),t:gv('lim','t'),k:1})],['Откат',()=>call('undo',{a:gv('lim','a')})]]},
 {t:'note',x:'По умолчанию ищет зажим FOV (30 и 110 рядом). Для чанков тип int и числа из своих находок. Литерал общий для всех мест, где он читается.'}]},
{c:'Система',id:'gms',n:'Слоты GameMode',k:'act',run:()=>call('gmslots',{n:40})},
{c:'Система',id:'hk',n:'Хуки и патчи',k:'set',
 set:[{t:'btns',b:[['Список хуков',()=>call('hooks',{})],['Запомнить',()=>call('hooksave',{})],['Загрузить',()=>call('hookload',{})]]},
 {t:'btns',b:[['Удалить сохранённые',()=>call('hookclear',{})],['Патчи сессии',()=>call('patches',{})],['Сохранённые патчи',()=>call('saved',{})]]},
 {t:'note',x:'Запомненные хуки ставятся сами при старте игры, если байты функции те же.'}]}
];
const CATS=['Мир','Игрок','Камера','Global','Система'];
const DEF={};for(const m of MODS){DEF[m.id]={};for(const f of m.set||[])if(f.id)DEF[m.id][f.id]=f.d==null?'':f.d}
function GL(){return S.fn.map(r=>{const prof=r.st[0]=='P',s=prof?r.st[1]:r.st;return{c:'Global',id:'fn:'+r.n,n:r.n,
 st:()=>s=='1'?1:s=='2'?.5:0,sub:()=>(prof?'набор ':'')+(s=='3'?'др. версия':s=='2'?'частично':''),
 tg:async on=>{if(s=='3'){log('байты не совпали: функция для другой версии игры');return}return call(on?'fnon':'fnoff',{n:r.n,k:UI.keep?1:0})}}})}
const ALL=()=>MODS.concat(GL());
async function run(m){if(m.k=='act'){m.run();return}if(m.k=='set'){toggleOpen(m);return}const on=m.st()!==1;await m.tg(on);await refresh()}
function liveSend(m){if(m.live&&m.st&&m.st()===1)m.tg(true).then(refresh)}
function toggleOpen(m){OPN[m.id]=!OPN[m.id];SV('mggPcOpen',OPN);const r=ROW[m.id];if(r&&r.set){r.set.hidden=!OPN[m.id];if(r.ar)r.ar.classList.toggle('o',!!OPN[m.id])}rep()}
function syncInputs(m){const r=ROW[m.id];if(!r||!r.set)return;r.set.querySelectorAll('[data-f]').forEach(e=>{e.value=gv(m.id,e.dataset.f)})}
function mkSet(m){const box=document.createElement('div');box.className='set';box.hidden=!OPN[m.id];
 for(const f of m.set||[]){
  if(f.t=='note'){const s=document.createElement('small');s.textContent=f.x||'';if(f.f)NOTES.push([s,f.f]);box.appendChild(s);continue}
  if(f.t=='btns'){const d=document.createElement('div');d.className='bt';for(const b of f.b){const e=document.createElement('button');e.textContent=b[0];
   e.onclick=()=>{if(typeof b[1]=='function'){b[1]()}else{VAL[m.id]=Object.assign(VAL[m.id]||{},b[1]);SV('mggPcVal',VAL);syncInputs(m);liveSend(m)}};d.appendChild(e)}box.appendChild(d);continue}
  const lb=document.createElement('label'),sp=document.createElement('span');sp.textContent=f.l;lb.appendChild(sp);let el;
  if(f.t=='sel'){el=document.createElement('select');for(const o of f.o){const op=document.createElement('option');op.value=Array.isArray(o)?o[0]:o;op.textContent=Array.isArray(o)?o[1]:o;el.appendChild(op)}}
  else{el=document.createElement('input');el.placeholder=f.ph||''}
  el.dataset.f=f.id;el.value=gv(m.id,f.id);
  el.onchange=()=>{(VAL[m.id]=VAL[m.id]||{})[f.id]=el.value.trim();SV('mggPcVal',VAL);liveSend(m)};
  lb.appendChild(el);box.appendChild(lb)}
 return box}
function build(){const pl=$('pl');pl.textContent='';ROW={};NOTES=[];WINS={};const mods=ALL();
 for(const c of CATS){const ms=mods.filter(m=>m.c==c);if(!ms.length)continue;
  const w=document.createElement('div');w.className='win';const hd=document.createElement('div');hd.className='hd';hd.innerHTML='<span></span><i></i>';hd.firstChild.textContent=c;w.appendChild(hd);
  const body=document.createElement('div');body.hidden=!!COL[c];w.appendChild(body);
  for(const m of ms){const row=document.createElement('div');row.className='mod'+(m.k=='act'?' act':'');row.innerHTML='<span class=n></span><small class=sb></small>';row.querySelector('.n').textContent=m.n;
   row.onclick=()=>{w.style.zIndex=++ZI;run(m)};const R={el:row,sb:row.querySelector('.sb'),m};
   if(m.set&&m.set.length){const ar=document.createElement('div');ar.className='ar'+(OPN[m.id]?' o':'');ar.textContent='›';ar.onclick=e=>{e.stopPropagation();toggleOpen(m)};row.appendChild(ar);R.ar=ar;
    body.appendChild(row);R.set=mkSet(m);body.appendChild(R.set)}else body.appendChild(row);
   ROW[m.id]=R}
  WINS[c]={w,hd,body,cnt:hd.querySelector('i'),ms};pl.appendChild(w);dragInit(c)}
 autoPlace();applySearch();paint();rep()}
function autoPlace(){const cv=$('cv'),cols=Math.max(1,Math.floor((cv.clientWidth/UI.zm-8)/158)),h=new Array(cols).fill(8);
 for(const c of CATS){const o=WINS[c];if(!o)continue;let p=POS[c];
  if(!p){let k=0;for(let i=1;i<cols;i++)if(h[i]<h[k])k=i;p=[8+k*158,h[k]];h[k]+=o.w.offsetHeight+8}
  o.w.style.left=p[0]+'px';o.w.style.top=p[1]+'px'}}
function dragInit(c){const o=WINS[c],hd=o.hd;let sx,sy,ox,oy,mv=false,on=false;
 hd.onpointerdown=e=>{o.w.style.zIndex=++ZI;on=true;mv=false;sx=e.clientX;sy=e.clientY;ox=o.w.offsetLeft;oy=o.w.offsetTop;hd.setPointerCapture(e.pointerId)};
 hd.onpointermove=e=>{if(!on)return;const dx=(e.clientX-sx)/UI.zm,dy=(e.clientY-sy)/UI.zm;if(Math.abs(dx)+Math.abs(dy)>4)mv=true;if(mv){o.w.style.left=Math.max(0,ox+dx)+'px';o.w.style.top=Math.max(0,oy+dy)+'px'}};
 hd.onpointerup=e=>{if(!on)return;on=false;if(mv){POS[c]=[o.w.offsetLeft,o.w.offsetTop];SV('mggPcPos',POS)}else{COL[c]=!COL[c];SV('mggPcCol',COL);o.body.hidden=!!COL[c]}rep()}}
function paint(){for(const c of CATS){const o=WINS[c];if(!o)continue;let on=0,tot=0;
  for(const m of o.ms){const r=ROW[m.id];if(!r)continue;const s=m.st?m.st():0;
   if(m.st){tot++;if(s===1)on++}
   r.el.classList.toggle('on',s===1);r.el.classList.toggle('mid',s===.5);r.sb.textContent=m.sub?m.sub():''}
  o.cnt.textContent=tot?on+'/'+tot:''}
 for(const n of NOTES)n[0].textContent=n[1]()}
function applySearch(){const q=$('q').value.trim().toLowerCase();
 for(const c of CATS){const o=WINS[c];if(!o)continue;let any=false;
  for(const m of o.ms){const r=ROW[m.id],ok=!q||m.n.toLowerCase().includes(q);r.el.style.display=ok?'':'none';if(r.set)r.set.style.display=ok?'':'none';if(ok)any=true}
  o.w.style.display=any?'':'none';if(q&&any)o.body.hidden=false;else if(!q)o.body.hidden=!!COL[c]}}
async function refresh(){
 const [z,p,pl,f,ch,fl]=await Promise.all([api('zone',{on:2}),api('place',{on:2}),api('prelist'),api('csst',{s:'fov'}),api('csst',{s:'chunk'}),api('fnlist')]);
 S.zone=z.trim()||'0';S.place=p.trim()||'0';S.fov=f;S.chunk=ch;S.pre={};
 for(const ln of pl.trim().split('\n')){const c=ln.split('\t');if(c.length>=7)S.pre[c[0]]={on:c[2]=='1',ds:c[3],dv:c[4],off:c[5],hint:c[6]}}
 const rows=[];if(!fl.startsWith('пусто')&&fl.indexOf('\t')>=0)for(const ln of fl.trim().split('\n')){const c=ln.split('\t');if(c.length>=3)rows.push({n:c[0],st:c[1],c:c[2]})}
 const sig=JSON.stringify(rows.map(r=>r.n+r.st));S.fn=rows;if(sig!==FNSIG||!Object.keys(WINS).length){FNSIG=sig;build()}else paint()}
function ui(){const R=document.documentElement.style;R.setProperty('--zm',UI.zm);R.setProperty('--a',UI.a);R.setProperty('--hd',UI.hd);$('hdc').value=UI.hd;$('keep').checked=!!UI.keep;SV('mggPcUi',UI)}
$('zm1').onclick=()=>{UI.zm=Math.max(.6,+(UI.zm-.1).toFixed(2));ui()};
$('zm2').onclick=()=>{UI.zm=Math.min(1.8,+(UI.zm+.1).toFixed(2));ui()};
$('op').onclick=()=>{const a=[.5,.7,.88,1];UI.a=a[(a.indexOf(UI.a)+1)%a.length]||.88;ui()};
$('hdc').oninput=e=>{UI.hd=e.target.value;ui()};
$('keep').onchange=e=>{UI.keep=e.target.checked?1:0;ui()};
$('rst').onclick=()=>{POS={};SV('mggPcPos',POS);autoPlace()};
$('lg').onclick=()=>document.body.classList.toggle('lb');
$('log').onclick=()=>document.body.classList.toggle('lb');
$('cpy').onclick=()=>{const t=$('log').textContent;if(window.MGGJ&&MGGJ.copy)MGGJ.copy(t);else if(navigator.clipboard)navigator.clipboard.writeText(t)};
$('q').oninput=()=>{applySearch();rep()};
$('gear').onclick=()=>{document.documentElement.classList.toggle('tb');rep()};
addEventListener('resize',()=>{autoPlace();rep()});setInterval(rep,500);
if(EMB){$('cls').hidden=false;$('cls').onclick=()=>parent.postMessage('pcclose','*')}
ui();refresh();setInterval(()=>{if(!document.hidden)refresh()},5000);
</script></body></html>
)MGP";


static Str route(const Str &path, const Params &q) {
    std::lock_guard<std::mutex> lk(g_mu);
    if (path == "ls" || path == "cat" || path == "grep" || path == "setkey" || path == "freplace" || path == "frestore") return fileRoute(path, q);
    if (path == "mscan" || path == "mnext" || path == "mlist" || path == "mreset" || path == "mset" || path == "mdump" || path == "mfreeze" || path == "mfrlist" || path == "munfreeze" || path == "mwatch" || path == "mwlog" || path == "mwstop") return memRoute(path, q);
    if (path == "findopt" || path == "status" || path == "unlock" || path == "reenable" || path == "rollall") return miscRoute(path, q);
    if (path == "libs" || path == "libsel") return libRoute(path, q);
    if (path.compare(0, 2, "cs") == 0) return csRoute(path, q);
    if (path.compare(0, 3, "dex") == 0) return dexRoute(path, q);
    if (path == "wplayer") return worldPlayer();
    if (path == "wmob") return worldMob();
    if (path == "wblock") return worldBlock();
    if (path == "wcfg") return worldCfg();
    { Str ho; if (helperRoute(path, q, ho)) return ho; }
    Img im;
    if (!loadImg(im)) return "библиотека " + g_lib + " не найдена в /proc/self/maps (выбери другую во вкладке Lib)\n";
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
    if (path == "uimode") {                                        // Functions second menu: off | pc (файл mgg_ui.txt, его читает и оверлей-кнопка F)
        Str f = dataDir() + "/mgg_ui.txt", m = P(q, "m");
        if (!m.empty()) {
            m = m == "pc" ? "pc" : "off";
            FILE *fp = fopen(f.c_str(), "w"); if (!fp) return "не могу писать " + f + "\n";
            fputs(m.c_str(), fp); fclose(fp);
            return m + "\n";
        }
        char b[16] = {0}; FILE *fp = fopen(f.c_str(), "r");
        if (fp) { size_t n = fread(b, 1, sizeof b - 1, fp); b[n] = 0; fclose(fp); }
        return strncmp(b, "pc", 2) == 0 ? "pc\n" : "off\n";
    }
    if (path == "fpair") return fPair(im, q);
    if (path == "fset") {                                          // записать слово-константу: a (hex, кратно 4), f (новое), t=f|i, o (ожидаемое старое, необязательно), k=1 запомнить
        if (!hexNum(q, "a", a)) return "нужен a (hex)\n";
        if (a & 3) return "адрес должен быть кратен 4 (литерал/слово)\n";
        bool isf = P(q, "t", "f") != "i"; uint32_t w = 0, w0 = 0;
        if (!numWord(P(q, "f"), isf, w)) return "нужно новое значение f\n";
        if (!P(q, "o").empty()) {
            if (!numWord(P(q, "o"), isf, w0)) return "o не число\n";
            if (!segAt(im, im.base + a, 4) || rd32(im.base + a) != w0) return "по адресу сейчас другое значение: не пишу\n";
        }
        std::vector<uint8_t> b(4); memcpy(b.data(), &w, 4);
        return doPatch(im, a, b, P(q, "k") == "1");
    }
    if (path == "sym") return symRoute(im, q);
#ifdef MGG_HAS_DOBBY
    if (path == "hooks") return hooksList();
    if (path == "hook") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        uintptr_t v = 0; hexNum(q, "v", v);
        Str t = P(q, "t", "auto"); int isa = t == "thumb" ? 1 : t == "arm" ? 2 : 0;
        Str msg; int id = hookInstall(im, a, hkMode(P(q, "m", "log")), (int)decNum(q, "n", 0), v, msg, isa);
        if (id < 0) return msg + "\n";
        return "хук #" + std::to_string(id) + " на " + hx(g_slots[id].off) + (g_slots[id].arm ? " (ARM)" : " (Thumb)") + "\n";
    }
    if (path == "zone") {                                          // слом области: w x h (в плоскости грани), d вглубь; on=0 выключить, on=2 статус
        int ex = -1; for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].mode == 5) ex = i;
        Str on = P(q, "on", "1");
        if (on == "2") return ex < 0 ? Str("0\n") : "1 " + std::to_string(g_slots[ex].val & 0xFF) + " " + std::to_string((g_slots[ex].val >> 8) & 0xFF) + " " + std::to_string((g_slots[ex].val >> 16) & 0xFF) + "\n";
        if (on == "0") { if (ex < 0) return "зона не включена\n"; g_slots[ex].mode = 0; return "выключено: Multiple destroy\n"; }   // хук остаётся стоять в режиме лога (снимать Dobby-хук на горячую не нужно)
        size_t w = decNum(q, "w", 3), h = decNum(q, "h", 3), d = decNum(q, "d", 1);
        w = w < 1 ? 1 : w > 9 ? 9 : w; h = h < 1 ? 1 : h > 9 ? 9 : h; d = d < 1 ? 1 : d > 5 ? 5 : d;
        if (w * h * d > 200) return "слишком много блоков (макс. 200)\n";
        uintptr_t val = w | (h << 8) | (d << 16), off = 0;
        if (!hexNum(q, "a", off)) { Str why; off = findDestroyBlock(im, why); if (!off) return why; }
        Str tag = std::to_string(w) + "x" + std::to_string(h) + "x" + std::to_string(d);
        if (ex >= 0) { g_slots[ex].val = val; return "включено: Multiple destroy " + tag + "\n"; }
        for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].off == (off & ~(uintptr_t)1)) {   // на destroyBlock уже стоит хук (например старый «слом вокруг»): переиспользуем
            g_slots[i].mode = 5; g_slots[i].val = val; return "включено: Multiple destroy " + tag + " (хук #" + std::to_string(i) + ")\n";
        }
        Str msg; int id = hookInstall(im, off, 5, 0, val, msg, 0);
        if (id < 0) return msg + "\n";
        return "включено: Multiple destroy " + tag + " (хук #" + std::to_string(id) + " на " + hx(g_slots[id].off) + ")\n";
    }
    if (path == "place") {                                         // Multiple place: ставит пластину w x h на грани; on=0 выключить, on=2 статус; s — слот vtable GameMode (7 = buildBlock)
        int ex = -1; for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].mode == 6) ex = i;
        Str on = P(q, "on", "1");
        if (on == "2") return ex < 0 ? Str("0\n") : "1 " + std::to_string(g_slots[ex].val & 0xFF) + " " + std::to_string((g_slots[ex].val >> 8) & 0xFF) + "\n";
        if (on == "0") { if (ex < 0) return "Multiple place не включён\n"; g_slots[ex].mode = 0; return "выключено: Multiple place\n"; }
        size_t w = decNum(q, "w", 3), h = decNum(q, "h", 3), sl = decNum(q, "s", 7);
        w = w < 1 ? 1 : w > 9 ? 9 : w; h = h < 1 ? 1 : h > 9 ? 9 : h; sl = sl < 4 ? 4 : sl > 12 ? 12 : sl;
        uintptr_t val = w | (h << 8), off = 0;
        if (!hexNum(q, "a", off)) { Str why; off = findGameModeSlot(im, (int)sl, why); if (!off) return why; }
        Str tag = std::to_string(w) + "x" + std::to_string(h);
        if (ex >= 0 && g_slots[ex].off == (off & ~(uintptr_t)1)) { g_slots[ex].val = val; return "включено: Multiple place " + tag + "\n"; }
        if (ex >= 0) g_slots[ex].mode = 0;                         // слот vtable сменили: старый хук остаётся в режиме лога
        for (int i = 0; i < 16; i++) if (g_slots[i].used && g_slots[i].off == (off & ~(uintptr_t)1)) {
            g_slots[i].mode = 6; g_slots[i].val = val; return "включено: Multiple place " + tag + " (хук #" + std::to_string(i) + ")\n";
        }
        Str msg; int id = hookInstall(im, off, 6, 0, val, msg, 0);
        if (id < 0) return msg + "\n";
        return "включено: Multiple place " + tag + " (слот " + std::to_string(sl) + ", хук #" + std::to_string(id) + " на " + hx(g_slots[id].off) + ")\n";
    }
    if (path == "gmslots") return gmSlots(im, decNum(q, "n", 40));
    if (path == "prelist") return preList();
    if (path == "pre") return preSet(im, q);
    if (path == "hooksave") return hooksSave();
    if (path == "hookload") return hooksApply(im);
    if (path == "hookclear") { remove(hooksFile().c_str()); return "сохранённые хуки удалены (уже стоящие остаются до перезапуска игры)\n"; }
    if (path == "hookset" || path == "unhook") {
        size_t id = decNum(q, "id", 99);
        if (id >= 16 || !g_slots[id].used) return "нет такого хука\n";
        Slot &s = g_slots[id];
        if (path == "unhook") { MGG_UNHOOK(s.target); s.used = false; return "снят\n"; }
        if (P(q, "reset") == "1") { s.calls = 0; s.t0 = hkNow(); for (int k = 0; k < 8; k++) { s.seen[k] = 0; s.seenN[k] = 0; } return "счётчики сброшены\n"; }
        uintptr_t v = 0; hexNum(q, "v", v);
        s.val = v; s.mode = hkMode(P(q, "m", "log")); s.arg = (int)decNum(q, "n", 0); if (s.arg > 7) s.arg = 7;
        return "режим обновлён\n";
    }
#else
    if (path == "hooks" || path == "hook" || path == "hookset" || path == "unhook" || path == "hooksave" || path == "hookload" || path == "hookclear" || path == "zone" || path == "place" || path == "gmslots" || path == "prelist" || path == "pre")
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
    if (path == "/pc") { reply(c, 200, "text/html", kPcPage); return; }
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
