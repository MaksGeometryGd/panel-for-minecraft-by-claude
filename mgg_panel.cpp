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
#include <utility>
#include <sys/mman.h>
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
    return found ? out : "ссылок не найдено (ищутся только Thumb + literal pool)\n";
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

// ---------------------------------------------------------------- маршруты
static const char *kPage = R"MGG(<!doctype html><html><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1"><title>MGG panel</title>
<style>
body{font:14px system-ui,sans-serif;background:#111;color:#eee;margin:0;padding:10px}
h1{font-size:18px;margin:0 0 6px}h3{font-size:14px;margin:0 0 4px;color:#9ab}
section{background:#1b1b1f;border-radius:10px;padding:8px;margin:8px 0}
input,select,button{font:inherit;padding:8px;border-radius:8px;border:1px solid #444;background:#222;color:#eee;margin:2px 0;width:100%;box-sizing:border-box}
button{background:#3b5bdb;border:0}
pre{white-space:pre-wrap;word-break:break-all;background:#000;padding:8px;border-radius:8px;min-height:90px;max-height:40vh;overflow:auto}
</style></head><body>
<h1>MGG panel</h1>
<pre id=out>Нажми «Инфо»</pre>
<button onclick="cp()">Скопировать результат</button>
<section><h3>Инфо</h3><button onclick="call('info',{})">База и сегменты</button></section>
<section><h3>Сигнатура (hex, ?? — любой байт)</h3>
<input id=sp placeholder="F0 B5 03 AF ?? ??"><select id=sa><option value=0>только код</option><option value=1>вся библиотека</option></select>
<button onclick="call('sig',{p:v('sp'),all:v('sa'),max:50})">Искать</button></section>
<section><h3>Строка</h3><input id=ss placeholder="viewdistance"><select id=si><option value=1>без учёта регистра</option><option value=0>с учётом</option></select>
<button onclick="call('str',{s:v('ss'),i:v('si'),max:60})">Искать</button></section>
<section><h3>Кто использует строку (xref)</h3><input id=xa placeholder="смещение строки, hex"><input id=xn placeholder="длина диапазона (по умолч. 1)">
<button onclick="call('xref',{a:v('xa'),n:v('xn'),max:40})">Найти ссылки</button></section>
<section><h3>Старт функции</h3><input id=fa placeholder="смещение внутри функции, hex">
<button onclick="call('fn',{a:v('fa')})">Найти начало</button></section>
<section><h3>Hex</h3><input id=ha placeholder="смещение, hex"><input id=hn placeholder="байт (десятичное, до 4096)">
<button onclick="call('hex',{a:v('ha'),n:v('hn')||128})">Показать</button></section>
<section><h3>Патч байтов</h3><input id=pa placeholder="смещение, hex"><input id=pb placeholder="байты: 00 20 70 47">
<button onclick="call('patch',{a:v('pa'),b:v('pb')})">Записать</button>
<button onclick="call('undo',{a:v('pa')})">Откатить по смещению</button>
<button onclick="call('patches',{})">Список патчей</button></section>
<section><h3>Хук (нужна сборка с Dobby)</h3><input id=ka placeholder="смещение функции, hex">
<select id=km><option value=log>лог (считать вызовы)</option><option value=ret>вернуть значение (без вызова)</option><option value=set>вызвать и подменить результат</option></select>
<input id=kv placeholder="значение, hex (для ret/set)">
<button onclick="call('hook',{a:v('ka'),m:v('km'),v:v('kv')})">Поставить</button>
<input id=ki placeholder="номер хука">
<button onclick="call('hookset',{id:v('ki'),m:v('km'),v:v('kv')})">Сменить режим</button>
<button onclick="call('unhook',{id:v('ki')})">Снять</button>
<button onclick="call('hooks',{})">Список хуков</button></section>
<script>
const T=new URLSearchParams(location.search).get('t')||'';const out=document.getElementById('out');
function v(i){return document.getElementById(i).value.trim()}
async function call(p,o){const q=new URLSearchParams(o);q.set('t',T);out.textContent='…';
try{const r=await fetch('/api/'+p+'?'+q);out.textContent=await r.text()}catch(e){out.textContent='ошибка: '+e}}
function cp(){const t=out.textContent;if(window.MGGJ){MGGJ.copy(t)}else if(navigator.clipboard){navigator.clipboard.writeText(t)}}
</script></body></html>)MGG";

static Str route(const Str &path, const Params &q) {
    Img im;
    if (!loadImg(im)) return Str("библиотека ") + MGG_TARGET_LIB + " не найдена в /proc/self/maps\n";
    uintptr_t a = 0;

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
        return writeMem(im, a, b, true);
    }
    if (path == "undo") {
        if (!hexNum(q, "a", a)) return "нужен параметр a (hex)\n";
        auto it = g_patches.find(a);
        if (it == g_patches.end()) return "патча по этому смещению нет\n";
        Str r = writeMem(im, a, it->second, false);
        g_patches.erase(it);
        return "откат: " + r;
    }
    if (path == "patches") {
        if (g_patches.empty()) return "патчей нет\n";
        Str o;
        for (auto &kv : g_patches) {
            o += hx(kv.first) + "  оригинал:";
            char b[8];
            for (uint8_t x : kv.second) { snprintf(b, sizeof b, " %02X", x); o += b; }
            o += "\n";
        }
        return o;
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
__attribute__((constructor)) static void mggInit() { std::thread(serve).detach(); }
#endif
