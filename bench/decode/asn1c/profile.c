/* Where asn1c's time goes: decode and free timed apart, and heap calls
 * counted by wrapping the allocator at link time (see the Makefile).
 *
 *   profile_asn1c DIR ROUNDS [TYPE]    TYPE as for bench_asn1c, DL-DCCH-Message if left out
 *
 * Built with -DBUMP (profile_asn1c_bump), every allocation instead comes from
 * an arena that is reset after each message and free does nothing: what
 * asn1c's decoding costs without the allocator. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dirent.h>

#include "BCCH-BCH-Message.h"
#include "BCCH-DL-SCH-Message.h"
#include "DL-CCCH-Message.h"
#include "DL-DCCH-Message.h"
#include "PCCH-Message.h"
#include "UL-CCCH-Message.h"
#include "UL-DCCH-Message.h"
#include "uper_decoder.h"

static const struct { const char *name; asn_TYPE_descriptor_t *def; } types[] = {
    {"DL-DCCH-Message", &asn_DEF_DL_DCCH_Message},
    {"UL-DCCH-Message", &asn_DEF_UL_DCCH_Message},
    {"PCCH-Message", &asn_DEF_PCCH_Message},
    {"BCCH-BCH-Message", &asn_DEF_BCCH_BCH_Message},
    {"BCCH-DL-SCH-Message", &asn_DEF_BCCH_DL_SCH_Message},
    {"UL-CCCH-Message", &asn_DEF_UL_CCCH_Message},
    {"DL-CCCH-Message", &asn_DEF_DL_CCCH_Message},
};

static unsigned long n_malloc, n_calloc, n_realloc, n_free;
void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void __real_free(void *);
#ifdef BUMP
static char *arena, *top;
static int bumping;
static void *bump(size_t s) {
    size_t *h = (size_t *)top;
    *h = s;
    top += (sizeof(size_t) + s + 15) & ~(size_t)15;
    return h + 1;
}
void *__wrap_malloc(size_t s) { n_malloc++; return bumping ? bump(s) : __real_malloc(s); }
void *__wrap_calloc(size_t a, size_t b) {
    n_calloc++;
    if (!bumping) return __real_calloc(a, b);
    void *p = bump(a * b);
    memset(p, 0, a * b);
    return p;
}
void *__wrap_realloc(void *p, size_t s) {
    n_realloc++;
    if (!bumping) return __real_realloc(p, s);
    void *q = bump(s);
    if (p) memcpy(q, p, ((size_t *)p)[-1] < s ? ((size_t *)p)[-1] : s);
    return q;
}
void __wrap_free(void *p) { if (p) n_free++; if (!bumping) __real_free(p); }
#else
void *__wrap_malloc(size_t s) { n_malloc++; return __real_malloc(s); }
void *__wrap_calloc(size_t a, size_t b) { n_calloc++; return __real_calloc(a, b); }
void *__wrap_realloc(void *p, size_t s) { n_realloc++; return __real_realloc(p, s); }
void __wrap_free(void *p) { if (p) n_free++; __real_free(p); }
#endif

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000u + t.tv_nsec;
}

int main(int argc, char **argv) {
    const char *ty = argc > 3 ? argv[3] : "DL-DCCH-Message";
    asn_TYPE_descriptor_t *def = NULL;
    for (size_t i = 0; i < sizeof types / sizeof *types; i++)
        if (!strcmp(types[i].name, ty)) def = types[i].def;
    if (!def) { fprintf(stderr, "%s: not one of the seven channel messages\n", ty); return 1; }
    DIR *d = opendir(argv[1]);
    int rounds = atoi(argv[2]);
    size_t n = 0, cap = 1024;
    uint8_t **buf = __real_malloc(cap * sizeof *buf);
    size_t *len = __real_malloc(cap * sizeof *len);
    struct dirent *e;
    while ((e = readdir(d))) {
        size_t l = strlen(e->d_name);
        if (l < 5 || strcmp(e->d_name + l - 5, ".uper")) continue;
        if (n == cap) {
            cap *= 2;
            buf = __real_realloc(buf, cap * sizeof *buf);
            len = __real_realloc(len, cap * sizeof *len);
        }
        char path[4096];
        snprintf(path, sizeof path, "%s/%s", argv[1], e->d_name);
        FILE *f = fopen(path, "rb");
        fseek(f, 0, SEEK_END);
        len[n] = ftell(f);
        rewind(f);
        buf[n] = __real_malloc(len[n] + 1);
        if (fread(buf[n], 1, len[n], f) != len[n]) return 1;
        fclose(f);
        n++;
    }
    closedir(d);
    /* decode and free each message in turn, as bench.c does, timing the
     * two apart; the clock's own cost is measured and taken off */
#ifdef BUMP
    arena = top = __real_malloc(64 << 20);
    bumping = 1;
#endif
    uint64_t best_dec = ~0ull, best_free = ~0ull, clk = ~0ull;
    unsigned long allocs = 0, frees = 0;
    for (int r = 0; r <= rounds; r++) {
        uint64_t dec = 0, fr = 0, c0 = now_ns();
        for (size_t i = 0; i < n; i++) { uint64_t a = now_ns(); dec += now_ns() - a; }
        uint64_t c = now_ns() - c0;
        dec = 0;
        n_malloc = n_calloc = n_realloc = n_free = 0;
        for (size_t i = 0; i < n; i++) {
            void *v = NULL;
            uint64_t t0 = now_ns();
            uper_decode_complete(NULL, def, &v, buf[i], len[i]);
            uint64_t t1 = now_ns();
            ASN_STRUCT_FREE(*def, v);
            uint64_t t2 = now_ns();
#ifdef BUMP
            top = arena;
#endif
            dec += t1 - t0;
            fr += t2 - t1;
        }
        allocs = n_malloc + n_calloc + n_realloc;
        frees = n_free;
        if (r > 0) {
            if (dec < best_dec) best_dec = dec;
            if (fr < best_free) best_free = fr;
            if (c < clk) clk = c;
        }
    }
    double oh = (double)clk / n / 2;  /* one now_ns() pair, per message, is two reads */
    printf("asn1c%s decode %.1f ns/msg, free %.1f ns/msg (clock overhead %.1f taken off each), "
           "%.1f allocations/msg, %.1f frees/msg\n",
#ifdef BUMP
           " (bump)",
#else
           "",
#endif
           (double)best_dec / n - oh, (double)best_free / n - oh, oh,
           (double)allocs / n, (double)frees / n);
    return 0;
}
