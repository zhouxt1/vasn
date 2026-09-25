/* asn1c's decoder for one of the seven NR channel messages, on a directory
 * of UPER messages. TYPE is DL-DCCH-Message if left out.
 *
 *   bench_asn1c DIR ROUNDS [TYPE]
 *   bench_asn1c DIR 0 [TYPE]      list the messages it fails to decode
 *
 * Every message is read into memory first. A round decodes each message once
 * and frees the result, as VUPER's output_time.c does; the time of a round is
 * taken with CLOCK_MONOTONIC around the whole round, not per message. Prints
 * how many messages decoded, and the fastest and median round. */
#define _GNU_SOURCE
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

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

typedef struct { uint8_t *buf; size_t len; char *name; } msg_t;

static int cmp_name(const void *a, const void *b) {
    return strcmp(*(char *const *)a, *(char *const *)b);
}

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}

static size_t load(const char *dir, msg_t **out) {
    DIR *d = opendir(dir);
    if (!d) { perror(dir); exit(1); }
    char **names = NULL;
    size_t n = 0, cap = 0;
    struct dirent *e;
    while ((e = readdir(d))) {
        size_t l = strlen(e->d_name);
        if (l < 5 || strcmp(e->d_name + l - 5, ".uper")) continue;
        if (n == cap) names = realloc(names, (cap = cap ? 2 * cap : 1024) * sizeof *names);
        names[n++] = strdup(e->d_name);
    }
    closedir(d);
    qsort(names, n, sizeof *names, cmp_name);
    msg_t *m = calloc(n, sizeof *m);
    for (size_t i = 0; i < n; i++) {
        char path[4096];
        snprintf(path, sizeof path, "%s/%s", dir, names[i]);
        FILE *f = fopen(path, "rb");
        fseek(f, 0, SEEK_END);
        m[i].len = ftell(f);
        rewind(f);
        m[i].buf = malloc(m[i].len ? m[i].len : 1);
        if (fread(m[i].buf, 1, m[i].len, f) != m[i].len) { perror(path); exit(1); }
        fclose(f);
        m[i].name = names[i];
    }
    free(names);
    *out = m;
    return n;
}

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000u + t.tv_nsec;
}

int main(int argc, char **argv) {
    if (argc != 3 && argc != 4) { fprintf(stderr, "usage: %s DIR ROUNDS [TYPE]\n", argv[0]); return 1; }
    const char *ty = argc == 4 ? argv[3] : "DL-DCCH-Message";
    asn_TYPE_descriptor_t *def = NULL;
    for (size_t i = 0; i < sizeof types / sizeof *types; i++)
        if (!strcmp(types[i].name, ty)) def = types[i].def;
    if (!def) { fprintf(stderr, "%s: not one of the seven channel messages\n", ty); return 1; }
    msg_t *m;
    size_t n = load(argv[1], &m);
    int rounds = atoi(argv[2]);
    if (rounds == 0) {
        for (size_t i = 0; i < n; i++) {
            void *v = NULL;
            asn_dec_rval_t rv = uper_decode_complete(NULL, def, &v, m[i].buf, m[i].len);
            if (rv.code != RC_OK) printf("%s code %d consumed %zu of %zu\n", m[i].name, rv.code, rv.consumed, m[i].len);
            ASN_STRUCT_FREE(*def, v);
        }
        return 0;
    }
    uint64_t *t = calloc(rounds, sizeof *t);
    size_t ok = 0;
    for (int r = -1; r < rounds; r++) {  /* round -1 warms up */
        size_t good = 0;
        uint64_t t0 = now_ns();
        for (size_t i = 0; i < n; i++) {
            void *v = NULL;
            asn_dec_rval_t rv = uper_decode_complete(NULL, def, &v, m[i].buf, m[i].len);
            good += rv.code == RC_OK;
            ASN_STRUCT_FREE(*def, v);
        }
        uint64_t dt = now_ns() - t0;
        if (r >= 0) t[r] = dt;
        ok = good;
    }
    qsort(t, rounds, sizeof *t, cmp_u64);
    printf("asn1c %zu messages, %zu decoded, min %.1f ns/msg, median %.1f ns/msg\n", n, ok,
           (double)t[0] / n, (double)t[rounds / 2] / n);
    return 0;
}
