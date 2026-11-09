/* BC6H mode-1/9 block encoder vectors: C vs Lean.
 *
 * Per line: `m<1|9> <16 x 3 float bits> | ok <16 bytes> <sse>` / `... | fail`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x77e1d3c5b9a70f21ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float F(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }

/* Tight blocks keep one exponent so the quantised spread stays inside the
 * delta limits; wide blocks vary the exponent so the region deltas exceed
 * them and exercise the no-fit path. */
static void make_block(uint32_t px[16][3], float fp[16][3], int tight,
                       uint32_t hi_exp_span) {
    uint32_t e = 120u + (uint32_t)(rnd() % 18u);
    uint32_t mbase = (uint32_t)(rnd() % 200u) * 0x4000u;
    for (int i = 0; i < 16; i++) {
        for (int c = 0; c < 3; c++) {
            uint32_t ee = e;
            uint32_t m;
            if (tight) {
                int32_t d = (int32_t)(rnd() % 9u) - 4;
                int64_t mm = (int64_t)mbase + (int64_t)d * 0x4000;
                if (mm < 0) mm = 0;
                if (mm > 0x7fffff) mm = 0x7fffff;
                m = (uint32_t)mm;
            } else {
                ee = 118u + (uint32_t)(rnd() % hi_exp_span);
                m = (uint32_t)(rnd() & 0x7fffffu);
            }
            px[i][c] = (ee << 23) | m;
            fp[i][c] = F(px[i][c]);
        }
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 260; s++) {
        uint32_t px[16][3];
        float fp[16][3];
        uint8_t blk[16];
        uint64_t err;
        make_block(px, fp, (s % 2) == 0, 16u);
        err = tc_bc6h_mode1_uf16(fp, blk);
        fprintf(out, "m1");
        for (int i = 0; i < 16; i++)
            for (int c = 0; c < 3; c++) fprintf(out, " %08x", px[i][c]);
        if (err == (uint64_t)-1) fprintf(out, " | fail\n");
        else {
            fprintf(out, " | ok");
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
            fprintf(out, " %llu\n", (unsigned long long)err);
        }
    }
    /* Mode 9: 6-bit explicit endpoints; never no-fit. */
    for (int s = 0; s < 260; s++) {
        uint32_t px[16][3];
        float fp[16][3];
        uint8_t blk[16];
        uint64_t err;
        make_block(px, fp, (s % 2) == 0, 8u);
        err = tc_bc6h_mode9_uf16(fp, blk);
        fprintf(out, "m9");
        for (int i = 0; i < 16; i++)
            for (int c = 0; c < 3; c++) fprintf(out, " %08x", px[i][c]);
        if (err == (uint64_t)-1) fprintf(out, " | fail\n");
        else {
            fprintf(out, " | ok");
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
            fprintf(out, " %llu\n", (unsigned long long)err);
        }
    }
    fclose(out);
    return 0;
}
