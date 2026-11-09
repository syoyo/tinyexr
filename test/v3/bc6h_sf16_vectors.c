/* BC6H signed (`sf16`) block encoder vectors: C vs Lean.
 *
 * Per line: `m<mode>s <16 x 3 float bits> | ok <16 bytes> <sse>` / `... | fail`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x3c9a7e15d2b846f1ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float F(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }

/* Tight blocks share one exponent and one sign so the quantised spread stays
 * inside the delta limits; wide blocks vary exponent and sign to push the
 * region deltas past them (no-fit path). */
static void make_block(uint32_t px[16][3], float fp[16][3], int tight,
                       uint32_t unit) {
    uint32_t e = 120u + (uint32_t)(rnd() % 18u);
    uint32_t mbase = (uint32_t)(rnd() % 200u) * unit;
    uint32_t sgn = (rnd() & 1u) ? 0x80000000u : 0u;
    for (int i = 0; i < 16; i++) {
        for (int c = 0; c < 3; c++) {
            uint32_t ee = e;
            uint32_t m;
            uint32_t s = sgn;
            if (tight) {
                int32_t d = (int32_t)(rnd() % 9u) - 4;
                int64_t mm = (int64_t)mbase + (int64_t)d * (int64_t)unit;
                if (mm < 0) mm = 0;
                if (mm > 0x7fffff) mm = 0x7fffff;
                m = (uint32_t)mm;
            } else {
                ee = 118u + (uint32_t)(rnd() % 16u);
                m = (uint32_t)(rnd() & 0x7fffffu);
                s = (rnd() & 1u) ? 0x80000000u : 0u;
            }
            px[i][c] = s | (ee << 23) | m;
            fp[i][c] = F(px[i][c]);
        }
    }
}

static uint64_t run_mode(int mode, const float fp[16][3], uint8_t blk[16]) {
    static const uint8_t dbits234[3][3] = {{5, 4, 4}, {4, 5, 4}, {4, 4, 5}};
    static const uint8_t dbits678[3][3] = {{6, 5, 5}, {5, 6, 5}, {5, 5, 6}};
    switch (mode) {
    case 0: return tc_bc6h_mode0_sf16(fp, blk);
    case 1: return tc_bc6h_mode1_sf16(fp, blk);
    case 2: return tc_bc6h_mode234_sf16(fp, dbits234[0], 2, blk);
    case 3: return tc_bc6h_mode234_sf16(fp, dbits234[1], 3, blk);
    case 4: return tc_bc6h_mode234_sf16(fp, dbits234[2], 4, blk);
    case 5: return tc_bc6h_mode5_sf16(fp, blk);
    case 9: return tc_bc6h_mode9_sf16(fp, blk);
    case 6: return tc_bc6h_mode678_sf16(fp, dbits678[0], 6, blk);
    case 7: return tc_bc6h_mode678_sf16(fp, dbits678[1], 7, blk);
    case 8: return tc_bc6h_mode678_sf16(fp, dbits678[2], 8, blk);
    case 12: return tc_bc6h_mode12_sf16(fp, blk);
    case 13: return tc_bc6h_mode13_sf16(fp, blk);
    default: return (uint64_t)-1;
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const int modes[12] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13};
    for (int mi = 0; mi < 12; mi++) {
        for (int s = 0; s < 150; s++) {
            uint32_t px[16][3];
            float fp[16][3];
            uint8_t blk[16];
            uint64_t err;
            make_block(px, fp, (s % 2) == 0, modes[mi] == 13 ? 0x200u : 0x4000u);
            err = run_mode(modes[mi], fp, blk);
            fprintf(out, "m%ds", modes[mi]);
            for (int i = 0; i < 16; i++)
                for (int c = 0; c < 3; c++) fprintf(out, " %08x", px[i][c]);
            if (err == (uint64_t)-1) fprintf(out, " | fail\n");
            else {
                fprintf(out, " | ok");
                for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
                fprintf(out, " %llu\n", (unsigned long long)err);
            }
        }
    }
    fclose(out);
    return 0;
}
