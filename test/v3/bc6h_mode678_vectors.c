/* BC6H mode-6/7/8 block encoder vectors: C vs Lean.
 *
 * Per line: `m<6|7|8> <16 x 3 float bits> | ok <16 bytes> <sse>` / `... | fail`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x51a2c3e4f6071829ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float F(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const int keys[3] = {6, 7, 8};
    static const uint8_t dbits[3][3] = {{6, 5, 5}, {5, 6, 5}, {5, 5, 6}};
    for (int ki = 0; ki < 3; ki++) {
        for (int s = 0; s < 260; s++) {
            uint32_t px[16][3];
            float fp[16][3];
            uint8_t blk[16];
            uint64_t err;
            /* The 8-bit quant step spans ~124.5 half-mantissa units, i.e.
             * ~1M float mantissa units, more than the whole mantissa range at
             * one exponent. Tight blocks (all-fit) therefore live inside one
             * exponent; wide blocks vary the exponent to push the region
             * deltas past the 6/5-bit limits and exercise the no-fit path. */
            uint32_t e = 120u + (uint32_t)(rnd() % 18u);
            int tight = (s % 2) == 0;
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
                        ee = 118u + (uint32_t)(rnd() % 8u);
                        m = (uint32_t)(rnd() & 0x7fffffu);
                    }
                    px[i][c] = (ee << 23) | m;
                    fp[i][c] = F(px[i][c]);
                }
            }
            err = tc_bc6h_mode678_uf16(fp, dbits[ki], keys[ki], blk);
            fprintf(out, "m%d", keys[ki]);
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
