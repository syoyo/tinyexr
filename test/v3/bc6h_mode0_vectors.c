/* BC6H mode-0 block encoder vectors: C vs Lean.
 *
 * `tc_bc6h_mode0_uf16` is static, so this translation unit includes it.
 * Per line: `m0 <16 x 3 float bits> | <ok|fail> <16 block bytes> <sse>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x13579bdf2468ace0ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float bits_to_f(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }
int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 400; s++) {
        uint32_t px[16][3];
        uint8_t blk[16];
        float fpix[16][3];
        /* Mode 0 stores 5-bit signed deltas from the region-0 low endpoint, so
         * only blocks whose values are close in the quantised (half) domain can
         * match. Step the float mantissa in units of 0x2000, which moves the
         * HALF mantissa by 1 and the BC6H quantised value by ~1. */
        {
            uint32_t e = 120u + (uint32_t)(rnd() % 16u);
            uint32_t mbase = (uint32_t)(rnd() % 200u) * 0x2000u;
            int spread;
            if (s % 4 == 0) spread = 0;
            else if (s % 4 == 3) spread = 400 + (int)(rnd() % 800u); /* mostly no-fit */
            else spread = (int)(rnd() % 9u);
            for (int i = 0; i < 16; i++) {
                for (int c = 0; c < 3; c++) {
                    int32_t d = (spread == 0) ? 0 : (int32_t)(rnd() % (uint32_t)(2 * spread + 1)) - spread;
                    int64_t m = (int64_t)mbase + (int64_t)d * 0x2000;
                    if (m < 0) m = 0;
                    if (m > 0x7fffff) m = 0x7fffff;
                    px[i][c] = (e << 23) | (uint32_t)m;
                }
            }
        }
        for (int i = 0; i < 16; i++)
            for (int c = 0; c < 3; c++) fpix[i][c] = bits_to_f(px[i][c]);
        {
            uint64_t err = tc_bc6h_mode0_uf16(fpix, blk);
            fprintf(out, "m0");
            for (int i = 0; i < 16; i++)
                for (int c = 0; c < 3; c++) fprintf(out, " %08x", px[i][c]);
            if (err == (uint64_t)-1) {
                fprintf(out, " | fail\n");
            } else {
                fprintf(out, " | ok");
                for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
                fprintf(out, " %llu\n", (unsigned long long)err);
            }
        }
    }
    fclose(out);
    return 0;
}
