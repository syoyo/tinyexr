/* BC6H mode-2/3/4 block encoder vectors: C vs Lean.
 *
 * Per line: `m<2|3|4> <16 x 3 float bits> | ok <16 bytes> <sse>` / `... | fail`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x0f1e2d3c4b5a6978ULL;
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
    static const int keys[3] = {2, 3, 4};
    static const uint8_t dbits[3][3] = {{5, 4, 4}, {4, 5, 4}, {4, 4, 5}};
    for (int ki = 0; ki < 3; ki++) {
        for (int s = 0; s < 260; s++) {
            uint32_t px[16][3];
            float fp[16][3];
            uint8_t blk[16];
            uint64_t err;
            uint32_t e = 120u + (uint32_t)(rnd() % 18u);
            uint32_t mbase = (uint32_t)(rnd() % 300u) * 0x2000u;
            /* 11-bit quant step ~ 0x2000 mantissa units, so a spread of a few
             * units fits the delta ranges; wider spreads exercise no-fit. */
            int spread = (s % 4 == 3) ? 300 + (int)(rnd() % 600u)
                                      : (int)(rnd() % 12u);
            for (int i = 0; i < 16; i++) {
                for (int c = 0; c < 3; c++) {
                    int32_t d = (spread == 0) ? 0
                        : (int32_t)(rnd() % (uint32_t)(2 * spread + 1)) - spread;
                    int64_t m = (int64_t)mbase + (int64_t)d * 0x2000;
                    if (m < 0) m = 0;
                    if (m > 0x7fffff) m = 0x7fffff;
                    px[i][c] = (e << 23) | (uint32_t)m;
                    fp[i][c] = F(px[i][c]);
                }
            }
            err = tc_bc6h_mode234_uf16(fp, dbits[ki], keys[ki], blk);
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
