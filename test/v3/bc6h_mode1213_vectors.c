/* BC6H mode-12/13 block encoder vectors: C vs Lean.
 *
 * Both encoders are static, so this translation unit includes them.
 * Per line: `m<mode> <16 x 3 float bits> | ok <16 bytes> <sse>` or `... | fail`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0x2468ace013579bdfULL;
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
    for (int mode = 0; mode < 2; mode++) {
        for (int s = 0; s < 300; s++) {
            uint32_t px[16][3];
            float fp[16][3];
            uint8_t blk[16];
            uint64_t err;
            /* A spread in mantissa units of 0x2000 ~= 1 BC6H quant step at
             * 10 bits; mode 13 needs the whole block within +-8 steps, mode 12
             * within +-128. */
            uint32_t e = 118u + (uint32_t)(rnd() % 20u);
            uint32_t mbase = (uint32_t)(rnd() % 400u) * 0x2000u;
            int spread;
            if (mode == 1) spread = (s % 3 == 2) ? (int)(rnd() % 24u) : (int)(rnd() % 5u);
            else spread = (s % 3 == 2) ? 200 + (int)(rnd() % 400u) : (int)(rnd() % 40u);
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
            err = mode ? tc_bc6h_mode13_uf16(fp, blk) : tc_bc6h_mode12_uf16(fp, blk);
            fprintf(out, "m%d", mode ? 13 : 12);
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
