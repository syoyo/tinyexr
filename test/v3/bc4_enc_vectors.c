/* BC4/BC5 encoder vectors: C vs Lean.
 *
 * Emits, per line:
 *   bc4 <16 hex alpha bytes> | <8 encoded bytes>
 *   bc5 <16 hex r bytes> <16 hex g bytes> | <16 encoded bytes>
 *   bc5s <16 hex r bytes> <16 hex g bytes> | <16 encoded bytes>   (SNORM)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng_state = 0x5deece66dULL;
static uint64_t rnd(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* BC4 has an external declaration; BC5's two block encoders are static, so
 * this file includes the translation unit (the block decoders are as well). */
void tc_encode_bc4_block(const uint8_t v[16], uint8_t out[8]);
#include "../../tools/texcomp/src/texcomp_bc5.c"

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    uint8_t a[16], blk[8], rg[16][2], out16[16];
    for (int s = 0; s < 400; s++) {
        for (int i = 0; i < 16; i++)
            a[i] = (s % 5 == 0) ? (uint8_t)(s & 0xff) : (uint8_t)rnd();
        tc_encode_bc4_block(a, blk);
        fprintf(out, "bc4 ");
        for (int i = 0; i < 16; i++) fprintf(out, "%02x", a[i]);
        fprintf(out, " |");
        for (int i = 0; i < 8; i++) fprintf(out, " %02x", blk[i]);
        fprintf(out, "\n");
    }
    for (int s = 0; s < 400; s++) {
        int snorm = (s % 2) == 1;
        for (int i = 0; i < 16; i++) {
            if (s % 7 == 0) {
                rg[i][0] = (uint8_t)((i * 16) & 0xff);
                rg[i][1] = (uint8_t)(255 - ((i * 16) & 0xff));
            } else {
                rg[i][0] = (uint8_t)rnd();
                rg[i][1] = (uint8_t)rnd();
            }
        }
        if (snorm) tc_encode_bc5_block_snorm(rg, out16);
        else tc_encode_bc5_block(rg, out16);
        fprintf(out, "%s ", snorm ? "bc5s" : "bc5");
        for (int i = 0; i < 16; i++) fprintf(out, "%02x", rg[i][0]);
        fprintf(out, " ");
        for (int i = 0; i < 16; i++) fprintf(out, "%02x", rg[i][1]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", out16[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
