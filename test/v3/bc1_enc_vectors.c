/* BC1 colour-block encoder vectors: C vs Lean.
 *
 * Emits, per line:
 *   bc1 <dxt1> <16 x 4 hex bytes of RGBA> | <8 encoded bytes>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng_state = 0x1234567890abcdefULL;
static uint64_t rnd(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* The encoder lives in texcomp_bc1.c without a header declaration. */
void tc_encode_bc1_color_block(const uint8_t px[16][4], int dxt1, uint8_t out[8]);

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    for (int s = 0; s < 1200; s++) {
        uint8_t px[16][4];
        uint8_t blk[8];
        int dxt1 = (s % 3) != 2; /* primarily standalone BC1 (dxt1 = 1) */
        /* A third of the blocks are a single colour (exercises the
         * punch-through guard and the c0 == c1 ordering), a third are a
         * smooth gradient, the rest are fully random. */
        if (s % 3 == 0) {
            uint8_t r = (uint8_t)rnd();
            uint8_t g = (uint8_t)rnd();
            uint8_t b = (uint8_t)rnd();
            for (int i = 0; i < 16; i++) {
                px[i][0] = r; px[i][1] = g; px[i][2] = b; px[i][3] = 255;
            }
        } else if (s % 3 == 1) {
            int r0 = (int)(rnd() % 256), g0 = (int)(rnd() % 256), b0 = (int)(rnd() % 256);
            int dr = (int)(rnd() % 64) - 32, dg = (int)(rnd() % 64) - 32,
                db = (int)(rnd() % 64) - 32;
            for (int i = 0; i < 16; i++) {
                int r = r0 + dr * (i % 4), g = g0 + dg * (i % 4), b = b0 + db * (i % 4);
                px[i][0] = (uint8_t)(r < 0 ? 0 : (r > 255 ? 255 : r));
                px[i][1] = (uint8_t)(g < 0 ? 0 : (g > 255 ? 255 : g));
                px[i][2] = (uint8_t)(b < 0 ? 0 : (b > 255 ? 255 : b));
                px[i][3] = 255;
            }
        } else {
            for (int i = 0; i < 16; i++) {
                px[i][0] = (uint8_t)rnd();
                px[i][1] = (uint8_t)rnd();
                px[i][2] = (uint8_t)rnd();
                px[i][3] = 255;
            }
        }
        tc_encode_bc1_color_block(px, dxt1, blk);
        fprintf(out, "bc1 %d ", dxt1);
        for (int i = 0; i < 16; i++)
            fprintf(out, "%02x%02x%02x%02x", px[i][0], px[i][1], px[i][2], px[i][3]);
        fprintf(out, " |");
        for (int i = 0; i < 8; i++) fprintf(out, " %02x", blk[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
