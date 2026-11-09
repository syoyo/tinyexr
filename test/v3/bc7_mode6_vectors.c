/* BC7 mode-6 block encoder vectors: C vs Lean.
 *
 * The encoder is restricted to mode 6 through `mode_mask`, with the default
 * quality/quick settings and PCA seeding off, so `tc_encode_bc7_all_modes_block`
 * runs exactly the seed -> refine_mode6 -> pack path the Lean model ports.
 *
 * Per line: `m6 <16 x RGBA hex> | <16 block bytes>`
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng = 0x0badc0ffee123456ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 600; s++) {
        uint8_t img[16][4];
        uint8_t blk[16];
        tc_bc7_options opt;
        tc_bc7_options_init(&opt);
        opt.mode_mask = 1u << 6;
        opt.pca_endpoints = 0;
        if (s % 4 == 0) {
            /* Constant block. */
            uint8_t r = (uint8_t)rnd(), g = (uint8_t)rnd(), b = (uint8_t)rnd(),
                    a = (uint8_t)rnd();
            for (int i = 0; i < 16; i++) {
                img[i][0] = r; img[i][1] = g; img[i][2] = b; img[i][3] = a;
            }
        } else if (s % 4 == 1) {
            /* Smooth gradient (the common case). */
            int r0 = (int)(rnd() % 200), g0 = (int)(rnd() % 200),
                b0 = (int)(rnd() % 200), a0 = (int)(rnd() % 200);
            int dr = (int)(rnd() % 40) - 20, dg = (int)(rnd() % 40) - 20,
                db = (int)(rnd() % 40) - 20, da = (int)(rnd() % 40) - 20;
            for (int i = 0; i < 16; i++) {
                int t = i;
                int rr = r0 + dr * t, gg = g0 + dg * t, bb2 = b0 + db * t,
                    aa = a0 + da * t;
                img[i][0] = (uint8_t)(rr < 0 ? 0 : rr > 255 ? 255 : rr);
                img[i][1] = (uint8_t)(gg < 0 ? 0 : gg > 255 ? 255 : gg);
                img[i][2] = (uint8_t)(bb2 < 0 ? 0 : bb2 > 255 ? 255 : bb2);
                img[i][3] = (uint8_t)(aa < 0 ? 0 : aa > 255 ? 255 : aa);
            }
        } else if (s % 4 == 2) {
            /* Two-tone with alpha variation. */
            for (int i = 0; i < 16; i++) {
                int hi = (i & 1);
                img[i][0] = (uint8_t)(hi ? 200 + (int)(rnd() % 55) : (int)(rnd() % 56));
                img[i][1] = (uint8_t)(hi ? 30 : 220);
                img[i][2] = (uint8_t)(hi ? 90 : 40);
                img[i][3] = (uint8_t)(hi ? 255 : 32);
            }
        } else {
            for (int i = 0; i < 16; i++) {
                img[i][0] = (uint8_t)rnd();
                img[i][1] = (uint8_t)rnd();
                img[i][2] = (uint8_t)rnd();
                img[i][3] = (uint8_t)rnd();
            }
        }
        if (tc_bc7_compress_rgba8(&img[0][0], 4, 4, 16, &opt, blk, sizeof(blk)) !=
            TC_SUCCESS) {
            fprintf(stderr, "compress failed\n");
            continue;
        }
        fprintf(out, "m6 ");
        for (int i = 0; i < 16; i++)
            fprintf(out, "%02x%02x%02x%02x", img[i][0], img[i][1], img[i][2], img[i][3]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
