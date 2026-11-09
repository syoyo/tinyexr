/* BC7 per-mode candidate vectors (luma seed + pack): C vs Lean.
 *
 * Each mode is forced through `mode_mask` at the default quality (so the
 * candidate is `tc_build_candidate(mode, 0, ...)` with PCA off) and, for
 * modes other than 6, packed without refinement. Modes 0..3 drop out of the
 * mask for translucent blocks, so those cases stay opaque.
 *
 * Per line: `seed <mode> <16 x RGBA hex> | <16 block bytes>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng = 0xfeedfacecafebeefULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const int modes[] = {0, 2, 3, 4, 5};
    for (unsigned mi = 0; mi < sizeof(modes) / sizeof(modes[0]); mi++) {
        int mode = modes[mi];
        for (int s = 0; s < 90; s++) {
            uint8_t img[16][4];
            uint8_t blk[16];
            tc_bc7_options opt;
            int opaque = mode < 4;
            tc_bc7_options_init(&opt);
            opt.mode_mask = 1u << mode;
            opt.pca_endpoints = 0;
            for (int i = 0; i < 16; i++) {
                int hi = (s & 1) ? (i & 1) : (i >> 2);
                int base = (s % 3 == 0) ? 128 : (int)(rnd() % 200);
                img[i][0] = (uint8_t)(hi ? base + 40 : base);
                img[i][1] = (uint8_t)(hi ? base : base + 30);
                img[i][2] = (uint8_t)(hi ? base + 20 : (int)(rnd() % 256));
                img[i][3] = opaque ? 255 : (uint8_t)(hi ? 255 : (int)(rnd() % 128));
                if (s % 4 == 0) {
                    img[i][0] = (uint8_t)rnd();
                    img[i][1] = (uint8_t)rnd();
                    img[i][2] = (uint8_t)rnd();
                    if (!opaque) img[i][3] = (uint8_t)rnd();
                }
            }
            if (tc_bc7_compress_rgba8(&img[0][0], 4, 4, 16, &opt, blk,
                                      sizeof(blk)) != TC_SUCCESS) {
                fprintf(stderr, "compress failed\n");
                continue;
            }
            fprintf(out, "seed %d ", mode);
            for (int i = 0; i < 16; i++)
                fprintf(out, "%02x%02x%02x%02x", img[i][0], img[i][1], img[i][2],
                        img[i][3]);
            fprintf(out, " |");
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
