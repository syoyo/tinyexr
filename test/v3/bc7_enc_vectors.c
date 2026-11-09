/* BC7 full block encoder vectors (default options): C vs Lean.
 *
 * Per line: `enc <16 x RGBA hex> | <16 block bytes>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng = 0x5ca1ab1e12345678ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 800; s++) {
        uint8_t img[16][4];
        uint8_t blk[16];
        tc_bc7_options opt;
        tc_bc7_options_init(&opt);
        /* Half the vectors use the exhaustive partition search (quick = 0). */
        if (s & 1) opt.quick = 0;
        for (int i = 0; i < 16; i++) {
            int hi = (i & 1) ^ ((i >> 2) & 1);
            switch (s % 6) {
            case 0: /* constant */
                img[i][0] = (uint8_t)(s * 7);
                img[i][1] = (uint8_t)(s * 11);
                img[i][2] = (uint8_t)(s * 13);
                img[i][3] = 255;
                break;
            case 1: /* opaque gradient */
                img[i][0] = (uint8_t)(16 + i * 14);
                img[i][1] = (uint8_t)(250 - i * 9);
                img[i][2] = (uint8_t)((i * 37) & 0xff);
                img[i][3] = 255;
                break;
            case 2: /* chromatic two-tone, opaque */
                img[i][0] = (uint8_t)(hi ? 230 : 20);
                img[i][1] = (uint8_t)(hi ? 40 : 200);
                img[i][2] = (uint8_t)(hi ? 60 : 120);
                img[i][3] = 255;
                break;
            case 3: /* translucent gradient */
                img[i][0] = (uint8_t)(i * 16);
                img[i][1] = (uint8_t)(255 - i * 12);
                img[i][2] = 90;
                img[i][3] = (uint8_t)(i * 15);
                break;
            case 4: /* random with alpha */
                img[i][0] = (uint8_t)rnd();
                img[i][1] = (uint8_t)rnd();
                img[i][2] = (uint8_t)rnd();
                img[i][3] = (uint8_t)rnd();
                break;
            default: /* random opaque */
                img[i][0] = (uint8_t)rnd();
                img[i][1] = (uint8_t)rnd();
                img[i][2] = (uint8_t)rnd();
                img[i][3] = 255;
                break;
            }
        }
        if (tc_bc7_compress_rgba8(&img[0][0], 4, 4, 16, &opt, blk, sizeof(blk)) !=
            TC_SUCCESS) {
            fprintf(stderr, "compress failed\n");
            continue;
        }
        fprintf(out, "enc%d ", (s & 1) ? 1 : 0);
        for (int i = 0; i < 16; i++)
            fprintf(out, "%02x%02x%02x%02x", img[i][0], img[i][1], img[i][2], img[i][3]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
