/* ASTC LDR image-level compress driver test-vector generator (C side).
 *
 * Emits one line per image:
 *   L <w> <h> <bdx> <bdy> <quality> <uastc> <w*h*4 texel bytes> | <hex blocks>
 *
 * The Lean differential checker (lean/AstcLdrImgCheck.lean) replays these
 * against `astcCompressRgba8` and requires bit-identical output.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"

static uint32_t rng = 0x1dea5eedu;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    /* block dims must pass tc_astc_valid_block; UASTC additionally requires
     * the 4x4 subset (see texcomp.h). */
    static const uint32_t dims[][2] = {
        {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 8}, {12, 10}};
    for (int s = 0; s < 40; s++) {
        uint32_t bdx = dims[s % 8][0], bdy = dims[s % 8][1];
        int cls = (s / 8) % 5;
        uint32_t w = 1 + rnd() % 14;
        uint32_t h = 1 + rnd() % 14;
        int quality = (s + cls) % 3;
        int uastc = (bdx == 4 && bdy == 4) ? ((s + cls) % 2) : 0;
        uint32_t n = w * h * 4;
        uint8_t *pix = malloc(n);
        for (uint32_t i = 0; i < n; i++) pix[i] = 0;
        if (cls == 3) {
            /* solid whole image (all blocks solid) */
            uint8_t base[4];
            for (int c = 0; c < 4; c++) base[c] = (uint8_t)(rnd() % 256);
            for (uint32_t i = 0; i < w * h; i++) memcpy(pix + i * 4, base, 4);
        } else if (cls == 4) {
            /* left half solid, right half noisy (mixed solid + non-solid) */
            uint8_t base[4];
            for (int c = 0; c < 4; c++) base[c] = (uint8_t)(rnd() % 256);
            for (uint32_t i = 0; i < w * h; i++) {
                if ((i % w) * 2u < w)
                    memcpy(pix + i * 4, base, 4);
                else
                    for (int c = 0; c < 4; c++)
                        pix[i * 4 + c] = (uint8_t)(rnd() % 256);
            }
        } else
        for (uint32_t i = 0; i < w * h; i++) {
            switch (cls) {
            case 0: /* noisy RGBA */
                for (int c = 0; c < 4; c++) pix[i * 4 + c] = (uint8_t)(rnd() % 256);
                break;
            case 1: /* noisy opaque */
                for (int c = 0; c < 3; c++) pix[i * 4 + c] = (uint8_t)(rnd() % 256);
                pix[i * 4 + 3] = 255;
                break;
            case 2: /* grayscale + varied alpha */
                pix[i * 4 + 0] = pix[i * 4 + 1] = pix[i * 4 + 2] =
                    (uint8_t)(rnd() % 256);
                pix[i * 4 + 3] = (uint8_t)(rnd() % 256);
                break;
            case 3: /* handled above */
                break;
            default: /* handled above */
                break;
            }
        }
        tc_astc_options opt;
        tc_astc_options_init(&opt);
        opt.block_x = bdx;
        opt.block_y = bdy;
        opt.quality = quality;
        opt.uastc = uastc;
        opt.threads = 1;
        size_t need = tc_astc_compressed_size(w, h, &opt);
        uint8_t *astc = malloc(need);
        if (tc_astc_compress_rgba8(pix, w, h, (size_t)w * 4, &opt, astc, need) !=
            TC_SUCCESS) {
            fprintf(stderr, "compress failed line %d\n", s);
            return 1;
        }
        fprintf(out, "L %u %u %u %u %d %d", w, h, bdx, bdy, quality, uastc);
        for (uint32_t i = 0; i < n; i++) fprintf(out, " %02x", pix[i]);
        fprintf(out, " |");
        for (size_t i = 0; i < need; i++) fprintf(out, " %02x", astc[i]);
        fprintf(out, "\n");
        free(pix);
        free(astc);
    }
    fclose(out);
    return 0;
}
