/* ASTC LDR image-level decoder test-vector generator (C side).
 *
 * Emits one line per image:
 *   D <w> <h> <bdx> <bdy> <ok> <blocks 16-byte hex> | <rgba 4*w*h bytes hex>
 *
 * Two classes:
 *   s < 20: compress a random RGBA8 image (valid footprint), then decode it
 *           via tc_astc_decompress_rgba8 -> ok == 1.
 *   s >= 20: random w/h and random block dims (1..12), random 16-byte
 *            blocks -> ok is whatever tc_astc_decompress_rgba8 returns
 *            (0 or 1), exercising the corrupt / unsupported paths.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"
#include "texcomp_astc_decode.c"

static uint32_t rng = 0xdeadbeefu;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const uint32_t dims[][2] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 8}, {12, 10}};

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 40; s++) {
        uint32_t w, h, bdx, bdy;
        uint32_t bw, bh, nblocks, blocksz, rgba_sz;
        uint8_t *blocks, *rgba;
        int ok;
        if (s < 20) {
            int d = s % 8;
            bdx = dims[d][0]; bdy = dims[d][1];
            w = 1 + rnd() % 14;
            h = 1 + rnd() % 14;
            uint32_t n = w * h * 4;
            uint8_t *pix = malloc(n);
            for (uint32_t i = 0; i < n; i++) pix[i] = (uint8_t)(rnd() % 256);
            tc_astc_options opt;
            tc_astc_options_init(&opt);
            opt.block_x = bdx;
            opt.block_y = bdy;
            opt.quality = (s + 1) % 3;
            opt.threads = 1;
            size_t need = tc_astc_compressed_size(w, h, &opt);
            uint8_t *astc = malloc(need);
            if (tc_astc_compress_rgba8(pix, w, h, (size_t)w * 4, &opt, astc, need) != TC_SUCCESS) {
                fprintf(stderr, "compress failed %d\n", s); return 1;
            }
            blocks = astc; blocksz = need;
            free(pix);
        } else {
            bdx = 1 + rnd() % 12;
            bdy = 1 + rnd() % 12;
            w = 1 + rnd() % 14;
            h = 1 + rnd() % 14;
            bw = (w + bdx - 1) / bdx;
            bh = (h + bdy - 1) / bdy;
            nblocks = bw * bh;
            blocksz = nblocks * 16;
            blocks = malloc(blocksz);
            for (uint32_t i = 0; i < blocksz; i++) blocks[i] = (uint8_t)(rnd() % 256);
        }
        bw = (w + bdx - 1) / bdx;
        bh = (h + bdy - 1) / bdy;
        rgba_sz = w * h * 4;
        rgba = malloc(rgba_sz);
        if (tc_astc_decompress_rgba8(blocks, w, h, bdx, bdy, rgba, rgba_sz) == TC_SUCCESS)
            ok = 1;
        else ok = 0;
        fprintf(out, "D %u %u %u %u %d", w, h, bdx, bdy, ok);
        for (uint32_t i = 0; i < blocksz; i++) fprintf(out, " %02x", blocks[i]);
        fprintf(out, " |");
        if (ok) {
            for (uint32_t i = 0; i < rgba_sz; i++) fprintf(out, " %02x", rgba[i]);
        }
        fprintf(out, "\n");
        free(blocks);
        free(rgba);
    }
    fclose(out);
    return 0;
}
