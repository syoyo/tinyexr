/* BC7 decoder-driven RDO pass vectors: C vs Lean.
 *
 * A synthetic image is encoded with the default all-modes encoder, then
 * `tc_bc7_rdo_pass` rewrites blocks. Per group: `G <rdo> <nblocks>`, then
 * per block `B <128 src hex> <32 pre-block hex> <32 post-block hex>` where
 * src is the gathered 64-byte source block, pre is the encoder output and
 * post is the block bytes after the RDO pass.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc7.c"

#define W 96
#define H 64
#define STRIDE (W * 4)

static uint8_t img[STRIDE * H];

static uint32_t rng = 0x13572468u;
static uint32_t rnd(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

static void fill_image(void) {
    /* Smooth gradient, a repeated tile band (so RDO can find duplicates) and
     * a noise band. */
    for (int y = 0; y < H; y++) {
        for (int x = 0; x < W; x++) {
            uint8_t *p = img + y * STRIDE + x * 4;
            if (y < 24) {
                p[0] = (uint8_t)(x * 2);
                p[1] = (uint8_t)(y * 6);
                p[2] = (uint8_t)((x + y) * 2);
                p[3] = 255;
            } else if (y < 40) {
                int tx = (x / 8) % 3;
                p[0] = (uint8_t)(tx == 0 ? 20 : tx == 1 ? 200 : 90);
                p[1] = (uint8_t)(tx == 0 ? 30 : tx == 1 ? 60 : 210);
                p[2] = (uint8_t)(tx == 0 ? 40 : tx == 1 ? 120 : 10);
                p[3] = 255;
            } else {
                p[0] = (uint8_t)rnd();
                p[1] = (uint8_t)rnd();
                p[2] = (uint8_t)rnd();
                p[3] = 255;
            }
        }
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    fill_image();
    uint32_t bxc = (W + 3u) / 4u, byc = (H + 3u) / 4u;
    uint32_t nblocks = bxc * byc;
    static uint8_t blocks[64 * 24 * 16];
    static uint8_t orig[64 * 24 * 16];
    tc_bc7_options opt;
    tc_bc7_options_init(&opt);
    opt.rdo = 0;
    opt.quick = 0;
    opt.pca_endpoints = 0;
    for (uint32_t i = 0; i < nblocks; i++) {
        uint8_t block[16][4];
        tc_bc7_gather_block(img, W, H, STRIDE, (i % bxc) * 4u, (i / bxc) * 4u, block);
        tc_encode_bc7_all_modes_block(block, &opt, blocks + (size_t)i * 16u);
    }
    memcpy(orig, blocks, (size_t)nblocks * 16u);
    static const int rdos[2] = {0, 6};
    for (int r = 0; r < 2; r++) {
        memcpy(blocks, orig, (size_t)nblocks * 16u);
        tc_bc7_rdo_pass(img, W, H, STRIDE, rdos[r], blocks);
        fprintf(out, "G %d %u\n", rdos[r], nblocks);
        for (uint32_t i = 0; i < nblocks; i++) {
            uint8_t block[16][4];
            tc_bc7_gather_block(img, W, H, STRIDE, (i % bxc) * 4u, (i / bxc) * 4u,
                                block);
            fprintf(out, "B ");
            for (int t = 0; t < 64; t++) fprintf(out, "%02x", ((const uint8_t *)block)[t]);
            fprintf(out, " ");
            for (int t = 0; t < 16; t++) fprintf(out, "%02x", orig[(size_t)i * 16u + (size_t)t]);
            fprintf(out, " ");
            for (int t = 0; t < 16; t++) fprintf(out, "%02x", blocks[(size_t)i * 16u + (size_t)t]);
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
