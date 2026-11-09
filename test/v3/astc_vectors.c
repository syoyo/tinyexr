/* ASTC differential vectors: encoder blocks + C decode of seeded 4x4 images. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng_state;
static uint64_t splitmix64(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    tc_astc_options opt;
    memset(&opt, 0, sizeof(opt));
    opt.block_x = 4;
    opt.block_y = 4;
    opt.quality = 2;
    opt.uastc = 1;
    for (int s = 0; s < 1024; s++) {
        uint8_t img[16][4];
        for (int i = 0; i < 16; i++)
            for (int c = 0; c < 4; c++) img[i][c] = (uint8_t)splitmix64();
        uint8_t blk[16];
        if (tc_astc_compress_rgba8(&img[0][0], 4, 4, 4 * 4, &opt, blk, sizeof(blk)) != TC_SUCCESS) {
            fprintf(stderr, "compress failed\n");
            continue;
        }
        uint8_t px[16][4];
        if (tc_astc_decompress_rgba8(blk, 4, 4, 4, 4, &px[0][0], sizeof(px)) != TC_SUCCESS) {
            fprintf(stderr, "decompress failed\n");
            continue;
        }
        fprintf(out, "0 ");
        for (int i = 0; i < 16; i++) fprintf(out, "%02x", blk[i]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++)
            fprintf(out, " %02x %02x %02x %02x", px[i][0], px[i][1], px[i][2], px[i][3]);
        fprintf(out, "\n");
    }
    if (out != stdout) fclose(out);
    return 0;
}
