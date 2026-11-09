/* BC1/BC3/BC5 differential vectors: C decode of seeded 4x4 images. */
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

static void emit(const char *kind, const uint8_t *blk, int nbytes,
                 const uint8_t *px, int npx, FILE *out) {
    fprintf(out, "%s ", kind);
    for (int i = 0; i < nbytes; i++) fprintf(out, "%02x", blk[i]);
    fprintf(out, " |");
    for (int i = 0; i < npx; i++)
        fprintf(out, " %02x %02x %02x %02x", px[i * 4 + 0], px[i * 4 + 1],
                px[i * 4 + 2], px[i * 4 + 3]);
    fprintf(out, "\n");
}

static void rand_block(uint8_t *blk, int n) {
    for (int i = 0; i < n; i++) blk[i] = (uint8_t)splitmix64();
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    for (int s = 0; s < 512; s++) {
        uint8_t blk[16];
        rand_block(blk, 16);
        uint8_t px[16][4];
        if (tc_bc1_decompress_rgba8(blk, 4, 4, 4 * 4, &px[0][0], sizeof(px)) == TC_SUCCESS)
            emit("bc1", blk, 8, &px[0][0], 16, out);
        if (tc_bc3_decompress_rgba8(blk, 4, 4, 4 * 4, &px[0][0], sizeof(px)) == TC_SUCCESS)
            emit("bc3", blk, 16, &px[0][0], 16, out);
        /* BC5 unsigned path only (snorm involves float conversion). */
        if (tc_bc5_decompress_rgba8(blk, 4, 4, 0, 4 * 4, &px[0][0], sizeof(px)) == TC_SUCCESS)
            emit("bc5", blk, 16, &px[0][0], 16, out);
    }
    if (out != stdout) fclose(out);
    return 0;
}
