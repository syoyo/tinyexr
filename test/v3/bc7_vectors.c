/* BC7 differential vectors: C decode of seeded 4x4 (one block) images. */
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

static void emit_block(uint8_t blk[16], FILE *out) {
    uint8_t px[16][4];
    uint8_t data[16];
    memcpy(data, blk, 16);
    tc_result r = tc_bc7_decompress_rgba8(data, 4, 4, 4 * 4, &px[0][0], sizeof(px));
    if (r != TC_SUCCESS) { fprintf(stderr, "decode failed\n"); return; }
    fprintf(out, "0 ");
    for (int i = 0; i < 16; i++) fprintf(out, "%02x", blk[i]);
    fprintf(out, " |");
    for (int i = 0; i < 16; i++)
        fprintf(out, " %02x %02x %02x %02x", px[i][0], px[i][1], px[i][2], px[i][3]);
    fprintf(out, "\n");
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    /* Modes 0..7 via unary prefix (m zero bits + 1), plus reserved 8 (8 zeros). */
    for (int m = 0; m <= 7; m++) {
        for (int s = 0; s < 64; s++) {
            uint8_t blk[16];
            for (int i = 0; i < 16; i++) blk[i] = (uint8_t)splitmix64();
            blk[0] = (uint8_t)((blk[0] & ~((1u << (m + 1)) - 1u)) | (1u << m));
            /* Lower m bits stay 0 (unary zeros), bit m = 1. */
            blk[0] = (uint8_t)(blk[0] & (uint8_t)~((1u << m) - 1u));
            emit_block(blk, out);
        }
    }
    for (int s = 0; s < 16; s++) {
        uint8_t blk[16];
        for (int i = 0; i < 16; i++) blk[i] = (uint8_t)splitmix64();
        blk[0] = (uint8_t)(blk[0] & 0xe0u); /* reserved: 8 zeros past 5 */
        emit_block(blk, out);
    }
    uint8_t z[16] = {0};
    uint8_t f[16];
    memset(f, 0xff, sizeof(f));
    emit_block(z, out);
    emit_block(f, out);
    if (out != stdout) fclose(out);
    return 0;
}
