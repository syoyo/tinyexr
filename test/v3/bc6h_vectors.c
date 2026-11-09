/* BC6H differential vectors: C decode of seeded 4x4 (one block) images. */
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

static void emit_block(uint8_t blk[16], int is_signed, FILE *out) {
    uint16_t px[16][3];
    uint8_t data[16];
    memcpy(data, blk, 16);
    tc_result r = tc_bc6h_decompress_rgb16f(data, 4, 4, is_signed, 4 * 3 * 2,
                                             &px[0][0], sizeof(px));
    if (r != TC_SUCCESS) { fprintf(stderr, "decode failed\n"); return; }
    fprintf(out, "%d ", is_signed);
    for (int i = 0; i < 16; i++) fprintf(out, "%02x", blk[i]);
    fprintf(out, " |");
    for (int i = 0; i < 16; i++)
        fprintf(out, " %04x %04x %04x", px[i][0], px[i][1], px[i][2]);
    fprintf(out, "\n");
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    /* Combined modes to cover: 0x00,0x01,0x02,0x06,0x0a,0x0e,0x12,0x16,
       0x1a,0x1e,0x03,0x07,0x0b,0x0f, plus reserved 0x04,0x08. */
    static const uint8_t modes[16] = {0x00,0x01,0x02,0x06,0x0a,0x0e,0x12,0x16,
                                      0x1a,0x1e,0x03,0x07,0x0b,0x0f,0x04,0x08};
    for (int m = 0; m < 16; m++) {
        for (int s = 0; s < 64; s++) {
            uint8_t blk[16];
            for (int i = 0; i < 16; i++) blk[i] = (uint8_t)splitmix64();
            /* Force the 5-bit combined mode: low 5 bits of the first byte. */
            blk[0] = (uint8_t)((blk[0] & 0xe0u) | (modes[m] & 0x1fu));
            emit_block(blk, s & 1, out);
        }
    }
    /* Edge blocks. */
    uint8_t z[16] = {0};
    uint8_t f[16];
    memset(f, 0xff, sizeof(f));
    for (int s = 0; s < 2; s++) { emit_block(z, s, out); emit_block(f, s, out); }
    if (out != stdout) fclose(out);
    return 0;
}
