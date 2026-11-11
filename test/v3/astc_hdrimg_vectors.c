/* ASTC HDR image-level encoder test-vector generator (C side).
 *
 * Emits one line per image:
 *   HR <w> <h> <w*3 float-bit hex> | <hex astc bytes>
 *   HA <w> <h> <w*4 float-bit hex> | <hex astc bytes>
 *
 * Floats are serialized as 8-hex-digit IEEE-754 bit patterns; the Lean
 * checker rebuilds them with Float32.ofBits.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"
#include "texcomp_astc_hdr.c"

static uint32_t rng = 0x0ddba11u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static float rand_float(void) {
    uint32_t k = rnd() % 20;
    if (k == 0) return 0.0f;
    if (k == 1) return 1.0e-30f;
    if (k == 2) return 1.0e30f;
    if (k == 3) return -0.0f;
    /* generic positive float with a limited exponent range */
    uint32_t bits = 0x38000000u + (rnd() % 0x08000000u);
    union { uint32_t u; float f; } v;
    v.u = bits;
    return v.f;
}

static void emit(FILE *out, char tag, uint32_t w, uint32_t h, uint32_t nch) {
    uint32_t n = w * h * nch;
    float *pix = malloc(n * sizeof(float));
    for (uint32_t i = 0; i < n; i++) pix[i] = rand_float();
    /* some solid rows to trigger allsame void extents */
    if (rnd() % 2 == 0) {
        uint32_t row = rnd() % h;
        float f = rand_float();
        for (uint32_t x = 0; x < w; x++)
            for (uint32_t c = 0; c < nch; c++) pix[(row * w + x) * nch + c] = f;
    }
    uint8_t *astc = malloc(tc_astc_hdr_compressed_size(w, h));
    if (tag == 'R')
        tc_astc_hdr_compress_rgbf(pix, w, h, w * 3 * sizeof(float), NULL, astc,
                                  tc_astc_hdr_compressed_size(w, h));
    else
        tc_astc_hdr_compress_rgbaf(pix, w, h, w * 4 * sizeof(float), NULL, astc,
                                   tc_astc_hdr_compressed_size(w, h));
    fprintf(out, "H%c %u %u", tag, w, h);
    union { float f; uint32_t u; } b;
    for (uint32_t i = 0; i < n; i++) {
        b.f = pix[i];
        fprintf(out, " %08x", b.u);
    }
    fprintf(out, " |");
    uint32_t blocks = ((w + 3) / 4) * ((h + 3) / 4);
    for (uint32_t i = 0; i < blocks * 16; i++) fprintf(out, " %02x", astc[i]);
    fprintf(out, "\n");
    free(pix);
    free(astc);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const uint32_t dims[][2] = {
        {4, 4}, {5, 3}, {8, 8}, {7, 7}, {4, 6}, {12, 4}, {1, 1}, {9, 5}};
    for (int s = 0; s < 24; s++) {
        uint32_t w = dims[s % 8][0], h = dims[s % 8][1];
        emit(out, (s % 2) ? 'A' : 'R', w, h, (s % 2) ? 4 : 3);
    }
    fclose(out);
    return 0;
}
