/* texcomp "uni" -> BC1 / BC7 transcode vectors (C side), public API only.
 *   T <w> <h> <ok> | <uni blocks> | <bc1> | <bc7>
 * s < 20: random RGBA8 -> tc_uni_compress_rgba8 -> transcode (ok = 1).
 * s >= 20: random uni bytes; ok = 1 only if the C accepts them.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "texcomp.h"

static uint32_t rng = 0x2468ace1u;
static uint32_t rn(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 36; s++) {
        uint32_t w = 1 + rn() % 10, h = 1 + rn() % 10;
        size_t usz = tc_uni_compressed_size(w, h), n = (size_t)w * h * 4;
        size_t b1 = tc_bc1_compressed_size(w, h), b7 = tc_bc7_compressed_size(w, h);
        uint8_t *pix = malloc(n), *uni = malloc(usz), *o1 = calloc(b1, 1), *o7 = calloc(b7, 1);
        int comp = s < 20, ok;
        for (size_t i = 0; i < n; i++) pix[i] = (uint8_t)rn();
        if (comp && s % 3 == 0) for (size_t i = 0; i < n; i++) pix[i] = pix[i & 3]; /* flat */
        if (comp && s % 4 == 1) for (size_t i = 3; i < n; i += 4) pix[i] = (uint8_t)(rn() % 2 ? 255 : rn()); /* alpha mix */
        if (comp) {
            if (tc_uni_compress_rgba8(pix, w, h, (size_t)w * 4, uni, usz) != TC_SUCCESS) return 2;
        } else {
            for (size_t i = 0; i < usz; i++) uni[i] = (uint8_t)rn();
        }
        ok = tc_uni_transcode_bc1(uni, w, h, o1, b1) == TC_SUCCESS;
        if (ok != (tc_uni_transcode_bc7(uni, w, h, o7, b7) == TC_SUCCESS)) return 3;
        fprintf(out, "T %u %u %d |", w, h, ok);
        for (size_t i = 0; i < usz; i++) fprintf(out, " %02x", uni[i]);
        fprintf(out, " |");
        if (ok) for (size_t i = 0; i < b1; i++) fprintf(out, " %02x", o1[i]);
        fprintf(out, " |");
        if (ok) for (size_t i = 0; i < b7; i++) fprintf(out, " %02x", o7[i]);
        fprintf(out, "\n");
        free(pix); free(uni); free(o1); free(o7);
    }
    fclose(out);
    return 0;
}
