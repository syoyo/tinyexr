/* texcomp "uni" test-vector generator (C side), public API only.
 *   U <w> <h> <ok> <compress> | <rgba> | <uni blocks> | <decoded rgba>
 * s < 24: random RGBA8 -> tc_uni_compress_rgba8 -> tc_uni_decompress_rgba8.
 * s >= 24: random uni bytes (corrupt/valid mix) -> decoder ok flag.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "texcomp.h"

static uint32_t rng = 0x13572468u;
static uint32_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 40; s++) {
        uint32_t w = 1 + rnd() % 14, h = 1 + rnd() % 14;
        size_t usz = tc_uni_compressed_size(w, h), n = (size_t)w * h * 4;
        uint8_t *pix = malloc(n), *uni = malloc(usz), *dec = calloc(n, 1);
        int comp = s < 24, ok;
        for (size_t i = 0; i < n; i++) pix[i] = (uint8_t)(rnd() % 256);
        if (comp) {
            /* mix in flat/solid content so void-extent-like UASTC modes occur */
            if (s % 3 == 0) for (size_t i = 0; i < n; i++) pix[i] = (uint8_t)(pix[i & 3] );
            if (tc_uni_compress_rgba8(pix, w, h, (size_t)w * 4, uni, usz) != TC_SUCCESS) {
                fprintf(stderr, "compress failed %d\n", s); return 1;
            }
        } else {
            for (size_t i = 0; i < usz; i++) uni[i] = (uint8_t)(rnd() % 256);
        }
        ok = tc_uni_decompress_rgba8(uni, w, h, (size_t)w * 4, dec, n) == TC_SUCCESS;
        fprintf(out, "U %u %u %d %d |", w, h, ok, comp);
        if (comp) for (size_t i = 0; i < n; i++) fprintf(out, " %02x", pix[i]);
        fprintf(out, " |");
        for (size_t i = 0; i < usz; i++) fprintf(out, " %02x", uni[i]);
        fprintf(out, " |");
        if (ok) for (size_t i = 0; i < n; i++) fprintf(out, " %02x", dec[i]);
        fprintf(out, "\n");
        free(pix); free(uni); free(dec);
    }
    fclose(out);
    return 0;
}
