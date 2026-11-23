/*
 * texcomp - emit BC4/BC5 full-image decoder vectors for the Lean gate.
 *
 * Format per line:
 *   bc4|bc5 <w> <h> <compressed-hex> <out-byte>...
 * Output is the unorm8 RGBA8 (BC5) or single-channel (BC4) row-major image.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#include "texcomp_internal.h"

static uint32_t st = 0x13579bdfu;
static uint8_t rnd8(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return (uint8_t)st;
}

int main(void) {
    int iter;
    for (iter = 0; iter < 200; ++iter) {
        uint32_t w = 1 + rnd8() % 17, h = 1 + rnd8() % 17;
        uint32_t bx = (w + 3) / 4, by = (h + 3) / 4;
        uint32_t nbc = bx * by;
        uint8_t *data = (uint8_t *)malloc((size_t)nbc * 16u);
        uint32_t i;
        for (i = 0; i < nbc * 16u; ++i) data[i] = rnd8();

        /* BC4 (unorm8, one BC4 block per 4x4 tile), row-major output */
        printf("bc4 %u %u ", w, h);
        for (i = 0; i < nbc * 8u; ++i) printf("%02x", data[i]);
        putchar(' ');
        for (i = 0; i < w * h; ++i) {
            uint32_t x = i % w, y = i / w;
            uint32_t bi = (y / 4u) * bx + x / 4u;
            uint32_t t = (y % 4u) * 4u + x % 4u;
            uint8_t v[16];
            tc_decode_bc4_block(data + bi * 8u, v);
            printf("%u ", v[t]);
        }
        putchar('\n');

        /* BC5 (two BC4 blocks per tile, RGBA8 row-major output) */
        printf("bc5 %u %u ", w, h);
        for (i = 0; i < nbc * 16u; ++i) printf("%02x", data[i]);
        putchar(' ');
        for (i = 0; i < w * h; ++i) {
            uint32_t x = i % w, y = i / w;
            uint32_t bi = (y / 4u) * bx + x / 4u;
            uint32_t t = (y % 4u) * 4u + x % 4u;
            uint8_t r[16], g[16];
            tc_decode_bc4_block(data + bi * 16u, r);
            tc_decode_bc4_block(data + bi * 16u + 8u, g);
            printf("%u %u 0 255 ", r[t], g[t]);
        }
        putchar('\n');
        free(data);
    }
    return 0;
}
