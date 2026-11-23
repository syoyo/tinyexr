/*
 * texcomp - emit BC6H image-compressor vectors for the Lean gate.
 * Format: bc6henc <w> <h> <signed> <f32-bit-words> <compressed-hex>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "texcomp.h"

static uint64_t st = 0x9e3779b97f4a7c15ULL;
static uint32_t rnd(void) {
    uint64_t z = (st += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return (uint32_t)(z ^ (z >> 31));
}
static float finite_f32(int sf) {
    uint32_t e = 100u + (rnd() % 48u);   /* ~[2^-27, 2^20] */
    uint32_t m = rnd() & 0x7fffffu;
    uint32_t s = sf && (rnd() & 1u) ? 0x80000000u : 0u;
    uint32_t b = s | (e << 23) | m;
    float f;
    memcpy(&f, &b, 4);
    return f;
}

int main(void) {
    int iter;
    for (iter = 0; iter < 100; ++iter) {
        uint32_t w = 1 + rnd() % 13, h = 1 + rnd() % 13;
        int sf = iter % 2;
        size_t npx = (size_t)w * h * 3u;
        size_t nout = tc_bc6h_compressed_size(w, h);
        float *src = (float *)malloc(npx * sizeof(float));
        uint8_t *out = (uint8_t *)malloc(nout);
        tc_bc6h_options opt;
        size_t i;
        for (i = 0; i < npx; ++i) src[i] = finite_f32(sf);
        memset(&opt, 0, sizeof(opt));
        opt.signed_float = sf;
        tc_bc6h_compress_rgb32f(src, w, h, (size_t)w * 3u * sizeof(float),
                                &opt, out, nout);
        printf("bc6henc %u %u %d ", w, h, sf);
        for (i = 0; i < npx; ++i) {
            uint32_t b;
            memcpy(&b, &src[i], 4);
            printf("%08x", b);
        }
        putchar(' ');
        for (i = 0; i < nout; ++i) printf("%02x", out[i]);
        putchar('\n');
        free(src);
        free(out);
    }
    return 0;
}
