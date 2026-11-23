/*
 * texcomp - emit BC5 image-compressor vectors for the Lean gate.
 * Format: bc5enc <w> <h> <rgba> <snorm> <src-hex> <compressed-hex>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#include "texcomp.h"

static uint32_t st = 0x27d4eb2fu;
static uint8_t rnd8(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return (uint8_t)st;
}
static void puthex(const uint8_t *p, size_t n) {
    size_t i;
    for (i = 0; i < n; ++i) printf("%02x", p[i]);
}

int main(void) {
    int iter;
    for (iter = 0; iter < 200; ++iter) {
        uint32_t w = 1 + rnd8() % 17, h = 1 + rnd8() % 17;
        int rgba = iter % 2, snorm = (iter / 2) % 2;
        size_t bpp = rgba ? 4u : 2u;
        size_t nsrc = (size_t)w * h * bpp;
        size_t nout = tc_bc5_compressed_size(w, h);
        uint8_t *src = (uint8_t *)malloc(nsrc);
        size_t nsrc4 = (size_t)w * h * 4u;
        uint8_t *src4 = (uint8_t *)malloc(nsrc4);
        uint8_t *out = (uint8_t *)malloc(nout);
        tc_bc5_options opt;
        size_t i;
        for (i = 0; i < nsrc; ++i) src[i] = rnd8();
        for (i = 0; i < nsrc4; ++i) src4[i] = rnd8();
        opt.snorm = snorm;
        if (rgba)
            tc_bc5_compress_rgba8(src, w, h, (size_t)w * bpp, &opt, out, nout);
        else
            tc_bc5_compress_rg8(src, w, h, (size_t)w * bpp, &opt, out, nout);
        if (rgba) {
            size_t n3 = tc_bc3_compressed_size(w, h);
            uint8_t *o3 = (uint8_t *)malloc(n3);
            tc_bc3_compress_rgba8(src4, w, h, (size_t)w * 4u, NULL, o3, n3);
            printf("bc3enc %u %u 1 0 ", w, h);
            puthex(src4, nsrc4);
            putchar(' ');
            puthex(o3, n3);
            putchar('\n');
            free(o3);
        }
        {
            int rg11 = iter % 2;
            size_t ne = tc_eac_r11_compressed_size(w, h);
            uint8_t *oe;
            if (rg11) ne = tc_eac_rg11_compressed_size(w, h);
            oe = (uint8_t *)malloc(ne);
            tc_eac_compress_rgba8(src4, w, h, (size_t)w * 4u, rg11, oe, ne);
            printf("eacenc %u %u %d 0 ", w, h, rg11);
            puthex(src4, nsrc4);
            putchar(' ');
            puthex(oe, ne);
            putchar('\n');
            free(oe);
        }
        {
            size_t n7 = tc_bc7_compressed_size(w, h);
            uint8_t *o7 = (uint8_t *)malloc(n7);
            tc_bc7_compress_rgba8(src4, w, h, (size_t)w * 4u, NULL, o7, n7);
            printf("bc7enc %u %u 0 0 ", w, h);
            puthex(src4, nsrc4);
            putchar(' ');
            puthex(o7, n7);
            putchar('\n');
            free(o7);
        }
        printf("bc5enc %u %u %d %d ", w, h, rgba, snorm);
        puthex(src, nsrc);
        putchar(' ');
        puthex(out, nout);
        putchar('\n');
        free(src);
        free(src4);
        free(out);
    }
    return 0;
}
