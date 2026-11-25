/*
 * texcomp - vectors for the half/float output decompress wrappers.
 *
 * Random 16-byte blocks are fed directly to the public wrappers (the block
 * decoders are total); the Lean model must reproduce every output byte.
 * Format: <op> <args...> <input-hex> <output-hex>
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "texcomp.h"

static uint32_t st = 0x12345678u;
static uint32_t rnd(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return st;
}
static void hex(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; ++i) printf("%02x", p[i]);
    putchar(' ');
}
static void hexf(const float *p, size_t n) {
    for (size_t i = 0; i < n; ++i) {
        uint32_t b; memcpy(&b, &p[i], 4); printf("%08x", b);
    }
    putchar(' ');
}

int main(void) {
    static const int dims[] = {1, 2, 3, 5, 7, 8};
    uint8_t blocks[64 * 16];
    uint16_t hout[64 * 3 * 4];
    float fout[64 * 4 * 4];
    for (int k = 0; k < 96; ++k) {
        int w = dims[k % 6], h = dims[(k / 6) % 6];
        int signed_mode = k & 1;
        size_t nb = (size_t)((w + 3) / 4) * (size_t)((h + 3) / 4) * 16;
        for (size_t i = 0; i < nb; ++i) blocks[i] = (uint8_t)rnd();
        size_t row = (size_t)w * 3 * sizeof(uint16_t);
        memset(hout, 0, sizeof(hout));
        if (tc_bc6h_decompress_rgb16f(blocks, (uint32_t)w, (uint32_t)h,
                signed_mode, row, hout, (size_t)h * row) != TC_SUCCESS) continue;
        printf("bc6h16 %d %d %d ", signed_mode, w, h);
        hex(blocks, nb);
        hex((const uint8_t *)hout, (size_t)w * h * 3 * 2);
        putchar('\n');

        row = (size_t)w * 4 * sizeof(float);
        memset(fout, 0, sizeof(fout));
        if (tc_bc6h_decompress_rgbaf(blocks, (uint32_t)w, (uint32_t)h,
                signed_mode, row, fout, (size_t)h * row) != TC_SUCCESS) continue;
        printf("bc6hf %d %d %d ", signed_mode, w, h);
        hex(blocks, nb);
        hexf(fout, (size_t)w * h * 4);
        putchar('\n');
    }
    for (int k = 0; k < 96; ++k) {
        int w = dims[k % 6], h = dims[(k / 6) % 6];
        size_t nb = (size_t)((w + 3) / 4) * (size_t)((h + 3) / 4) * 16;
        for (size_t i = 0; i < nb; ++i) blocks[i] = (uint8_t)rnd();
        size_t row = (size_t)w * 4 * sizeof(float);
        memset(fout, 0, sizeof(fout));
        if (tc_bc7_decompress_rgbaf(blocks, (uint32_t)w, (uint32_t)h,
                row, fout, (size_t)h * row) != TC_SUCCESS) continue;
        printf("bc7f %d %d ", w, h);
        hex(blocks, nb);
        hexf(fout, (size_t)w * h * 4);
        putchar('\n');
    }
    for (int k = 0; k < 96; ++k) {
        int w = dims[k % 6], h = dims[(k / 6) % 6];
        int bx = (k & 1) ? 6 : 4, by = (k & 2) ? 6 : 4;
        size_t bxc = (size_t)((w + bx - 1) / bx);
        size_t nb = bxc * (size_t)((h + by - 1) / by) * 16;
        for (size_t i = 0; i < nb; ++i) blocks[i] = (uint8_t)rnd();
        size_t row = (size_t)w * 4 * sizeof(float);
        memset(fout, 0, sizeof(fout));
        if (tc_astc_hdr_decompress_rgbaf(blocks, (uint32_t)w, (uint32_t)h,
                (uint32_t)bx, (uint32_t)by, row, fout, (size_t)h * row) != TC_SUCCESS) continue;
        printf("astcf %d %d %d %d ", w, h, bx, by);
        hex(blocks, nb);
        hexf(fout, (size_t)w * h * 4);
        putchar('\n');
    }
    return 0;
}
