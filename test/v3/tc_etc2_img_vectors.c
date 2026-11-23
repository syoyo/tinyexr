/*
 * texcomp - emit ETC2/EAC full-image decoder vectors for the Lean gate.
 * Format: <kind> <w> <h> <compressed-hex> <out-byte>...
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "texcomp.h"

static uint32_t st = 0x51ed270bu;
static uint8_t rnd8(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return (uint8_t)st;
}

static void emit(const char *kind, uint32_t w, uint32_t h, const uint8_t *data,
                 size_t nbytes, int mode) {
    uint32_t bsz = mode < 2 ? (mode == 1 ? 16u : 8u) : (mode == 3 ? 16u : 8u);
    size_t outsz = (size_t)w * h * 4u;
    uint8_t *out = (uint8_t *)calloc(outsz, 1);
    size_t i;
    tc_result rc;
    if (mode < 2)
        rc = tc_etc2_decompress_rgba8(data, w, h, mode, (size_t)w * 4u, out, outsz);
    else
        rc = tc_eac_decompress_rgba8(data, w, h, mode == 3, (size_t)w * 4u, out, outsz);
    if (rc != TC_SUCCESS) { free(out); return; }
    printf("%s %u %u ", kind, w, h);
    for (i = 0; i < nbytes; ++i) printf("%02x", data[i]);
    putchar(' ');
    for (i = 0; i < outsz; ++i) printf("%u ", out[i]);
    putchar('\n');
    free(out);
}

static void emit_bc7(uint32_t w, uint32_t h, const uint8_t *data, size_t nbytes) {
    size_t outsz = (size_t)w * h * 4u;
    uint8_t *out = (uint8_t *)calloc(outsz, 1);
    size_t i;
    if (tc_bc7_decompress_rgba8(data, w, h, (size_t)w * 4u, out, outsz) != TC_SUCCESS) {
        free(out); return;
    }
    printf("bc7 %u %u ", w, h);
    for (i = 0; i < nbytes; ++i) printf("%02x", data[i]);
    putchar(' ');
    for (i = 0; i < outsz; ++i) printf("%u ", out[i]);
    putchar('\n');
    free(out);
}

int main(void) {
    int iter;
    for (iter = 0; iter < 100; ++iter) {
        uint32_t w = 1 + rnd8() % 13, h = 1 + rnd8() % 13;
        uint32_t bx = (w + 3) / 4, by = (h + 3) / 4, nbc = bx * by;
        uint8_t *data = (uint8_t *)malloc((size_t)nbc * 16u);
        uint32_t i;
        for (i = 0; i < nbc * 16u; ++i) data[i] = rnd8();
        emit("etc2rgb", w, h, data, (size_t)nbc * 8u, 0);
        emit("etc2rgba", w, h, data, (size_t)nbc * 16u, 1);
        emit("eacr11", w, h, data, (size_t)nbc * 8u, 2);
        emit("eacrg11", w, h, data, (size_t)nbc * 16u, 3);
        emit_bc7(w, h, data, (size_t)nbc * 16u);
        free(data);
    }
    return 0;
}
