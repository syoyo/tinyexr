/*
 * tocio - matrix/LUT kernel vectors for the algebraic-model gate.
 * Format:
 *   mat <16 m bits> <4 off bits> <4 px bits> <4 out bits>
 *   lut <n> <channels> <domain-min> <domain-max> <n*channels data bits>
 *       <3 px bits> <3 out bits>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "toc_internal.h"

void toc_lut1d_apply_pixel(const toc_op *op, float *px, int ch);

static uint64_t st = 0x9e3779b97f4a7c15ULL;
static uint32_t rnd(void) {
    uint64_t z = (st += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return (uint32_t)(z ^ (z >> 31));
}
static float rf(void) {
    uint32_t e = 120u + (rnd() % 16u);
    uint32_t b = (e << 23) | (rnd() & 0x7fffffu);
    float f; memcpy(&f, &b, 4); return f;
}
static void pf(float f) { uint32_t b; memcpy(&b, &f, 4); printf("%08x ", b); }

int main(void) {
    for (int k = 0; k < 120; ++k) {
        float m[16], off[4], px[4];
        for (int i = 0; i < 16; ++i) m[i] = rf();
        for (int i = 0; i < 4; ++i) off[i] = rf();
        for (int i = 0; i < 4; ++i) px[i] = rf();
        printf("mat ");
        for (int i = 0; i < 16; ++i) pf(m[i]);
        for (int i = 0; i < 4; ++i) pf(off[i]);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_matrix_batch_scalar(m, off, px, 1, 4);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        float sc[4], of[4], lo[4], hi[4], px[4];
        int cl = k & 1, ch = (k >> 1) & 1;
        for (int i = 0; i < 4; ++i) { sc[i] = rf(); of[i] = rf(); lo[i] = rf(); hi[i] = rf(); }
        for (int i = 0; i < 4; ++i) px[i] = rf();
        printf("range ");
        for (int i = 0; i < 4; ++i) pf(sc[i]);
        for (int i = 0; i < 4; ++i) pf(of[i]);
        for (int i = 0; i < 4; ++i) pf(lo[i]);
        for (int i = 0; i < 4; ++i) pf(hi[i]);
        printf("%d %d ", cl, ch);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_range_batch_scalar(sc, of, lo, hi, cl, ch, px, 1, 4);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        toc_op op;
        float px[4];
        int mirror = k & 1, ch = 1 + (k % 4);
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_EXPONENT;
        op.u.exponent.mirror = mirror;
        for (int i = 0; i < 4; ++i) op.u.exponent.e[i] = 0.5f + (float)(rnd() % 200) / 100.0f;
        for (int i = 0; i < 4; ++i) px[i] = (float)((int)(rnd() % 300) - 100) / 100.0f;
        printf("exp %d %d ", mirror, ch);
        for (int i = 0; i < 4; ++i) pf(op.u.exponent.e[i]);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_exponent_batch_scalar(&op, px, 1, ch);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        int n = 2 + (int)(rnd() % 14);
        int chans = (k & 1) ? 3 : 1;
        float data[16 * 3], px[3], result[3];
        toc_op op;
        for (int i = 0; i < n * chans; ++i) data[i] = rf();
        for (int i = 0; i < 3; ++i) px[i] = (float)((int)(rnd() % 200) - 50) / 100.0f;
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_LUT1D;
        op.u.lut1d.length = n;
        op.u.lut1d.channels = chans;
        op.u.lut1d.domain_min = 0.0f;
        op.u.lut1d.domain_max = 1.0f;
        op.u.lut1d.data = data;
        op.u.lut1d.interp = TOC_INTERP_LINEAR;
        memcpy(result, px, sizeof(result));
        toc_lut1d_apply_pixel(&op, result, 3);
        printf("lut %d %d %08x %08x ", n, chans, 0x00000000u, 0x3f800000u);
        for (int i = 0; i < n * chans; ++i) pf(data[i]);
        for (int i = 0; i < 3; ++i) pf(px[i]);
        for (int i = 0; i < 3; ++i) pf(result[i]);
        putchar('\n');
    }
    return 0;
}
