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
void toc_fixedfunc_apply_pixel(const toc_op *op, float *px, int ch);

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
        toc_op op;
        float px[4];
        int inv = k & 1, ch = 3 + (k & 1);
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_LOG;
        op.u.log.inverse = inv;
        op.u.log.base = 2.0f + (float)(k % 5);
        for (int i = 0; i < 3; ++i) {
            op.u.log.log_slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.log.log_offset[i] = (float)((int)(rnd() % 40) - 20) / 100.0f;
            op.u.log.lin_slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.log.lin_offset[i] = 0.05f + (float)(rnd() % 50) / 100.0f;
            px[i] = 0.1f + (float)(rnd() % 100) / 100.0f;
        }
        px[3] = 1.0f;
        printf("log %d %d ", inv, ch);
        for (int i = 0; i < 3; ++i) pf(op.u.log.log_slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.log.log_offset[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.log.lin_slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.log.lin_offset[i]);
        pf(op.u.log.base);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_log_batch_scalar(&op, px, 1, ch);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        toc_op op;
        float px[4];
        int inv = k & 1, ch = 3 + (k & 1);
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_LOG_CAMERA;
        op.u.logcam.inverse = inv;
        op.u.logcam.base = 2.0f + (float)(k % 5);
        for (int i = 0; i < 3; ++i) {
            op.u.logcam.log_slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.logcam.log_offset[i] = (float)((int)(rnd() % 40) - 20) / 100.0f;
            op.u.logcam.lin_slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.logcam.lin_offset[i] = 0.05f + (float)(rnd() % 50) / 100.0f;
            op.u.logcam.lin_break[i] = 0.1f + (float)(rnd() % 50) / 100.0f;
            op.u.logcam.linear_slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.logcam.linear_offset[i] = (float)((int)(rnd() % 40) - 20) / 100.0f;
            px[i] = 0.1f + (float)(rnd() % 100) / 100.0f;
        }
        px[3] = 1.0f;
        printf("logcam %d %d ", inv, ch);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.log_slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.log_offset[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.lin_slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.lin_offset[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.lin_break[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.linear_slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.logcam.linear_offset[i]);
        pf(op.u.logcam.base);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_logcam_batch_scalar(&op, px, 1, ch);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        toc_op op;
        float px[4];
        int inv = k & 1, mirror = (k >> 1) & 1, ch = 1 + (k % 4);
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_EXP_LINEAR;
        op.u.exp_linear.inverse = inv;
        op.u.exp_linear.mirror = mirror;
        for (int i = 0; i < 4; ++i) {
            op.u.exp_linear.scale[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.exp_linear.offset[i] = (float)((int)(rnd() % 40) - 20) / 100.0f;
            op.u.exp_linear.gamma[i] = 0.5f + (float)(rnd() % 200) / 100.0f;
            op.u.exp_linear.breakpoint[i] = (float)(rnd() % 100) / 100.0f;
            op.u.exp_linear.slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            px[i] = (float)((int)(rnd() % 300) - 100) / 100.0f;
        }
        printf("exlin %d %d %d ", inv, mirror, ch);
        for (int i = 0; i < 4; ++i) pf(op.u.exp_linear.scale[i]);
        for (int i = 0; i < 4; ++i) pf(op.u.exp_linear.offset[i]);
        for (int i = 0; i < 4; ++i) pf(op.u.exp_linear.gamma[i]);
        for (int i = 0; i < 4; ++i) pf(op.u.exp_linear.breakpoint[i]);
        for (int i = 0; i < 4; ++i) pf(op.u.exp_linear.slope[i]);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_explin_batch_scalar(&op, px, 1, ch);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        toc_op op;
        float px[4];
        int inv = k & 1, cl = (k >> 1) & 1;
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_CDL;
        op.u.cdl.inverse = inv;
        op.u.cdl.clamp = cl;
        op.u.cdl.saturation = 0.2f + (float)(rnd() % 100) / 100.0f;
        for (int i = 0; i < 3; ++i) {
            op.u.cdl.slope[i] = 0.5f + (float)(rnd() % 150) / 100.0f;
            op.u.cdl.offset[i] = (float)((int)(rnd() % 40) - 20) / 100.0f;
            op.u.cdl.power[i] = 0.5f + (float)(rnd() % 200) / 100.0f;
            op.u.cdl.luma[i] = (i == 0 && (k & 4)) ? 0.0f
                             : 0.1f + (float)(rnd() % 80) / 100.0f;
            px[i] = (float)((int)(rnd() % 200) - 50) / 100.0f;
        }
        px[3] = 1.0f;
        printf("cdl %d %d ", inv, cl);
        for (int i = 0; i < 3; ++i) pf(op.u.cdl.slope[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.cdl.offset[i]);
        for (int i = 0; i < 3; ++i) pf(op.u.cdl.power[i]);
        pf(op.u.cdl.saturation);
        for (int i = 0; i < 3; ++i) pf(op.u.cdl.luma[i]);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_cdl_batch_scalar(&op, px, 1, 4);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        putchar('\n');
    }
    for (int k = 0; k < 120; ++k) {
        static const int styles[] = {8, 9, 2, 3, 0, 1, 6, 7, 10, 11,
                                     12, 13, 14, 15, 16, 17, 18, 19,
                                     20, 21, 22, 23, 24, 25};
        toc_op op;
        float px[4];
        int style = styles[k % (int)(sizeof(styles) / sizeof(styles[0]))];
        memset(&op, 0, sizeof(op));
        op.kind = TOC_OP_FIXEDFUNC;
        op.u.fixedfunc.style = style;
        op.u.fixedfunc.nparams = (style == 4 || style == 5) ? 7 : 2;
        for (int i = 0; i < op.u.fixedfunc.nparams; ++i)
            op.u.fixedfunc.params[i] = 0.2f + (float)(rnd() % 100) / 100.0f;
        for (int i = 0; i < 3; ++i) px[i] = (float)(rnd() % 100) / 100.0f;
        px[3] = 1.0f;
        printf("ff %d %d ", style, op.u.fixedfunc.nparams);
        for (int i = 0; i < 8; ++i) pf(op.u.fixedfunc.params[i]);
        for (int i = 0; i < 4; ++i) pf(px[i]);
        toc_fixedfunc_apply_pixel(&op, px, 4);
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
