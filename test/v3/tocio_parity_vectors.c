/*
 * tocio - JIT/SIMD parity gate.
 *
 * Compares the x64 JIT output and every SIMD tier against the scalar
 * interpreter on the same randomized pixels. Reports mismatches and exits
 * non-zero on any difference (JIT may skip with a notice when unsupported).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tocio.h"
#include "toc_internal.h"

static uint32_t st = 0x9e3779b9u;
static uint32_t rnd(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return st;
}

static toc_op_list *newlist(void) {
    const toc_allocator *a = toc_default_allocator();
    toc_op_list *l = (toc_op_list *)malloc(sizeof(*l));
    if (!l) return NULL;
    memset(l, 0, sizeof(*l));
    l->alloc = *a;
    return l;
}

static void build_ops(toc_op_list *l) {
    toc_op *o;
    int c;
    o = toc_op_list_push(l, TOC_OP_MATRIX);
    if (o) for (c = 0; c < 16; ++c) o->u.matrix.m[c] = (c % 5 == 0) ? 1.1f : 0.01f;
    o = toc_op_list_push(l, TOC_OP_EXPONENT);
    if (o) {
        o->u.exponent.mirror = 1;
        for (c = 0; c < 4; ++c) o->u.exponent.e[c] = 1.0f + (float)c * 0.05f;
    }
    o = toc_op_list_push(l, TOC_OP_RANGE);
    if (o) {
        for (c = 0; c < 4; ++c) {
            o->u.range.scale[c] = 1.2f; o->u.range.offset[c] = -0.1f;
            o->u.range.min[c] = 0.0f; o->u.range.max[c] = 4.0f;
        }
        o->u.range.clamp_lo = 1; o->u.range.clamp_hi = 1;
    }
    o = toc_op_list_push(l, TOC_OP_EXP_LINEAR);
    if (o) {
        o->u.exp_linear.mirror = 1;
        for (c = 0; c < 4; ++c) {
            o->u.exp_linear.scale[c] = 1.3f; o->u.exp_linear.offset[c] = 0.05f;
            o->u.exp_linear.gamma[c] = 1.1f + (float)c * 0.05f;
            o->u.exp_linear.breakpoint[c] = 0.18f; o->u.exp_linear.slope[c] = 1.0f;
        }
    }
    o = toc_op_list_push(l, TOC_OP_LOG);
    if (o) {
        o->u.log.base = 10.0f;
        for (c = 0; c < 3; ++c) {
            o->u.log.log_slope[c] = 1.0f; o->u.log.log_offset[c] = 0.0f;
            o->u.log.lin_slope[c] = 1.0f; o->u.log.lin_offset[c] = 0.0f;
        }
    }
    o = toc_op_list_push(l, TOC_OP_LOG_CAMERA);
    if (o) {
        o->u.logcam.base = 2.0f;
        for (c = 0; c < 3; ++c) {
            o->u.logcam.log_slope[c] = 1.0f; o->u.logcam.log_offset[c] = 0.0f;
            o->u.logcam.lin_slope[c] = 1.0f; o->u.logcam.lin_offset[c] = 0.0f;
            o->u.logcam.lin_break[c] = 0.1f; o->u.logcam.linear_slope[c] = 1.0f;
            o->u.logcam.linear_offset[c] = 0.0f;
        }
    }
}

static int same(const float *a, const float *b, size_t n) {
    size_t i;
    for (i = 0; i < n; ++i)
        if (memcmp(&a[i], &b[i], sizeof(float)) != 0) return 0;
    return 1;
}

int main(void) {
    enum { NP = 256, NC = 4 };
    static float base[NP * NC], ref[NP * NC], got[NP * NC];
    toc_op_list *l = newlist();
    toc_jit *jit = NULL;
    toc_jit_fn fn;
    int i, c, bad = 0, level;
    for (i = 0; i < NP * NC; ++i) {
        uint32_t b = (rnd() & 0x00ffffffu) | 0x3d800000u; /* [0.0625,0.5) */
        memcpy(&base[i], &b, 4);
        if (i % 7 == 0) base[i] = -base[i];
    }
    build_ops(l);

    toc_simd_force(0);
    memcpy(ref, base, sizeof(ref));
    toc_apply(l, ref, NP, NC);

    for (level = 1; level <= 2; ++level) {
        toc_simd_force(level);
        memcpy(got, base, sizeof(got));
        toc_apply(l, got, NP, NC);
        printf("simd level %d: %s\n", level, same(ref, got, NP * NC) ? "OK" : "FAIL");
        if (!same(ref, got, NP * NC)) bad = 1;
    }
    toc_simd_force(0);

    if (TOC_OK(toc_jit_compile(l, NC, NULL, &jit)) && jit) {
        fn = toc_jit_func(jit);
        if (fn) {
            memcpy(got, base, sizeof(got));
            fn(got, NP);
            printf("jit: %s\n", same(ref, got, NP * NC) ? "OK" : "FAIL");
            if (!same(ref, got, NP * NC)) bad = 1;
        }
        toc_jit_destroy(jit);
    } else {
        printf("jit: SKIP (unsupported on this target)\n");
    }
    (void)c;
    toc_op_list_free(l);
    printf("tocio parity: %s\n", bad ? "FAIL" : "OK");
    return bad;
}
