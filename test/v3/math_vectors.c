/*
 * TinyEXR - emit bit-exact vectors for the Lean math-model gate.
 *
 * Line format: <op> <in_bits> [<in2_bits>] <out_bits>
 * Ops: log2f exp2f logf expf powf sqrtf sqrtfExact
 *      log2fFast exp2fFast powfFast sqrtfFast
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdint.h>
#include <stdio.h>

#include "exr_math.h"

static uint32_t st = 0x9e3779b9u;
static uint32_t rnd(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return st;
}
static float b2f(uint32_t u) {
    union { uint32_t u; float f; } v;
    v.u = u; return v.f;
}
static uint32_t f2b(float f) {
    union { float f; uint32_t u; } v;
    v.f = f; return v.u;
}
static void emit1(const char *op, float x, float y) {
    printf("%s %08x %08x\n", op, f2b(x), f2b(y));
}
static void emit2(const char *op, float x, float y, float r) {
    printf("%s %08x %08x %08x\n", op, f2b(x), f2b(y), f2b(r));
}

int main(void) {
    static const uint32_t special[] = {
        0x00000000u, 0x80000000u, 0x00000001u, 0x00000002u,
        0x007fffffu, 0x00800000u, 0x3f800000u, 0x40000000u,
        0x7f7fffffu, 0x7f800000u, 0xff800000u, 0x7fc00000u
    };
    size_t k;
    int i;

    for (k = 0; k < sizeof(special) / sizeof(special[0]); ++k) {
        float x = b2f(special[k]);
        emit1("log2f", x, exr_math_log2f(x));
        emit1("exp2f", x, exr_math_exp2f(x));
        emit1("logf", x, exr_math_logf(x));
        emit1("expf", x, exr_math_expf(x));
        emit1("sqrtf", x, exr_math_sqrtf(x));
        emit1("sqrtfExact", x, exr_math_sqrtf_exact(x));
        emit1("log2fFast", x, exr_math_log2f_fast(x));
        emit1("exp2fFast", x, exr_math_exp2f_fast(x));
        emit1("sqrtfFast", x, exr_math_sqrtf_fast(x));
        emit2("powf", x, 2.0f, exr_math_powf(x, 2.0f));
        emit2("powfFast", x, 2.0f, exr_math_powf_fast(x, 2.0f));
    }

    for (i = 0; i < 512; ++i) {
        uint32_t b = rnd() & 0x7f7fffffu;
        float x = b2f(b);
        float y = (float)((int)(rnd() % 17) - 8);
        emit1("log2f", x, exr_math_log2f(x));
        emit1("exp2f", x, exr_math_exp2f(x));
        emit1("logf", x, exr_math_logf(x));
        emit1("sqrtf", x, exr_math_sqrtf(x));
        emit1("sqrtfExact", x, exr_math_sqrtf_exact(x));
        emit1("log2fFast", x, exr_math_log2f_fast(x));
        emit1("exp2fFast", x, exr_math_exp2f_fast(x));
        emit1("sqrtfFast", x, exr_math_sqrtf_fast(x));
        emit2("powf", x, y, exr_math_powf(x, y));
        emit2("powfFast", x, y, exr_math_powf_fast(x, y));
    }

    /* expf's useful domain is bounded; sample it densely. */
    for (i = 0; i < 512; ++i) {
        float x = -100.0f + 200.0f * (float)(rnd() & 0xffffffu) / 16777215.0f;
        emit1("expf", x, exr_math_expf(x));
    }
    return 0;
}
