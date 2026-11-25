/*
 * TinyEXR - link smoke test for the four shipped libraries without -lm.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>

float exr_math_log2f(float x);
float tir_math_logf(float x);
float tc_math_sqrtf_exact(float x);
float toc_log2f(float x);

int main(void) {
    float a = exr_math_log2f(8.0f);
    float b = tir_math_logf(8.0f);
    float c = tc_math_sqrtf_exact(16.0f);
    float d = toc_log2f(8.0f);
    if (a < 2.99f || a > 3.01f || b < 2.07f || b > 2.09f ||
        c != 4.0f || d < 2.99f || d > 3.01f) {
        printf("libm-free smoke: FAIL (%f %f %f %f)\n", a, b, c, d);
        return 1;
    }
    printf("libm-free smoke: OK\n");
    return 0;
}
