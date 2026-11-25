/*
 * TinyEXR - core translation unit for the shared libm-free math module.
 *
 * The exr_util_* entry points keep their original (frozen) fast-tier bodies so
 * color/ACES output stays byte-identical. New call sites use the accurate tier
 * or the exact square root through the exr_math_* names.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr_internal.h"

#include "exr_math.h"
#include "exr_math_impl.h"

/* Frozen fast tier: core compatibility names. */
float exr_util_log2f(float x) { return exr_math_i_log2f_fast(x); }
float exr_util_exp2f(float x) { return exr_math_i_exp2f_fast(x); }
float exr_util_powf(float x, float y) { return exr_math_i_powf_fast(x, y); }
float exr_util_sqrtf(float x) { return exr_math_i_sqrtf_fast(x); }

/* Shared module entry points. */
float exr_math_log2f_fast(float x) { return exr_math_i_log2f_fast(x); }
float exr_math_exp2f_fast(float x) { return exr_math_i_exp2f_fast(x); }
float exr_math_powf_fast(float x, float y) { return exr_math_i_powf_fast(x, y); }
float exr_math_sqrtf_fast(float x) { return exr_math_i_sqrtf_fast(x); }

float exr_math_log2f(float x) { return exr_math_i_log2f(x); }
float exr_math_exp2f(float x) { return exr_math_i_exp2f(x); }
float exr_math_logf(float x) { return exr_math_i_logf(x); }
float exr_math_expf(float x) { return exr_math_i_expf(x); }
float exr_math_powf(float x, float y) { return exr_math_i_powf(x, y); }
float exr_math_sqrtf(float x) { return exr_math_i_sqrtf(x); }
float exr_math_sqrtf_exact(float x) { return exr_math_i_sqrtf_exact(x); }

double exr_math_sin(double x) { return exr_math_i_sin(x); }
double exr_math_cos(double x) { return exr_math_i_cos(x); }
double exr_math_exp64(double x) { return exr_math_i_exp64(x); }
double exr_math_sqrt64(double x) { return exr_math_i_sqrt64(x); }
double exr_math_floor64(double x) { return exr_math_i_floor64(x); }
double exr_math_ceil64(double x) { return exr_math_i_ceil64(x); }
double exr_math_fabs64(double x) { return exr_math_i_fabs64(x); }
