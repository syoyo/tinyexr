/*
 * TinyEXR - public declarations for the shared libm-free math module.
 * See exr_math_impl.h for the tier contract and implementation.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#ifndef TINYEXR_MATH_H_
#define TINYEXR_MATH_H_

#ifdef __cplusplus
extern "C" {
#endif

/* Frozen fast tier (bit-compatible with the original exr_util_* / toc_*). */
float exr_math_log2f_fast(float x);
float exr_math_exp2f_fast(float x);
float exr_math_powf_fast(float x, float y);
float exr_math_sqrtf_fast(float x);

/* Accurate tier (f32-only op sequences, Lean-mirrored). */
float exr_math_log2f(float x);
float exr_math_exp2f(float x);
float exr_math_logf(float x);
float exr_math_expf(float x);
float exr_math_powf(float x, float y);
float exr_math_sqrtf(float x);

/* Integer-exact IEEE square root (0 ULP vs hardware/libm). */
float exr_math_sqrtf_exact(float x);

/* F64 helpers for build-time filter/task tables; no -lm required. */
double exr_math_sin(double x);
double exr_math_cos(double x);
double exr_math_exp64(double x);
double exr_math_sqrt64(double x);
double exr_math_floor64(double x);
double exr_math_ceil64(double x);
double exr_math_fabs64(double x);

#ifdef __cplusplus
}
#endif

#endif /* TINYEXR_MATH_H_ */
