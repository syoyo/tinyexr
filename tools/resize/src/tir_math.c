/*
 * tir - libm-free math entry points (shared deps/math implementation).
 *
 * The accurate f32 tier replaces libm logf/expf in the domain-compression
 * path; sqrt uses the integer-exact variant so libm's sqrtf bit pattern is
 * preserved. The f64 subset is used only when building filter tables.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "tir_internal.h"
#include "exr_math.h"
#include "exr_math_impl.h"

float tir_math_logf(float x) { return exr_math_i_logf(x); }
float tir_math_expf(float x) { return exr_math_i_expf(x); }
float tir_math_sqrtf_exact(float x) { return exr_math_i_sqrtf_exact(x); }

double tir_math_sin(double x) { return exr_math_i_sin(x); }
double tir_math_cos(double x) { return exr_math_i_cos(x); }
double tir_math_exp64(double x) { return exr_math_i_exp64(x); }
double tir_math_sqrt64(double x) { return exr_math_i_sqrt64(x); }
double tir_math_floor64(double x) { return exr_math_i_floor64(x); }
double tir_math_ceil64(double x) { return exr_math_i_ceil64(x); }
double tir_math_fabs64(double x) { return exr_math_i_fabs64(x); }
