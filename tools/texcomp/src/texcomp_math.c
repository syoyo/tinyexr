/*
 * TinyEXR texcomp - libm-free math entry points (shared deps/math module).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "texcomp_internal.h"
#include "exr_math.h"
#include "exr_math_impl.h"

float tc_math_sqrtf_exact(float x) { return exr_math_i_sqrtf_exact(x); }
float tc_math_sqrtf(float x) { return exr_math_i_sqrtf(x); }
