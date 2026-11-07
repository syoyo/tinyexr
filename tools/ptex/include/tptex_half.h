/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Half-precision conversion, bit-identical to upstream PtexHalf (which uses a
 * 65536-entry and a 512-entry lookup table; these routines are table-free).
 *
 * Intentional upstream quirks that are reproduced exactly:
 *  - float -> half is round-half-up on the magnitude (bit 12), not
 *    round-to-nearest-even; carries propagate into the exponent, so values
 *    that round past the largest finite half become infinity;
 *  - +-0.0f converts to +0 (the sign of a negative zero is dropped), while a
 *    negative float denormal converts to a signed zero;
 *  - a NaN whose top ten mantissa bits are zero converts to infinity;
 *  - half -> float keeps signed zeros, exact denormals and NaN payload bits.
 *
 * The *_bits variants operate on IEEE-754 bit patterns and involve no float
 * arithmetic at all, so they cannot be affected by x87 excess precision,
 * FMA contraction or fast-math.
 */
#ifndef TPTEX_HALF_H_
#define TPTEX_HALF_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

uint32_t tptex_half_to_float_bits(uint16_t half);
uint16_t tptex_float_bits_to_half(uint32_t float_bits);

float tptex_half_to_float(uint16_t half);
uint16_t tptex_float_to_half(float value);

/* Bulk helpers; `src` and `dst` may not overlap. */
void tptex_half_to_float_n(const uint16_t* src, float* dst, size_t count);
void tptex_float_to_half_n(const float* src, uint16_t* dst, size_t count);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_HALF_H_ */
