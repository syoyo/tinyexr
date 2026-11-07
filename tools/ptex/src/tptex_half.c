/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Table-free half <-> float conversion, bit-identical to upstream PtexHalf
 * (PtexHalf.h, PtexHalf.cpp, PtexHalfTableGen.cpp). The exhaustive identity
 * proofs live in test/test_tptex_half.c and compare/cmp_half.cc.
 */
#include "../include/tptex_half.h"

#include <string.h>

uint32_t tptex_half_to_float_bits(uint16_t half) {
  const uint32_t h = half;
  const uint32_t s = (h & 0x8000u) << 16;
  const uint32_t m = h & 0x03ffu;
  const uint32_t e = h & 0x7c00u;

  if (e != 0u && e != 0x7c00u) {
    /* normal: rebias the exponent (15 -> 127) and widen the mantissa */
    return s | (((e + 0x1c000u) | m) << 13);
  }
  if (e == 0u) {
    /* denormal or zero: m * 2^-24 is exact in single precision */
    if (m == 0u) return s;
    uint32_t p = 9u; /* position of the most significant set bit of m */
    while ((m >> p) == 0u) --p;
    return s | ((p + 103u) << 23) | ((m << (23u - p)) & 0x7fffffu);
  }
  /* inf / nan: keep the low mantissa bits so NaN payloads survive */
  return s | 0x7f800000u | (m << 13);
}

uint16_t tptex_float_bits_to_half(uint32_t f) {
  if ((f & 0x7fffffffu) == 0u) return 0u; /* +-0.0f -> +0 (upstream drops the sign) */

  const uint32_t s = (f >> 16) & 0x8000u;
  const uint32_t exp32 = (f >> 23) & 0xffu;

  if (exp32 >= 113u && exp32 <= 142u) {
    /* normalized half range: add the round bit (0x1000) to the mantissa and
     * let the carry ripple into the exponent (overflow becomes infinity). */
    const uint32_t base = s | ((exp32 - 112u) << 10);
    return (uint16_t)(base + (((f & 0x7fffffu) + 0x1000u) >> 13));
  }
  if (exp32 <= 112u) {
    /* denormalized half (or underflow): round-half-up of |f| * 2^24, computed
     * exactly in integers. |f| = mant24 * 2^(E-150) with E = max(exp32, 1). */
    const uint32_t E = exp32 == 0u ? 1u : exp32;
    const uint32_t mant24 = (exp32 == 0u ? 0u : 0x800000u) | (f & 0x7fffffu);
    const uint32_t shift = 126u - E; /* 14 .. 125 */
    uint32_t r = 0u;
    if (shift < 32u)
      r = (uint32_t)(((uint64_t)mant24 + ((uint64_t)1 << (shift - 1u))) >> shift);
    return (uint16_t)(s | r);
  }
  if (exp32 == 255u) {
    /* inf / nan: keep the top mantissa bits (a payload with all-zero top bits
     * becomes infinity, as upstream does) */
    return (uint16_t)(s | 0x7c00u | ((f & 0x7fffffu) >> 13));
  }
  return (uint16_t)(s | 0x7c00u); /* overflow -> infinity */
}

float tptex_half_to_float(uint16_t half) {
  const uint32_t bits = tptex_half_to_float_bits(half);
  float value;
  memcpy(&value, &bits, sizeof value);
  return value;
}

uint16_t tptex_float_to_half(float value) {
  uint32_t bits;
  memcpy(&bits, &value, sizeof bits);
  return tptex_float_bits_to_half(bits);
}

void tptex_half_to_float_n(const uint16_t* src, float* dst, size_t count) {
  size_t i;
  for (i = 0; i < count; ++i) dst[i] = tptex_half_to_float(src[i]);
}

void tptex_float_to_half_n(const float* src, uint16_t* dst, size_t count) {
  size_t i;
  for (i = 0; i < count; ++i) dst[i] = tptex_float_to_half(src[i]);
}
