/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Half-float identity tests. The reference below is a literal C transcription
 * of upstream PtexHalf (table generator PtexHalfTableGen.cpp, fromFloat,
 * fromFloat_except), including its double-precision denormal path, so the
 * table-free production code is checked against the table-driven algorithm it
 * must reproduce. compare/cmp_half.cc repeats the check against the real
 * upstream library.
 *
 * Default: all 65536 half->float inputs, every float exponent/sign with the
 * mantissa rounding thresholds, and a few million pseudo-random floats.
 * TPTEX_EXHAUSTIVE=1: all 2^32 float bit patterns.
 */
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "../include/tptex_half.h"
#include "tptex_test.h"

static uint32_t ref_h2f[65536];
static uint16_t ref_f2h[512];

static void ref_init(void) {
  int h, i;
  for (h = 0; h < 65536; ++h) {
    uint32_t s = ((uint32_t)h & 0x8000u) << 16;
    uint32_t m = (uint32_t)h & 0x03ffu;
    uint32_t e = (uint32_t)h & 0x7c00u;
    uint32_t bits;
    if ((e - 1u) < ((31u << 10) - 1u)) {
      bits = s | (((e + 0x1c000u) | m) << 13);
    } else if (e == 0u) {
      float f;
      if (!(h & 0x8000)) f = (float)(5.9604644775390625e-08 * (double)m);
      else f = (float)(-5.9604644775390625e-08 * (double)m);
      memcpy(&bits, &f, sizeof bits);
    } else {
      bits = s | 0x7f800000u | (m << 13);
    }
    ref_h2f[h] = bits;
  }
  for (i = 0; i < 512; ++i) {
    uint32_t f = (uint32_t)i << 23;
    int32_t e = (int32_t)((f & 0x7f800000u) - 0x38000000u);
    ref_f2h[i] = 0;
    if ((uint32_t)(e - 1) < ((31u << 23) - 1u)) {
      uint32_t s = (f >> 16) & 0x8000u;
      uint32_t m = f & 0x7fe000u;
      ref_f2h[i] = (uint16_t)((s | (((uint32_t)e | m) >> 13)) + ((f >> 12) & 1u));
    }
  }
}

static uint16_t ref_from_float_except(uint32_t i) {
  uint32_t s = ((i >> 16) & 0x8000u);
  int32_t e = (int32_t)((i >> 13) & 0x3fc00u) - 0x1c000;
  if (e <= 0) {
    float f;
    double scaled;
    memcpy(&f, &i, sizeof f);
    scaled = fabs((double)f) * 1.6777216e7 + .5;
    return (uint16_t)(s | (uint32_t)(int)scaled);
  }
  if (e == 0x23c00) return (uint16_t)(s | 0x7c00u | ((i & 0x7fffffu) >> 13));
  return (uint16_t)(s | 0x7c00u);
}

static uint16_t ref_from_float_bits(uint32_t u) {
  float v;
  int e;
  memcpy(&v, &u, sizeof v);
  if (v == 0) return 0;
  e = ref_f2h[(u >> 23) & 0x1ffu];
  if (e) return (uint16_t)((uint32_t)e + (((u & 0x7fffffu) + 0x1000u) >> 13));
  return ref_from_float_except(u);
}

static uint64_t g_mismatch = 0;

static void check_f2h(uint32_t bits) {
  uint16_t want = ref_from_float_bits(bits);
  uint16_t got = tptex_float_bits_to_half(bits);
  if (want != got) {
    if (g_mismatch++ < 8)
      fprintf(stderr, "  f2h mismatch: float bits 0x%08x want 0x%04x got 0x%04x\n", bits,
              want, got);
  }
}

static uint32_t xorshift32(uint32_t* s) {
  uint32_t x = *s;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  return *s = x;
}

void test_half(void) {
  uint32_t h, bits, rng = 0x1234567u;
  uint32_t sign, exp, i;
  static const uint32_t mants[] = {0x000000u, 0x000001u, 0x000fffu, 0x001000u, 0x001001u,
                                   0x001fffu, 0x002000u, 0x002001u, 0x7fe000u, 0x7fefffu,
                                   0x7ff000u, 0x7ff001u, 0x7fffffu, 0x400000u, 0x3fffffu,
                                   0x000800u, 0x7fe001u, 0x1fe000u};
  const int exhaustive = getenv("TPTEX_EXHAUSTIVE") && getenv("TPTEX_EXHAUSTIVE")[0] == '1';

  ref_init();

  /* half -> float over the full domain, bit-exact (incl. NaN payloads). */
  g_mismatch = 0;
  for (h = 0; h < 65536u; ++h) {
    if (tptex_half_to_float_bits((uint16_t)h) != ref_h2f[h]) {
      if (g_mismatch++ < 8) fprintf(stderr, "  h2f mismatch at 0x%04x\n", h);
    }
  }
  TPTEX_CHECK_EQ_U(g_mismatch, 0);

  /* float -> half: boundaries of every exponent/sign. */
  g_mismatch = 0;
  for (sign = 0; sign < 2u; ++sign)
    for (exp = 0; exp < 256u; ++exp)
      for (i = 0; i < sizeof mants / sizeof mants[0]; ++i)
        check_f2h((sign << 31) | (exp << 23) | mants[i]);
  TPTEX_CHECK_EQ_U(g_mismatch, 0);

  if (exhaustive) {
    bits = 0u;
    do {
      check_f2h(bits);
      ++bits;
    } while (bits != 0u);
  } else {
    /* dense stride (prime) over the whole space, plus pseudo-random bit patterns */
    for (bits = 0u; bits < 0xfffff000u; bits += 1021u) check_f2h(bits);
    for (i = 0; i < 4000000u; ++i) check_f2h(xorshift32(&rng));
  }
  TPTEX_CHECK_EQ_U(g_mismatch, 0);

  /* documented upstream quirks and anchor values */
  TPTEX_CHECK_EQ_U(tptex_float_to_half(1.0f), 0x3c00);
  TPTEX_CHECK_EQ_U(tptex_float_to_half(-2.0f), 0xc000);
  TPTEX_CHECK_EQ_U(tptex_float_to_half(65504.0f), 0x7bff);
  TPTEX_CHECK_EQ_U(tptex_float_to_half(65520.0f), 0x7c00);   /* round-half-up carries to inf */
  TPTEX_CHECK_EQ_U(tptex_float_to_half(1.0e9f), 0x7c00);     /* overflow */
  TPTEX_CHECK_EQ_U(tptex_float_to_half(0.0f), 0x0000);
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0x80000000u), 0x0000); /* -0.0f -> +0 */
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0x80000001u), 0x8000); /* neg float denormal -> -0 */
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0x7f800000u), 0x7c00); /* +inf */
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0xff800000u), 0xfc00); /* -inf */
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0x7fc00000u), 0x7e00); /* quiet NaN keeps its top bits */
  TPTEX_CHECK_EQ_U(tptex_float_bits_to_half(0x7f800001u), 0x7c00); /* NaN with zero top bits -> inf */
  TPTEX_CHECK_EQ_U(tptex_half_to_float_bits(0x0001), 0x33800000u); /* 2^-24 */
  TPTEX_CHECK_EQ_U(tptex_half_to_float_bits(0x8000), 0x80000000u); /* -0 stays -0 */
  TPTEX_CHECK_EQ_U(tptex_half_to_float_bits(0x7e01), 0x7fc02000u); /* NaN payload bits kept */

  /* every non-NaN half survives half -> float -> half, except that -0 loses
   * its sign (upstream quirk) */
  g_mismatch = 0;
  for (h = 0; h < 65536u; ++h) {
    uint32_t e = h & 0x7c00u, m = h & 0x3ffu;
    uint16_t back;
    if (e == 0x7c00u && m != 0u) continue; /* NaN */
    back = tptex_float_bits_to_half(tptex_half_to_float_bits((uint16_t)h));
    if (h == 0x8000u) { if (back != 0u) ++g_mismatch; }
    else if (back != (uint16_t)h) ++g_mismatch;
  }
  TPTEX_CHECK_EQ_U(g_mismatch, 0);

  /* float API is the bit API through memcpy */
  {
    float f = tptex_half_to_float(0x3c00);
    TPTEX_CHECK(f == 1.0f);
    TPTEX_CHECK_EQ_U(tptex_float_to_half(f), 0x3c00);
  }
}
