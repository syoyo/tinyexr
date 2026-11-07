/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Unit tests for the PtexUtils port: hand-checked values and algebraic
 * properties. Bit-exactness against the real upstream functions is checked by
 * compare/cmp_utils.cc (make ptex-compare).
 */
#include <string.h>

#include "../include/tptex_half.h"
#include "../include/tptex_utils.h"
#include "tptex_test.h"

static uint32_t rng_state = 0x9e3779b9u;
static uint32_t rnd(void) {
  uint32_t x = rng_state;
  x ^= x << 13; x ^= x >> 17; x ^= x << 5;
  return rng_state = x;
}

static void test_reduce(void) {
  /* 2x2 u8, 1 channel: (10+20+30+40)>>2 = 25 */
  const uint8_t a[4] = {10, 20, 30, 40};
  uint8_t out = 0;
  tptex_reduce(a, 2, 2, 2, &out, 1, TPTEX_UINT8, 1);
  TPTEX_CHECK_EQ_U(out, 25);
  /* integer truncation: (1+1+1+2)>>2 = 1 */
  {
    const uint8_t b[4] = {1, 1, 1, 2};
    tptex_reduce(b, 2, 2, 2, &out, 1, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(out, 1);
  }
  /* u only / v only */
  {
    const uint8_t c[4] = {10, 30, 50, 70}; /* 2x2 */
    uint8_t ou[2], ov[2];
    tptex_reduce_u(c, 2, 2, 2, ou, 1, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(ou[0], 20);
    TPTEX_CHECK_EQ_U(ou[1], 60);
    tptex_reduce_v(c, 2, 2, 2, ov, 2, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(ov[0], 30); /* (10+50)/2 */
    TPTEX_CHECK_EQ_U(ov[1], 50); /* (30+70)/2 */
  }
  /* float: exact 0.25 scale */
  {
    const float f[4] = {1.0f, 2.0f, 3.0f, 6.0f};
    float of = 0.0f;
    tptex_reduce(f, 8, 2, 2, &of, 4, TPTEX_FLOAT, 1);
    TPTEX_CHECK(of == 3.0f);
  }
  /* triangle reduction of a 2x2 packed block uses the mirrored pixel (row 1,col 1) */
  {
    const uint8_t t[4] = {4, 8, 12, 16}; /* rows: [4 8],[12 16]; output = (4+8+12+16)>>2 */
    uint8_t ot = 0;
    tptex_reduce_tri(t, 2, 2, &ot, 1, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(ot, 10);
  }
  /* 4x4 triangle block: spot-check one output with the documented formula */
  {
    uint8_t src[16], dst[4];
    int i;
    for (i = 0; i < 16; ++i) src[i] = (uint8_t)(i * 10);
    tptex_reduce_tri(src, 4, 4, dst, 2, TPTEX_UINT8, 1);
    /* out(x=1,y=0): src[0][2]+src[0][3]+src[1][2] + mirrored(row 4-1-2=1, col 3) */
    TPTEX_CHECK_EQ_U(dst[1], (src[2] + src[3] + src[6] + src[7]) >> 2);
    /* out(x=0,y=1): src[2][0]+src[2][1]+src[3][0] + mirrored(row 3, col 4-1-2=1) */
    TPTEX_CHECK_EQ_U(dst[2], (src[8] + src[9] + src[12] + src[13]) >> 2);
  }
}

static void test_difference(void) {
  uint8_t b[256], orig[256];
  uint16_t w[128], worig[128];
  size_t i;
  for (i = 0; i < 256; ++i) b[i] = orig[i] = (uint8_t)rnd();
  tptex_encode_difference(b, sizeof b, TPTEX_UINT8);
  TPTEX_CHECK(memcmp(b, orig, sizeof b) != 0);
  tptex_decode_difference(b, sizeof b, TPTEX_UINT8);
  TPTEX_CHECK(memcmp(b, orig, sizeof b) == 0);
  for (i = 0; i < 128; ++i) w[i] = worig[i] = (uint16_t)rnd();
  tptex_encode_difference(w, sizeof w, TPTEX_UINT16);
  tptex_decode_difference(w, sizeof w, TPTEX_UINT16);
  TPTEX_CHECK(memcmp(w, worig, sizeof w) == 0);
  /* float/half are untouched */
  {
    float f[4] = {1.f, 2.f, 3.f, 4.f}, g[4] = {1.f, 2.f, 3.f, 4.f};
    tptex_encode_difference(f, sizeof f, TPTEX_FLOAT);
    TPTEX_CHECK(memcmp(f, g, sizeof f) == 0);
  }
}

static void test_interleave(void) {
  enum { U = 5, V = 3, N = 4 };
  uint8_t planar[N * V * U], inter[V * U * N], back[N * V * U];
  size_t i;
  for (i = 0; i < sizeof planar; ++i) planar[i] = (uint8_t)(i * 7 + 1);
  tptex_interleave(planar, U, U, V, inter, (size_t)U * N, TPTEX_UINT8, N);
  /* pixel (2,1) channel 3 comes from plane 3, row 1, col 2 */
  TPTEX_CHECK_EQ_U(inter[(1 * U + 2) * N + 3], planar[3 * V * U + 1 * U + 2]);
  tptex_deinterleave(inter, (size_t)U * N, U, V, back, U, TPTEX_UINT8, N);
  TPTEX_CHECK(memcmp(planar, back, sizeof planar) == 0);
}

static void test_alpha(void) {
  /* premultiply then un-premultiply on u8 with alpha last: rgb scaled by a/255 */
  uint8_t px[4] = {200, 100, 50, 128};
  tptex_multalpha(px, 1, TPTEX_UINT8, 4, 3);
  TPTEX_CHECK_EQ_U(px[0], (uint8_t)(200.0f * (128.0f * (1.f / 255.f))));
  TPTEX_CHECK_EQ_U(px[3], 128);
  /* alpha == 0 is skipped by divalpha */
  {
    uint8_t z[4] = {7, 8, 9, 0};
    tptex_divalpha(z, 1, TPTEX_UINT8, 4, 3);
    TPTEX_CHECK_EQ_U(z[0], 7);
  }
  /* alpha in channel 0 multiplies the rest */
  {
    float f[3] = {0.5f, 0.8f, 0.4f};
    tptex_multalpha(f, 1, TPTEX_FLOAT, 3, 0);
    TPTEX_CHECK(f[0] == 0.5f);
    TPTEX_CHECK(f[1] == 0.8f * 0.5f);
  }
}

static void test_rfaceids(void) {
  tptex_face_info f[5];
  uint32_t r[5], ids[5];
  int i;
  memset(f, 0, sizeof f);
  f[0].res = tptex_make_res(4, 6); /* key 4 */
  f[1].res = tptex_make_res(6, 6); /* key 6 */
  f[2].res = tptex_make_res(4, 4); /* key 4 (ties keep face order) */
  f[3].res = tptex_make_res(9, 9); f[3].flags = TPTEX_FACE_CONSTANT; /* key 1 */
  f[4].res = tptex_make_res(5, 3); /* key 3 */
  tptex_gen_rfaceids(f, 5, r, ids);
  /* descending key, stable: 1(6), 0(4), 2(4), 4(3), 3(1) */
  TPTEX_CHECK_EQ_U(ids[0], 1); TPTEX_CHECK_EQ_U(ids[1], 0); TPTEX_CHECK_EQ_U(ids[2], 2);
  TPTEX_CHECK_EQ_U(ids[3], 4); TPTEX_CHECK_EQ_U(ids[4], 3);
  for (i = 0; i < 5; ++i) TPTEX_CHECK_EQ_U(ids[r[i]], i);
}

static void test_convert(void) {
  float f[3] = {0.0f, 0.5f, 1.0f};
  uint8_t u[3];
  float back[3];
  tptex_convert_from_float(u, f, TPTEX_UINT8, 3);
  TPTEX_CHECK_EQ_U(u[0], 0); TPTEX_CHECK_EQ_U(u[1], 128); TPTEX_CHECK_EQ_U(u[2], 255);
  tptex_convert_to_float(back, u, TPTEX_UINT8, 3);
  TPTEX_CHECK(back[2] == 255.f * (1.f / 255.f));
  /* clamping and NaN handling */
  {
    float in[3] = {-4.0f, 7.0f, 0.0f / 0.0f};
    uint8_t o[3];
    in[2] = in[2] * 0.0f; /* NaN */
    tptex_convert_from_float(o, in, TPTEX_UINT8, 3);
    TPTEX_CHECK_EQ_U(o[0], 0); TPTEX_CHECK_EQ_U(o[1], 255); TPTEX_CHECK_EQ_U(o[2], 0);
  }
  /* half: -0 widens to +0 through the `+ round` term, like upstream */
  {
    const uint16_t nz = 0x8000u;
    float o;
    uint32_t bits;
    tptex_convert_to_float(&o, &nz, TPTEX_HALF, 1);
    memcpy(&bits, &o, 4);
    TPTEX_CHECK_EQ_U(bits, 0);
  }
}

static void test_blend_average(void) {
  const uint8_t src[2] = {100, 50};
  uint8_t dst[2] = {10, 10};
  tptex_blend(src, 0.5f, dst, 0, 2, TPTEX_UINT8, 1);
  TPTEX_CHECK_EQ_U(dst[0], 60); TPTEX_CHECK_EQ_U(dst[1], 35);
  { uint8_t d2[2] = {10, 10}; tptex_blend(src, 0.5f, d2, 1, 2, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(d2[0], 35); TPTEX_CHECK_EQ_U(d2[1], 60); }
  {
    const uint8_t blk[4] = {10, 20, 30, 41};
    uint8_t avg;
    tptex_average(blk, 2, 2, 2, &avg, TPTEX_UINT8, 1);
    TPTEX_CHECK_EQ_U(avg, 25); /* 101/4 = 25.25 truncates */
  }
}

static void test_const_fill(void) {
  uint8_t buf[12], px[3] = {1, 2, 3};
  tptex_fill(px, buf, 6, 2, 2, 3);
  TPTEX_CHECK(tptex_is_constant(buf, 6, 2, 2, 3));
  buf[10] = 9;
  TPTEX_CHECK(!tptex_is_constant(buf, 6, 2, 2, 3));
  {
    float acc[2] = {1.0f, 1.0f};
    const uint8_t d[2] = {10, 20};
    tptex_apply_const(0.5f, acc, d, TPTEX_UINT8, 2);
    TPTEX_CHECK(acc[0] == 6.0f && acc[1] == 11.0f);
  }
}

void test_utils(void) {
  test_reduce();
  test_difference();
  test_interleave();
  test_alpha();
  test_rfaceids();
  test_convert();
  test_blend_average();
  test_const_fill();
}
