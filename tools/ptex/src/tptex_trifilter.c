/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Triangle-mesh elliptical gaussian filter: a C11 port of PtexTriangleFilter.cpp
 * and PtexTriangleKernel.{h,cpp}. A face is applied as one block rather than
 * tile by tile (only the float summation order differs).
 */
#include <math.h>

#include "../include/tptex_utils.h"
#include "tptex_filter_internal.h"

#define KERNEL_WIDTH 3.5f /* PtexTriangleKernelWidth */

typedef struct tkern {
  tptex_res res;
  float u, v;
  float u1, v1, w1;
  float u2, v2, w2;
  float A, B, C;
} tkern;

typedef struct titer {
  int rowlen;
  float u, v;
  int u1, v1, w1;
  int u2, v2, w2;
  float A, B, C;
  int valid;
  float wscale;
  float weight;
} titer;

static float minf_(float a, float b) { return a < b ? a : b; }
static float maxf_(float a, float b) { return a > b ? a : b; }
static int mini_(int a, int b) { return a < b ? a : b; }
static int maxi_(int a, int b) { return a > b ? a : b; }
static float squared(float x) { return x * x; }
static int finite_f(float x) { return x - x == 0.0f; }

static float gaussian(float x_squared) {
  static const float scale = -0.5f * (KERNEL_WIDTH * KERNEL_WIDTH);
  return (float)exp((double)(scale * x_squared));
}

static void tk_set(tkern* k, float u, float v, float u1, float v1, float w1, float u2, float v2, float w2) {
  k->u = u; k->v = v;
  k->u1 = u1; k->v1 = v1; k->w1 = w1;
  k->u2 = u2; k->v2 = v2; k->w2 = w2;
}
static void tk_set_abc(tkern* k, float A, float B, float C) { k->A = A; k->B = B; k->C = C; }
static void tk_rotate1(tkern* k) { tk_set_abc(k, k->C, 2.0f * k->C - k->B, k->A + k->C - k->B); }
static void tk_rotate2(tkern* k) { tk_set_abc(k, k->A + k->C - k->B, 2.0f * k->A - k->B, k->A); }

static void tk_reorient(tkern* k, int eid, int aeid) {
  const float u = k->u, v = k->v, w = 1.0f - u - v;
  const float u1 = k->u1, v1 = k->v1, w1 = k->w1, u2 = k->u2, v2 = k->v2, w2 = k->w2;
  switch (eid * 3 + aeid) {
    case 0: tk_set(k, 1.0f - u, -v, 1.0f - u2, -v2, 1.0f - w2, 1.0f - u1, -v1, 1.0f - w1); break;
    case 1: tk_set(k, 1.0f - w, 1.0f - u, 1.0f - w2, 1.0f - u2, -v2, 1.0f - w1, 1.0f - u1, -v1); tk_rotate1(k); break;
    case 2: tk_set(k, -v, 1.0f - w, -v2, 1.0f - w2, 1.0f - u2, -v1, 1.0f - w1, 1.0f - u1); tk_rotate2(k); break;
    case 3: tk_set(k, 1.0f - v, -w, 1.0f - v2, -w2, 1.0f - u2, 1.0f - v1, -w1, 1.0f - u1); tk_rotate2(k); break;
    case 4: tk_set(k, 1.0f - u, 1.0f - v, 1.0f - u2, 1.0f - v2, -w2, 1.0f - u1, 1.0f - v1, -w1); break;
    case 5: tk_set(k, -w, 1.0f - u, -w2, 1.0f - u2, 1.0f - v2, -w1, 1.0f - u1, 1.0f - v1); tk_rotate1(k); break;
    case 6: tk_set(k, 1.0f - w, -u, 1.0f - w2, -u2, 1.0f - v2, 1.0f - w1, -u1, 1.0f - v1); tk_rotate1(k); break;
    case 7: tk_set(k, 1.0f - v, 1.0f - w, 1.0f - v2, 1.0f - w2, -u2, 1.0f - v1, 1.0f - w1, -u1); tk_rotate2(k); break;
    case 8: tk_set(k, -u, 1.0f - v, -u2, 1.0f - v2, 1.0f - w2, -u1, 1.0f - v1, 1.0f - w1); break;
    default: break;
  }
}

static void tk_clamp_res(tkern* k, tptex_res fres) {
  k->res.ulog2 = k->res.ulog2 < fres.ulog2 ? k->res.ulog2 : fres.ulog2;
  k->res.vlog2 = k->res.ulog2;
}

static void tk_clamp_extent(tkern* k) {
  k->u1 = maxf_(k->u1, 0.0f);
  k->v1 = maxf_(k->v1, 0.0f);
  k->w1 = maxf_(k->w1, 0.0f);
  k->u2 = minf_(k->u2, 1.0f - (k->v1 + k->w1));
  k->v2 = minf_(k->v2, 1.0f - (k->w1 + k->u1));
  k->w2 = minf_(k->w2, 1.0f - (k->u1 + k->v1));
}

static int tk_finite(const tkern* k) {
  return finite_f(k->u) && finite_f(k->v) && finite_f(k->u1) && finite_f(k->v1) && finite_f(k->w1) &&
         finite_f(k->u2) && finite_f(k->v2) && finite_f(k->w2) && finite_f(k->A) && finite_f(k->B) &&
         finite_f(k->C);
}

static void tk_get_iterators(const tkern* k, titer* ke, titer* ko) {
  const int resu = 1 << k->res.ulog2;
  const float third = (float)(1 / 3.0);
  float Finv = 1.0f / ((float)resu * (float)resu * (k->A * k->C - 0.25f * k->B * k->B));
  float Ak = k->A * Finv, Bk = k->B * Finv, Ck = k->C * Finv, scale;
  ke->rowlen = resu;
  ke->wscale = 1.0f / ((float)resu * (float)resu);
  scale = (float)ke->rowlen;
  ke->u = k->u * scale - third;
  ke->v = k->v * scale - third;
  ke->u1 = tptex__fl_to_int(tptex__fl_ceil(k->u1 * scale - third));
  ke->v1 = tptex__fl_to_int(tptex__fl_ceil(k->v1 * scale - third));
  ke->w1 = tptex__fl_to_int(tptex__fl_ceil(k->w1 * scale - third));
  ke->u2 = tptex__fl_to_int(tptex__fl_ceil(k->u2 * scale - third));
  ke->v2 = tptex__fl_to_int(tptex__fl_ceil(k->v2 * scale - third));
  ke->w2 = tptex__fl_to_int(tptex__fl_ceil(k->w2 * scale - third));
  ke->A = Ak; ke->B = Bk; ke->C = Ck;
  ke->valid = ke->u2 > ke->u1 && ke->v2 > ke->v1 && ke->w2 > ke->w1;
  ke->weight = 0.0f;

  ko->rowlen = ke->rowlen;
  ko->wscale = ke->wscale;
  ko->u = (1.0f - k->v) * scale - third;
  ko->v = (1.0f - k->u) * scale - third;
  ko->u1 = tptex__fl_to_int(tptex__fl_ceil((1.0f - k->v2) * scale - third));
  ko->v1 = tptex__fl_to_int(tptex__fl_ceil((1.0f - k->u2) * scale - third));
  ko->w1 = tptex__fl_to_int(tptex__fl_ceil((-k->w2) * scale - third));
  ko->u2 = tptex__fl_to_int(tptex__fl_ceil((1.0f - k->v1) * scale - third));
  ko->v2 = tptex__fl_to_int(tptex__fl_ceil((1.0f - k->u1) * scale - third));
  ko->w2 = tptex__fl_to_int(tptex__fl_ceil((-k->w1) * scale - third));
  ko->A = Ck; ko->B = Bk; ko->C = Ak;
  ko->valid = ko->u2 > ko->u1 && ko->v2 > ko->v1 && ko->w2 > ko->w1;
  ko->weight = 0.0f;
}

/* iterator extents must lie inside the face for the data walk to stay in bounds */
static int ti_in_bounds(const titer* k) {
  return k->u1 >= 0 && k->v1 >= 0 && k->u2 <= k->rowlen && k->v2 <= k->rowlen && k->u1 <= k->u2 &&
         k->v1 <= k->v2;
}

/* dst += gaussian-weighted sum over the iterator; Q by finite differences (Heckbert) */
static void ti_apply(const tptex_filter* F, titer* k, float* dst, const uint8_t* data) {
  const size_t es = F->dtsize, pstride = (size_t)F->ntxchan * es;
  const float DDQ = 2.0f * k->A;
  int vi, c;
  for (vi = k->v1; vi != k->v2; ++vi) {
    const int xw = k->rowlen - vi;
    const int x1 = maxi_(k->u1, xw - k->w2), x2 = mini_(k->u2, xw - k->w1);
    const float U = (float)x1 - k->u, V = (float)vi - k->v;
    float DQ = k->A * (2.0f * U + 1.0f) + k->B * V;
    float Q = k->A * U * U + (k->B * U + k->C * V) * V;
    const uint8_t* p = data + ((size_t)vi * (size_t)k->rowlen + (size_t)(x1 < 0 ? 0 : x1)) * pstride + F->firstoff;
    int x;
    if (x1 < 0 || x2 > k->rowlen) continue; /* cannot happen for valid extents */
    for (x = x1; x < x2; ++x, p += pstride) {
      if (Q < 1.0f) {
        float weight = gaussian(Q) * k->wscale;
        k->weight += weight;
        for (c = 0; c < F->nchan; ++c) dst[c] += tptex__fl_rd(p + (size_t)c * es, F->dt) * weight;
      }
      Q += DQ;
      DQ += DDQ;
    }
  }
}

static void ti_apply_const(titer* k, float* dst, const uint8_t* pixel, tptex_data_type dt, int nchan) {
  const float DDQ = 2.0f * k->A;
  int vi;
  for (vi = k->v1; vi != k->v2; ++vi) {
    const int xw = k->rowlen - vi;
    const int x1 = maxi_(k->u1, xw - k->w2), x2 = mini_(k->u2, xw - k->w1);
    const float U = (float)x1 - k->u, V = (float)vi - k->v;
    float DQ = k->A * (2.0f * U + 1.0f) + k->B * V;
    float Q = k->A * U * U + (k->B * U + k->C * V) * V;
    int x;
    for (x = x1; x < x2; ++x) {
      if (Q < 1.0f) k->weight += gaussian(Q) * k->wscale;
      Q += DQ;
      DQ += DDQ;
    }
  }
  tptex_apply_const(k->weight, dst, pixel, dt, nchan);
}

static void tri_split_and_apply(tptex_filter* F, tkern* k, int faceid, const tptex_face_info* f);

static void tri_apply(tptex_filter* F, tkern* k, int faceid, const tptex_face_info* f) {
  titer ke, ko;
  tptex_face_data fd;
  tptex_status st;
  titer* its[2];
  int i;
  if (F->err) return;
  if (!tk_finite(k)) { F->err = TPTEX_E_LIMIT; return; }
  tk_clamp_res(k, f->res);
  tk_clamp_extent(k);
  if (k->res.ulog2 < 0) { F->err = TPTEX_E_CORRUPT; return; }
  tk_get_iterators(k, &ke, &ko);
  if (!ke.valid && !ko.valid) return;
  if ((ke.valid && !ti_in_bounds(&ke)) || (ko.valid && !ti_in_bounds(&ko))) { F->err = TPTEX_E_LIMIT; return; }
  st = tptex_get_face_data(F->tx, faceid, k->res, &fd);
  if (st != TPTEX_OK) { F->err = st; return; }
  its[0] = &ke;
  its[1] = &ko;
  for (i = 0; i < 2; ++i) {
    titer* it = its[i];
    if (!it->valid) continue;
    if (fd.is_constant) {
      ti_apply_const(it, F->result, (const uint8_t*)fd.data + F->firstoff, F->dt, F->nchan);
      F->weight += it->weight;
    } else {
      ti_apply(F, it, F->result, (const uint8_t*)fd.data);
      F->weight += it->weight;
    }
  }
  tptex_release_face_data(F->tx, &fd);
}

static void tri_apply_across_edge(tptex_filter* F, tkern* k, const tptex_face_info* f, int eid) {
  int afid = f->adjfaces[eid], aeid = (int)tptex_face_adjedge(f, eid), ok;
  tptex_face_info af;
  if (!tptex__fl_adj_ok(F, afid) || aeid > 2) { F->err = TPTEX_E_CORRUPT; return; }
  ok = tptex_get_face_info(F->tx, afid, &af) == TPTEX_OK;
  if (!ok) { F->err = TPTEX_E_CORRUPT; return; }
  tk_reorient(k, eid, aeid);
  tri_split_and_apply(F, k, afid, &af);
}

static int adj_valid(const tptex_filter* F, const tptex_face_info* f, int e) {
  return tptex__fl_adj_ok(F, f->adjfaces[e]);
}

static void tri_split_and_apply(tptex_filter* F, tkern* k, int faceid, const tptex_face_info* f) {
  if (F->err) return;
  if (++F->depth > TPTEX_FILTER_MAX_DEPTH) { F->err = TPTEX_E_LIMIT; --F->depth; return; }
  if (k->u1 < 0 && adj_valid(F, f, 2)) {
    tkern ka = *k;
    k->u1 = 0;
    ka.u2 = 0;
    tri_apply_across_edge(F, &ka, f, 2);
  }
  if (!F->err && k->v1 < 0 && adj_valid(F, f, 0)) {
    tkern ka = *k;
    k->v1 = 0;
    ka.v2 = 0;
    tri_apply_across_edge(F, &ka, f, 0);
  }
  if (!F->err && k->w1 < 0 && adj_valid(F, f, 1)) {
    tkern ka = *k;
    k->w1 = 0;
    ka.w2 = 0;
    tri_apply_across_edge(F, &ka, f, 1);
  }
  if (!F->err) tri_apply(F, k, faceid, f);
  --F->depth;
}

void tptex__tri_eval(tptex_filter* F, int faceid, float u, float v, float uw1, float vw1, float uw2,
                     float vw2, float width, float blur) {
  const float sqrt3 = 1.7320508075688772f;
  tptex_face_info f;
  tkern k;
  float scaleAC, scaleB, A, B, C, Ac, Bc, Cc, X, b_e, b_t, b_b, b, m, scale, uw, vw, ww, w;
  const float maxEcc = 15.0f;
  const float eccRatio = (maxEcc * maxEcc + 1.0f) / (maxEcc * maxEcc - 1.0f);
  int reslog2;
  if (tptex_get_face_info(F->tx, faceid, &f) != TPTEX_OK) { F->err = TPTEX_E_RANGE; return; }
  u = u < 0.0f ? 0.0f : (u > 1.0f ? 1.0f : u);
  v = v < 0.0f ? 0.0f : (v > 1.0f ? 1.0f : v);

  /* PtexTriangleFilter::buildKernel */
  scaleAC = 0.25f * width * width;
  scaleB = -2.0f * scaleAC;
  A = (vw1 * vw1 + vw2 * vw2) * scaleAC;
  B = (uw1 * vw1 + uw2 * vw2) * scaleB;
  C = (uw1 * uw1 + uw2 * uw2) * scaleAC;
  Ac = 0.75f * A;
  Bc = (float)(sqrt3 / 2) * (B - A);
  Cc = 0.25f * A - 0.5f * B + C;
  X = sqrtf(squared(Ac - Cc) + squared(Bc));
  b_e = 0.5f * (eccRatio * X - (Ac + Cc));
  b_t = squared(0.5f / (float)(1 << f.res.ulog2));
  b_b = 0.25f * blur * blur;
  b = maxf_(b_b, maxf_(b_e, b_t));
  Ac += b;
  Cc += b;
  m = sqrtf(2.0f * (Ac * Cc - 0.25f * Bc * Bc) / (Ac + Cc + X));
  reslog2 = tptex__fl_calc_res_from_width(2.0f * m);
  if (reslog2 < 0) reslog2 = 0;
  if (!finite_f(m) || reslog2 > 127) { F->err = TPTEX_E_LIMIT; return; }
  A = (float)(4 / 3.0) * Ac;
  B = (float)(2 / sqrt3) * Bc + A;
  C = -0.25f * A + 0.5f * B + Cc;
  scale = KERNEL_WIDTH * KERNEL_WIDTH;
  A *= scale;
  B *= scale;
  C *= scale;
  uw = minf_(sqrtf(C), 1.0f);
  vw = minf_(sqrtf(A), 1.0f);
  ww = minf_(sqrtf(A - B + C), 1.0f);
  w = 1.0f - u - v;
  k.res = tptex_make_res(reslog2, reslog2);
  k.u = u; k.v = v;
  k.u1 = u - uw; k.v1 = v - vw; k.w1 = w - ww;
  k.u2 = u + uw; k.v2 = v + vw; k.w2 = w + ww;
  k.A = A; k.B = B; k.C = C;
  if (!tk_finite(&k)) { F->err = TPTEX_E_LIMIT; return; }
  F->weight = 0.0f;
  tri_split_and_apply(F, &k, faceid, &f);
}
