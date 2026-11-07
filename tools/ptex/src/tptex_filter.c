/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Quad-mesh filters and the common dispatch: a C11 port of PtexFilters.cpp,
 * PtexSeparableFilter.cpp and PtexSeparableKernel.{h,cpp}.
 *
 * Differences from upstream: no alloca/asserts (scratch is owned by the filter,
 * malformed meshes or kernels set an error instead of overrunning), adjacency
 * is range-checked, recursion across faces is depth-limited, and a face is
 * applied as one block rather than tile by tile.
 */
#include <math.h>

#include "../include/tptex_half.h"
#include "../include/tptex_utils.h"
#include "tptex_filter_internal.h"

#define KMAX 10

enum { E_BOTTOM = 0, E_RIGHT = 1, E_TOP = 2, E_LEFT = 3 };

/* ------------------------------------------------------------------------- */
/* small helpers                                                             */

float tptex__fl_floor(float x) { return floorf(x); }
float tptex__fl_ceil(float x) { return ceilf(x); }

int tptex__fl_to_int(float x) {
  if (!(x > -2147483648.0f && x < 2147483648.0f)) return INT32_MIN; /* NaN / out of range */
  return (int)x;
}

int tptex__fl_calc_res_from_width(float w) {
  uint32_t bits;
  memcpy(&bits, &w, 4);
  return 127 - (int)((bits >> 23) & 0xffu);
}

float tptex__fl_reciprocal_pow2(int power) {
  uint32_t bits = (uint32_t)(127 - power) << 23;
  float f;
  memcpy(&f, &bits, 4);
  return f;
}

float tptex__fl_rd(const uint8_t* p, tptex_data_type dt) {
  switch (dt) {
    case TPTEX_UINT8: return (float)p[0];
    case TPTEX_UINT16: return (float)tptex__ld_u16(p);
    case TPTEX_HALF: return tptex_half_to_float(tptex__ld_u16(p));
    default: {
      float f;
      uint32_t b = tptex__ld_u32(p);
      memcpy(&f, &b, 4);
      return f;
    }
  }
}

static float fabs_f(float x) { return fabsf(x); }
static float minf_(float a, float b) { return a < b ? a : b; }
static float maxf_(float a, float b) { return a > b ? a : b; }
static float clampf_(float x, float lo, float hi) { return minf_(maxf_(x, lo), hi); }

static tptex_face_info adj_fi(const tptex_filter* f, int faceid, int* ok) {
  tptex_face_info fi;
  memset(&fi, 0, sizeof fi);
  *ok = tptex_get_face_info(f->tx, faceid, &fi) == TPTEX_OK;
  return fi;
}

int tptex__fl_adj_ok(const tptex_filter* f, int faceid) {
  return faceid >= 0 && faceid < f->info->num_faces;
}

/* neighbour face for an edge, or -1 when absent or out of range (hostile files) */
static int adjface(const tptex_filter* f, const tptex_face_info* fi, int e) {
  int a = fi->adjfaces[e];
  return tptex__fl_adj_ok(f, a) ? a : -1;
}
static int adjedge(const tptex_face_info* fi, int e) { return (int)tptex_face_adjedge(fi, e); }

static int res_u(tptex_res r) { return 1 << r.ulog2; }
static int res_v(tptex_res r) { return 1 << r.vlog2; }

/* ------------------------------------------------------------------------- */
/* separable kernel                                                          */

typedef struct skern {
  tptex_res res;
  int u, v, uw, vw;
  float* ku;
  float* kv;
  float kubuff[KMAX];
  float kvbuff[KMAX];
  int rot;
} skern;

static void sk_init(skern* k) {
  memset(k, 0, sizeof *k);
  k->ku = k->kubuff;
  k->kv = k->kvbuff;
}

/* PtexSeparableKernel::set: copies the weights into the kernel's own buffers */
static int sk_set(skern* k, tptex_res res, int u, int v, int uw, int vw, const float* ku,
                  const float* kv, int rot) {
  if (uw < 0 || vw < 0 || uw > KMAX || vw > KMAX) return 0;
  k->res = res;
  k->u = u;
  k->v = v;
  k->uw = uw;
  k->vw = vw;
  memmove(k->kubuff, ku, sizeof(float) * (size_t)uw);
  memmove(k->kvbuff, kv, sizeof(float) * (size_t)vw);
  k->ku = k->kubuff;
  k->kv = k->kvbuff;
  k->rot = rot;
  return 1;
}

static int sk_copy(skern* dst, const skern* src) {
  /* use temporaries so dst == src is safe */
  float a[KMAX], b[KMAX];
  if (src->uw < 0 || src->uw > KMAX || src->vw < 0 || src->vw > KMAX) return 0;
  memcpy(a, src->ku, sizeof(float) * (size_t)src->uw);
  memcpy(b, src->kv, sizeof(float) * (size_t)src->vw);
  return sk_set(dst, src->res, src->u, src->v, src->uw, src->vw, a, b, src->rot);
}

static float accumulate(const float* p, int n) {
  float r = 0.0f;
  int i;
  for (i = 0; i < n; ++i) r += p[i];
  return r;
}

static int sk_strip_zeros(skern* k) {
  while (k->uw > 0 && k->ku[0] == 0.0f) { k->ku++; k->u++; k->uw--; }
  while (k->uw > 0 && k->ku[k->uw - 1] == 0.0f) k->uw--;
  while (k->vw > 0 && k->kv[0] == 0.0f) { k->kv++; k->v++; k->vw--; }
  while (k->vw > 0 && k->kv[k->vw - 1] == 0.0f) k->vw--;
  return k->uw > 0 && k->vw > 0;
}

static float sk_weight(const skern* k) { return accumulate(k->ku, k->uw) * accumulate(k->kv, k->vw); }

/* merge helpers return 0 when the geometry is inconsistent (never for valid input) */
static int sk_merge_l(skern* k, tptex_border_mode mode) {
  int w = -k->u;
  if (w < 0) return 0;
  if (w >= k->uw) { if (mode != TPTEX_BORDER_BLACK) return 0; k->u = 0; k->uw = 0; return 1; }
  if (mode != TPTEX_BORDER_BLACK) k->ku[w] += accumulate(k->ku, w);
  k->ku += w;
  k->uw -= w;
  k->u = 0;
  return 1;
}
static int sk_merge_r(skern* k, tptex_border_mode mode) {
  int w = k->uw + k->u - res_u(k->res);
  float* kp;
  if (w < 0) return 0;
  if (w >= k->uw) { if (mode != TPTEX_BORDER_BLACK) return 0; k->uw = 0; return 1; }
  kp = k->ku + k->uw - w;
  if (mode != TPTEX_BORDER_BLACK) kp[-1] += accumulate(kp, w);
  k->uw -= w;
  return 1;
}
static int sk_merge_b(skern* k, tptex_border_mode mode) {
  int w = -k->v;
  if (w < 0) return 0;
  if (w >= k->vw) { if (mode != TPTEX_BORDER_BLACK) return 0; k->v = 0; k->vw = 0; return 1; }
  if (mode != TPTEX_BORDER_BLACK) k->kv[w] += accumulate(k->kv, w);
  k->kv += w;
  k->vw -= w;
  k->v = 0;
  return 1;
}
static int sk_merge_t(skern* k, tptex_border_mode mode) {
  int w = k->vw + k->v - res_v(k->res);
  float* kp;
  if (w < 0) return 0;
  if (w >= k->vw) { if (mode != TPTEX_BORDER_BLACK) return 0; k->vw = 0; return 1; }
  kp = k->kv + k->vw - w;
  if (mode != TPTEX_BORDER_BLACK) kp[-1] += accumulate(kp, w);
  k->vw -= w;
  return 1;
}

static int sk_split_l(skern* k, skern* out) {
  int w = -k->u;
  if (w < k->uw) {
    if (!sk_set(out, k->res, res_u(k->res) - w, k->v, w, k->vw, k->ku, k->kv, 0)) return 0;
    k->u = 0;
    k->uw -= w;
    k->ku += w;
  } else {
    if (!sk_copy(out, k)) return 0;
    out->u += res_u(k->res);
    k->u = 0;
    k->uw = 0;
  }
  return 1;
}
static int sk_split_r(skern* k, skern* out) {
  int w = k->u + k->uw - res_u(k->res);
  if (w < k->uw) {
    if (!sk_set(out, k->res, 0, k->v, w, k->vw, k->ku + k->uw - w, k->kv, 0)) return 0;
    k->uw -= w;
  } else {
    if (!sk_copy(out, k)) return 0;
    out->u -= res_u(k->res);
    k->u = 0;
    k->uw = 0;
  }
  return 1;
}
static int sk_split_b(skern* k, skern* out) {
  int w = -k->v;
  if (w < k->vw) {
    if (!sk_set(out, k->res, k->u, res_v(k->res) - w, k->uw, w, k->ku, k->kv, 0)) return 0;
    k->v = 0;
    k->vw -= w;
    k->kv += w;
  } else {
    if (!sk_copy(out, k)) return 0;
    out->v += res_v(k->res);
    k->v = 0;
    k->vw = 0;
  }
  return 1;
}
static int sk_split_t(skern* k, skern* out) {
  int w = k->v + k->vw - res_v(k->res);
  if (w < k->vw) {
    if (!sk_set(out, k->res, k->u, 0, k->uw, w, k->ku, k->kv + k->vw - w, 0)) return 0;
    k->vw -= w;
  } else {
    if (!sk_copy(out, k)) return 0;
    out->v -= res_v(k->res);
    k->v = 0;
    k->vw = 0;
  }
  return 1;
}

static void reverse_f(float* p, int n) {
  int i;
  for (i = 0; i < n / 2; ++i) { float t = p[i]; p[i] = p[n - 1 - i]; p[n - 1 - i] = t; }
}
static void sk_flip_u(skern* k) { k->u = res_u(k->res) - k->u - k->uw; reverse_f(k->ku, k->uw); }
static void sk_flip_v(skern* k) { k->v = res_v(k->res) - k->v - k->vw; reverse_f(k->kv, k->vw); }
static void sk_swap_uv(skern* k) {
  int t;
  float* fp;
  int8_t r = k->res.ulog2;
  k->res.ulog2 = k->res.vlog2;
  k->res.vlog2 = r;
  t = k->u; k->u = k->v; k->v = t;
  t = k->uw; k->uw = k->vw; k->vw = t;
  fp = k->ku; k->ku = k->kv; k->kv = fp;
}
static void sk_rotate(skern* k, int rot) {
  switch (rot & 3) {
    default: return;
    case 1: sk_flip_u(k); sk_swap_uv(k); break;
    case 2: sk_flip_u(k); sk_flip_v(k); break;
    case 3: sk_flip_v(k); sk_swap_uv(k); break;
  }
  k->rot = (k->rot + rot) & 3;
}

static int sk_downres_u(skern* k) {
  float *src = k->ku, *dst = k->ku;
  int i;
  if (k->u & 1) { dst++; src++; k->uw--; }
  for (i = k->uw / 2; i > 0; --i) { *dst++ = src[0] + src[1]; src += 2; }
  if (k->uw & 1) *dst++ = *src++;
  k->u /= 2;
  k->uw = (int)(dst - k->ku);
  k->res.ulog2--;
  return k->res.ulog2 >= 0;
}
static int sk_downres_v(skern* k) {
  float *src = k->kv, *dst = k->kv;
  int i;
  if (k->v & 1) { dst++; src++; k->vw--; }
  for (i = k->vw / 2; i > 0; --i) { *dst++ = src[0] + src[1]; src += 2; }
  if (k->vw & 1) *dst++ = *src++;
  k->v /= 2;
  k->vw = (int)(dst - k->kv);
  k->res.vlog2--;
  return k->res.vlog2 >= 0;
}
/* upres needs room: weights are relative to kubuff, so bound by buffer end */
static int sk_upres_u(skern* k) {
  float* src;
  float* dst;
  int i;
  if ((k->ku - k->kubuff) + k->uw * 2 > KMAX || k->res.ulog2 >= 30) return 0;
  src = k->ku + k->uw - 1;
  dst = k->ku + k->uw * 2 - 2;
  for (i = k->uw; i > 0; --i) { dst[0] = dst[1] = *src-- / 2.0f; dst -= 2; }
  k->uw *= 2;
  k->u *= 2;
  k->res.ulog2++;
  return 1;
}
static int sk_upres_v(skern* k) {
  float* src;
  float* dst;
  int i;
  if ((k->kv - k->kvbuff) + k->vw * 2 > KMAX || k->res.vlog2 >= 30) return 0;
  src = k->kv + k->vw - 1;
  dst = k->kv + k->vw * 2 - 2;
  for (i = k->vw; i > 0; --i) { dst[0] = dst[1] = *src-- / 2.0f; dst -= 2; }
  k->vw *= 2;
  k->v *= 2;
  k->res.vlog2++;
  return 1;
}

static int sk_adjust_main_to_subface(skern* k, int eid, int* primary_out) {
  int primary = 0, resu, resv;
  if (k->res.ulog2 == 0 && !sk_upres_u(k)) return 0;
  if (k->res.vlog2 == 0 && !sk_upres_v(k)) return 0;
  if (k->res.ulog2 > 0) k->res.ulog2--;
  if (k->res.vlog2 > 0) k->res.vlog2--;
  resu = res_u(k->res);
  resv = res_v(k->res);
  switch (eid & 3) {
    case E_BOTTOM: primary = k->u < resu; k->v -= resv; if (!primary) k->u -= resu; break;
    case E_RIGHT: primary = k->v < resv; if (!primary) k->v -= resv; break;
    case E_TOP: primary = k->u >= resu; if (primary) k->u -= resu; break;
    case E_LEFT: primary = k->v >= resv; k->u -= resu; if (primary) k->v -= resv; break;
  }
  *primary_out = primary;
  return 1;
}

static int sk_adjust_subface_to_main(skern* k, int eid) {
  switch (eid & 3) {
    case E_BOTTOM: k->v += res_v(k->res); break;
    case E_RIGHT: break;
    case E_TOP: k->u += res_u(k->res); break;
    case E_LEFT: k->u += res_u(k->res); k->v += res_v(k->res); break;
  }
  if (k->res.ulog2 >= 30 || k->res.vlog2 >= 30) return 0;
  k->res.ulog2++;
  k->res.vlog2++;
  return 1;
}

static float sk_make_symmetric(skern* k, float initial_weight) {
  float new_weight = 0.0f, scale;
  int i;
  if (k->res.ulog2 > k->res.vlog2) { do { sk_downres_u(k); } while (k->res.ulog2 > k->res.vlog2); }
  else if (k->res.vlog2 > k->res.ulog2) { do { sk_downres_v(k); } while (k->res.vlog2 > k->res.ulog2); }
  k->uw = k->vw = k->uw < k->vw ? k->uw : k->vw;
  for (i = 0; i < k->uw; ++i) {
    float sum = k->ku[i] + k->kv[i];
    k->ku[i] = k->kv[i] = sum;
    new_weight += sum;
  }
  new_weight *= new_weight;
  scale = new_weight == 0.0f ? 1.0f : initial_weight / new_weight;
  if (scale >= 1.0f) {
    /* nothing */
  } else if (scale < -1.0f) {
    for (i = 0; i < k->uw; ++i) k->ku[i] *= -1.0f;
    new_weight = -new_weight;
  } else {
    for (i = 0; i < k->uw; ++i) k->ku[i] *= scale;
    new_weight = initial_weight;
  }
  return new_weight;
}

/* dst[c] += sum over kernel of pixel[c] * ku * kv, with upstream's evaluation order */
static void sk_apply(const tptex_filter* f, const skern* k, float* dst, const uint8_t* data) {
  const size_t es = f->dtsize;
  const size_t pstride = (size_t)f->ntxchan * es;
  const size_t rowbytes = (size_t)res_u(k->res) * pstride;
  const uint8_t* p0 = data + ((size_t)k->v * (size_t)res_u(k->res) + (size_t)k->u) * pstride + f->firstoff;
  float* row = f->row;
  int vi, x, c;
  for (vi = 0; vi < k->vw; ++vi) {
    const uint8_t* pr = p0 + (size_t)vi * rowbytes;
    for (x = 0; x < k->uw; ++x) {
      const uint8_t* px = pr + (size_t)x * pstride;
      const float wu = k->ku[x];
      if (x == 0)
        for (c = 0; c < f->nchan; ++c) row[c] = tptex__fl_rd(px + (size_t)c * es, f->dt) * wu;
      else
        for (c = 0; c < f->nchan; ++c) row[c] += tptex__fl_rd(px + (size_t)c * es, f->dt) * wu;
    }
    {
      const float wv = k->kv[vi];
      for (c = 0; c < f->nchan; ++c) dst[c] += row[c] * wv;
    }
  }
}

/* ------------------------------------------------------------------------- */
/* separable filter core                                                     */

typedef struct sepctx {
  tptex_filter* f;
} sepctx;

static void sep_split_and_apply(tptex_filter* F, skern* k, int faceid, const tptex_face_info* fi);

static void sep_apply(tptex_filter* F, skern* k, int faceid, const tptex_face_info* fi) {
  tptex_face_data fd;
  int tanvec;
  float* result;
  tptex_status st;
  if (F->err) return;
  if (k->uw <= 0 || k->vw <= 0) return;
  if (k->u < 0 || k->v < 0 || k->u + k->uw > res_u(k->res) || k->v + k->vw > res_v(k->res)) {
    F->err = TPTEX_E_CORRUPT;
    return;
  }
  while (res_u(k->res) > res_u(fi->res)) if (!sk_downres_u(k)) { F->err = TPTEX_E_CORRUPT; return; }
  while (res_v(k->res) > res_v(fi->res)) if (!sk_downres_v(k)) { F->err = TPTEX_E_CORRUPT; return; }
  if (k->uw <= 0 || k->vw <= 0) return;
  st = tptex_get_face_data(F->tx, faceid, k->res, &fd);
  if (st != TPTEX_OK) { F->err = st; return; }
  if (fd.is_constant) {
    /* weight() then dst[c] += pixel[c] * weight */
    tptex_apply_const(sk_weight(k), F->result, (const uint8_t*)fd.data + F->firstoff, F->dt, F->nchan);
    tptex_release_face_data(F->tx, &fd);
    return;
  }
  tanvec = F->efm == TPTEX_EDGE_FILTER_TANGENT && F->nchan >= 2 && k->rot > 0;
  result = tanvec ? F->tmp : F->result;
  if (tanvec) memset(F->tmp, 0, sizeof(float) * (size_t)F->nchan);
  sk_apply(F, k, result, (const uint8_t*)fd.data);
  tptex_release_face_data(F->tx, &fd);
  if (tanvec) {
    float* r = F->result;
    const float* t = F->tmp;
    int i;
    switch (k->rot) {
      case 0: r[0] += t[0]; r[1] += t[1]; break;
      case 1: r[0] -= t[1]; r[1] += t[0]; break;
      case 2: r[0] -= t[0]; r[1] -= t[1]; break;
      case 3: r[0] += t[1]; r[1] -= t[0]; break;
    }
    for (i = 2; i < F->nchan; ++i) r[i] += t[i];
  }
}

static void sep_apply_across_edge(tptex_filter* F, skern* k, int faceid, const tptex_face_info* f, int eid) {
  int afid = adjface(F, f, eid), aeid = adjedge(f, eid), ok, rot;
  tptex_face_info af;
  int f_sub, af_sub;
  if (afid < 0) { F->err = TPTEX_E_CORRUPT; return; }
  af = adj_fi(F, afid, &ok);
  if (!ok) { F->err = TPTEX_E_CORRUPT; return; }
  rot = eid - aeid + 2;
  f_sub = tptex_face_is_subface(f);
  af_sub = tptex_face_is_subface(&af);
  if (f_sub != af_sub) {
    if (af_sub) {
      int primary = 0;
      if (!sk_adjust_main_to_subface(k, eid, &primary)) { F->err = TPTEX_E_CORRUPT; return; }
      if (!primary) {
        int neid = (aeid + 3) % 4;
        afid = adjface(F, &af, neid);
        aeid = adjedge(&af, neid);
        if (afid < 0) { F->err = TPTEX_E_CORRUPT; return; }
        af = adj_fi(F, afid, &ok);
        if (!ok) { F->err = TPTEX_E_CORRUPT; return; }
        rot += neid - aeid + 2;
      }
    } else {
      int primary = adjface(F, &af, aeid) == faceid;
      if (!sk_adjust_subface_to_main(k, eid - primary)) { F->err = TPTEX_E_CORRUPT; return; }
    }
  }
  sk_rotate(k, rot);
  if (af_sub) sep_split_and_apply(F, k, afid, &af);
  else sep_apply(F, k, afid, &af);
}

static void sep_apply_to_corner_face(tptex_filter* F, skern* k, const tptex_face_info* f, int eid,
                                     int cfid, const tptex_face_info* cf, int ceid) {
  int f_sub = tptex_face_is_subface(f), cf_sub = tptex_face_is_subface(cf);
  if (f_sub != cf_sub) {
    if (cf_sub) {
      int primary;
      if (!sk_adjust_main_to_subface(k, eid + 3, &primary)) { F->err = TPTEX_E_CORRUPT; return; }
    } else if (!sk_adjust_subface_to_main(k, eid + 3)) { F->err = TPTEX_E_CORRUPT; return; }
  }
  sk_rotate(k, eid - ceid + 2);
  if (cf_sub) sep_split_and_apply(F, k, cfid, cf);
  else sep_apply(F, k, cfid, cf);
}

static void sep_apply_to_corner(tptex_filter* F, skern* k, int faceid, const tptex_face_info* f, int eid) {
  enum { MAX_VALENCE = 10 };
  int afid = faceid, aeid = eid;
  tptex_face_info af = *f;
  int prev_sub = tptex_face_is_subface(&af);
  int cface_id[MAX_VALENCE], cedge_id[MAX_VALENCE];
  tptex_face_info cface[MAX_VALENCE];
  int ncorners = 0, i, ok;
  for (i = 0; i < MAX_VALENCE; ++i) {
    int prev_face = afid, is_sub;
    afid = adjface(F, &af, aeid);
    aeid = (adjedge(&af, aeid) + 1) % 4;
    if (afid < 0 || (afid == faceid && aeid == eid)) { ncorners = i - 2; break; }
    af = adj_fi(F, afid, &ok);
    if (!ok) { F->err = TPTEX_E_CORRUPT; return; }
    cface_id[i] = afid;
    cedge_id[i] = aeid;
    cface[i] = af;
    is_sub = tptex_face_is_subface(&af);
    if (prev_sub && !is_sub && adjface(F, &af, (aeid + 3) % 4) == prev_face) {
      int primary = i == 1;
      if (!sk_adjust_subface_to_main(k, eid + primary * 2)) { F->err = TPTEX_E_CORRUPT; return; }
      sk_rotate(k, eid - aeid + 3 - primary);
      sep_split_and_apply(F, k, afid, &af);
      return;
    }
    prev_sub = is_sub;
    if (i == MAX_VALENCE - 1) ncorners = 0; /* valence overflow: treat as irregular */
  }
  if (ncorners == 1) {
    sep_apply_to_corner_face(F, k, f, eid, cface_id[1], &cface[1], cedge_id[1]);
  } else if (ncorners > 1) {
    float initial, new_weight;
    sk_rotate(k, eid + 2);
    initial = sk_weight(k);
    new_weight = sk_make_symmetric(k, initial);
    for (i = 1; i <= ncorners && !F->err; ++i) {
      skern kc;
      sk_init(&kc);
      if (!sk_copy(&kc, k)) { F->err = TPTEX_E_CORRUPT; return; }
      sep_apply_to_corner_face(F, &kc, f, 2, cface_id[i], &cface[i], cedge_id[i]);
    }
    F->weight += new_weight * (float)ncorners - initial;
  } else {
    F->weight -= sk_weight(k);
  }
}

static void sep_split_and_apply(tptex_filter* F, skern* k, int faceid, const tptex_face_info* f) {
  int split_r, split_l, split_t, split_b;
  if (F->err) return;
  if (++F->depth > TPTEX_FILTER_MAX_DEPTH) { F->err = TPTEX_E_LIMIT; --F->depth; return; }
  split_r = k->u + k->uw > res_u(k->res);
  split_l = k->u < 0;
  split_t = k->v + k->vw > res_v(k->res);
  split_b = k->v < 0;
  if (F->opt.noedgeblend) {
    int ok = 1;
    if (split_r) ok &= sk_merge_r(k, F->umode);
    if (split_l) ok &= sk_merge_l(k, F->umode);
    if (split_t) ok &= sk_merge_t(k, F->vmode);
    if (split_b) ok &= sk_merge_b(k, F->vmode);
    if (!ok) F->err = TPTEX_E_CORRUPT;
    else sep_apply(F, k, faceid, f);
    --F->depth;
    return;
  }
  if (split_r || split_l || split_t || split_b) {
    skern ka, kc;
    int ok = 1;
    sk_init(&ka);
    sk_init(&kc);
    if (split_r) {
      if (adjface(F, f, E_RIGHT) >= 0) {
        ok &= sk_split_r(k, &ka);
        if (split_t) {
          if (adjface(F, f, E_TOP) >= 0) {
            ok &= sk_split_t(&ka, &kc);
            if (ok) sep_apply_to_corner(F, &kc, faceid, f, E_TOP);
          } else ok &= sk_merge_t(&ka, F->vmode);
        }
        if (split_b) {
          if (adjface(F, f, E_BOTTOM) >= 0) {
            ok &= sk_split_b(&ka, &kc);
            if (ok) sep_apply_to_corner(F, &kc, faceid, f, E_RIGHT);
          } else ok &= sk_merge_b(&ka, F->vmode);
        }
        if (ok) sep_apply_across_edge(F, &ka, faceid, f, E_RIGHT);
      } else ok &= sk_merge_r(k, F->umode);
    }
    if (ok && !F->err && split_l) {
      if (adjface(F, f, E_LEFT) >= 0) {
        ok &= sk_split_l(k, &ka);
        if (split_t) {
          if (adjface(F, f, E_TOP) >= 0) {
            ok &= sk_split_t(&ka, &kc);
            if (ok) sep_apply_to_corner(F, &kc, faceid, f, E_LEFT);
          } else ok &= sk_merge_t(&ka, F->vmode);
        }
        if (split_b) {
          if (adjface(F, f, E_BOTTOM) >= 0) {
            ok &= sk_split_b(&ka, &kc);
            if (ok) sep_apply_to_corner(F, &kc, faceid, f, E_BOTTOM);
          } else ok &= sk_merge_b(&ka, F->vmode);
        }
        if (ok) sep_apply_across_edge(F, &ka, faceid, f, E_LEFT);
      } else ok &= sk_merge_l(k, F->umode);
    }
    if (ok && !F->err && split_t) {
      if (adjface(F, f, E_TOP) >= 0) {
        ok &= sk_split_t(k, &ka);
        if (ok) sep_apply_across_edge(F, &ka, faceid, f, E_TOP);
      } else ok &= sk_merge_t(k, F->vmode);
    }
    if (ok && !F->err && split_b) {
      if (adjface(F, f, E_BOTTOM) >= 0) {
        ok &= sk_split_b(k, &ka);
        if (ok) sep_apply_across_edge(F, &ka, faceid, f, E_BOTTOM);
      } else ok &= sk_merge_b(k, F->vmode);
    }
    if (!ok && !F->err) F->err = TPTEX_E_CORRUPT;
  }
  if (!F->err) sep_apply(F, k, faceid, f);
  --F->depth;
}

/* ------------------------------------------------------------------------- */
/* kernel builders                                                           */

static float kern_bicubic(const tptex_filter* F, float x) {
  const float* c = F->coeffs;
  x = fabs_f(x);
  if (x < 1.0f) return (c[0] * x + c[1]) * x * x + c[2];
  if (x < 2.0f) return ((c[3] * x + c[4]) * x + c[5]) * x + c[6];
  return 0.0f;
}
static float kern_gaussian(float x) { return (float)exp((double)(-2.0f * x * x)); }

static float kern_eval(const tptex_filter* F, float x) {
  return F->opt.filter == TPTEX_FILTER_GAUSSIAN ? kern_gaussian(x) : kern_bicubic(F, x);
}

static float blur_kernel(float x) {
  x = fabs_f(x);
  return x < 1.0f ? (2.0f * x - 3.0f) * x * x + 1.0f : 0.0f;
}

/* PtexWidth4Filter::buildKernelAxis; returns 0 if the kernel would overflow */
static int build_axis_w4(const tptex_filter* F, int8_t* k_ureslog2, int* k_u, int* k_uw, float* ku,
                        float u, float uw, int f_ureslog2) {
  int resu, i;
  float uwlo, lerp2, lerp1;
  uw = maxf_(uw, tptex__fl_reciprocal_pow2(f_ureslog2));
  *k_ureslog2 = (int8_t)tptex__fl_calc_res_from_width(uw);
  if (*k_ureslog2 < 0 || *k_ureslog2 > 30) {
    if (uw < 0.25f) return 0;
  }
  resu = *k_ureslog2 >= 0 && *k_ureslog2 <= 30 ? 1 << *k_ureslog2 : 1;
  uwlo = 1.0f / (float)resu;
  lerp2 = F->opt.lerp ? (uw - uwlo) / uwlo : 0.0f;
  lerp1 = 1.0f - lerp2;
  if (uw >= 0.25f) {
    if (uw < 0.5f) {
      float upix, x1, s;
      int u1, u2;
      *k_ureslog2 = 2;
      upix = u * 4.0f - 0.5f;
      u1 = tptex__fl_to_int(tptex__fl_ceil(upix - 2.0f));
      u2 = tptex__fl_to_int(tptex__fl_ceil(upix + 2.0f));
      u1 = u1 & ~1;
      u2 = (u2 + 1) & ~1;
      *k_u = u1;
      *k_uw = u2 - u1;
      if (*k_uw < 0 || *k_uw > KMAX) return 0;
      x1 = (float)u1 - upix;
      s = 1.0f / (uw + 0.75f);
      for (i = 0; i < *k_uw; i += 2) {
        float xa = x1 + (float)i, xb = xa + 1.0f, xc = (xa + xb) * 0.25f;
        float ka = kern_eval(F, xa), kb = kern_eval(F, xb), kc = blur_kernel(xc * s);
        ku[i] = ka * lerp1 + kc * lerp2;
        ku[i + 1] = kb * lerp1 + kc * lerp2;
      }
      return 1;
    } else if (uw < 1.0f) {
      float upix, x1, s;
      *k_ureslog2 = 1;
      upix = u * 2.0f - 0.5f;
      *k_u = tptex__fl_to_int(tptex__fl_floor(u - 0.5f)) * 2;
      *k_uw = 4;
      x1 = (float)*k_u - upix;
      s = 1.0f / (uw * 1.5f + 0.5f);
      for (i = 0; i < *k_uw; i += 2) {
        float xa = x1 + (float)i, xb = xa + 1.0f, xc = (xa + xb) * 0.5f;
        float ka = blur_kernel(xa * s), kb = blur_kernel(xb * s), kc = blur_kernel(xc * s);
        ku[i] = ka * lerp1 + kc * lerp2;
        ku[i + 1] = kb * lerp1 + kc * lerp2;
      }
      return 1;
    } else {
      float upix = u - 0.5f, ui;
      *k_ureslog2 = 0;
      *k_uw = 2;
      ui = tptex__fl_floor(upix);
      *k_u = tptex__fl_to_int(ui);
      ku[0] = blur_kernel(upix - ui);
      ku[1] = 1.0f - ku[0];
      return 1;
    }
  }
  {
    float upix = u * (float)resu - 0.5f, uwpix = uw * (float)resu, dupix = 2.0f * uwpix;
    int u1 = tptex__fl_to_int(tptex__fl_ceil(upix - dupix)), u2 = tptex__fl_to_int(tptex__fl_ceil(upix + dupix));
    if (lerp2 != 0.0f) {
      float step, x1;
      u1 = u1 & ~1;
      u2 = (u2 + 1) & ~1;
      *k_u = u1;
      *k_uw = u2 - u1;
      if (*k_uw < 0 || *k_uw > KMAX) return 0;
      step = 1.0f / uwpix;
      x1 = ((float)u1 - upix) * step;
      for (i = 0; i < *k_uw; i += 2) {
        float xa = x1 + (float)i * step, xb = xa + step, xc = (xa + xb) * 0.5f;
        float ka = kern_eval(F, xa), kb = kern_eval(F, xb), kc = kern_eval(F, xc);
        ku[i] = ka * lerp1 + kc * lerp2;
        ku[i + 1] = kb * lerp1 + kc * lerp2;
      }
    } else {
      float x1, step;
      *k_u = u1;
      *k_uw = u2 - u1;
      if (*k_uw < 0 || *k_uw > KMAX) return 0;
      x1 = ((float)u1 - upix) / uwpix;
      step = 1.0f / uwpix;
      for (i = 0; i < *k_uw; ++i) ku[i] = kern_eval(F, x1 + (float)i * step);
    }
  }
  return 1;
}

static int build_w4(const tptex_filter* F, skern* k, float u, float v, float uw, float vw, tptex_res fres) {
  return build_axis_w4(F, &k->res.ulog2, &k->u, &k->uw, k->ku, u, uw, fres.ulog2) &&
         build_axis_w4(F, &k->res.vlog2, &k->v, &k->vw, k->kv, v, vw, fres.vlog2);
}

static void box_weights(float* kernel, int size, float f1, float f2) {
  int i;
  if (size == 1) {
    kernel[0] = f1 + f2 - 1.0f;
  } else {
    kernel[0] = f1;
    for (i = 1; i < size - 1; ++i) kernel[i] = 1.0f;
    kernel[size - 1] = f2;
  }
}

static int build_box(skern* k, float u, float v, float uw, float vw, tptex_res fres) {
  float u1, u2, v1, v2, u1f, u2c, v1f, v2c;
  uw = minf_(uw, 1.0f);
  vw = minf_(vw, 1.0f);
  uw = maxf_(uw, tptex__fl_reciprocal_pow2(fres.ulog2));
  vw = maxf_(vw, tptex__fl_reciprocal_pow2(fres.vlog2));
  k->res.ulog2 = (int8_t)(uint8_t)tptex__fl_calc_res_from_width(uw);
  k->res.vlog2 = (int8_t)(uint8_t)tptex__fl_calc_res_from_width(vw);
  if (k->res.ulog2 < 0 || k->res.vlog2 < 0 || k->res.ulog2 > 30 || k->res.vlog2 > 30) return 0;
  u = u * (float)res_u(k->res);
  v = v * (float)res_v(k->res);
  uw *= (float)res_u(k->res);
  vw *= (float)res_v(k->res);
  u1 = u - 0.5f * uw; u2 = u + 0.5f * uw;
  v1 = v - 0.5f * vw; v2 = v + 0.5f * vw;
  u1f = tptex__fl_floor(u1); u2c = tptex__fl_ceil(u2);
  v1f = tptex__fl_floor(v1); v2c = tptex__fl_ceil(v2);
  k->u = tptex__fl_to_int(u1f);
  k->v = tptex__fl_to_int(v1f);
  k->uw = tptex__fl_to_int(u2c) - k->u;
  k->vw = tptex__fl_to_int(v2c) - k->v;
  if (k->uw < 1 || k->uw > 3 || k->vw < 1 || k->vw > 3) return 0;
  box_weights(k->ku, k->uw, 1.0f - (u1 - u1f), 1.0f - (u2c - u2));
  box_weights(k->kv, k->vw, 1.0f - (v1 - v1f), 1.0f - (v2c - v2));
  return 1;
}

static int build_bilinear(skern* k, float u, float v, float uw, float vw, tptex_res fres) {
  float upix, vpix, uf, vf, ufrac, vfrac;
  uw = minf_(uw, 1.0f);
  vw = minf_(vw, 1.0f);
  uw = maxf_(uw, tptex__fl_reciprocal_pow2(fres.ulog2));
  vw = maxf_(vw, tptex__fl_reciprocal_pow2(fres.vlog2));
  k->res.ulog2 = (int8_t)(uint8_t)tptex__fl_calc_res_from_width(uw);
  k->res.vlog2 = (int8_t)(uint8_t)tptex__fl_calc_res_from_width(vw);
  if (k->res.ulog2 < 0 || k->res.vlog2 < 0 || k->res.ulog2 > 30 || k->res.vlog2 > 30) return 0;
  upix = u * (float)res_u(k->res) - 0.5f;
  vpix = v * (float)res_v(k->res) - 0.5f;
  uf = tptex__fl_floor(upix);
  vf = tptex__fl_floor(vpix);
  k->u = tptex__fl_to_int(uf);
  k->v = tptex__fl_to_int(vf);
  k->uw = 2;
  k->vw = 2;
  ufrac = upix - uf;
  vfrac = vpix - vf;
  k->ku[0] = 1.0f - ufrac;
  k->ku[1] = ufrac;
  k->kv[0] = 1.0f - vfrac;
  k->kv[1] = vfrac;
  return 1;
}

static int build_kernel(const tptex_filter* F, skern* k, float u, float v, float uw, float vw, tptex_res fres) {
  switch (F->opt.filter) {
    case TPTEX_FILTER_BILINEAR: return build_bilinear(k, u, v, uw, vw, fres);
    case TPTEX_FILTER_GAUSSIAN:
    case TPTEX_FILTER_BICUBIC:
    case TPTEX_FILTER_BSPLINE:
    case TPTEX_FILTER_CATMULLROM:
    case TPTEX_FILTER_MITCHELL: return build_w4(F, k, u, v, uw, vw, fres);
    default: return build_box(k, u, v, uw, vw, fres);
  }
}

static void sep_eval(tptex_filter* F, int faceid, float u, float v, float uw1, float vw1, float uw2,
                     float vw2, float width, float blur) {
  tptex_face_info f;
  float uw, vw;
  int return_black = 0, ok;
  skern k;
  f = adj_fi(F, faceid, &ok);
  if (!ok) { F->err = TPTEX_E_RANGE; return; }
  uw = fabs_f(uw1) + fabs_f(uw2);
  vw = fabs_f(vw1) + fabs_f(vw2);
  switch (F->umode) {
    case TPTEX_BORDER_CLAMP: u = clampf_(u, 0.0f, 1.0f); break;
    case TPTEX_BORDER_PERIODIC: u = u - tptex__fl_floor(u); break;
    case TPTEX_BORDER_BLACK: if (u <= -1.0f || u >= 2.0f) return_black = 1; break;
  }
  switch (F->vmode) {
    case TPTEX_BORDER_CLAMP: v = clampf_(v, 0.0f, 1.0f); break;
    case TPTEX_BORDER_PERIODIC: v = v - tptex__fl_floor(v); break;
    case TPTEX_BORDER_BLACK: if (v <= -1.0f || v >= 2.0f) return_black = 1; break;
  }
  if (return_black) { memset(F->result, 0, sizeof(float) * (size_t)F->nchan); F->weight = 1.0f; F->err = TPTEX_OK; F->depth = -1; return; }
  sk_init(&k);
  if (tptex_face_is_subface(&f)) {
    uw = uw * width + blur * 2.0f;
    vw = vw * width + blur * 2.0f;
    if (!build_kernel(F, &k, u * 0.5f, v * 0.5f, uw * 0.5f, vw * 0.5f,
                      tptex_make_res(f.res.ulog2 + 1, f.res.vlog2 + 1))) { F->err = TPTEX_E_LIMIT; return; }
    if (k.res.ulog2 == 0 && !sk_upres_u(&k)) { F->err = TPTEX_E_LIMIT; return; }
    if (k.res.vlog2 == 0 && !sk_upres_v(&k)) { F->err = TPTEX_E_LIMIT; return; }
    k.res.ulog2--;
    k.res.vlog2--;
  } else {
    uw = uw * width + blur;
    vw = vw * width + blur;
    if (!build_kernel(F, &k, u, v, uw, vw, f.res)) { F->err = TPTEX_E_LIMIT; return; }
  }
  if (!sk_strip_zeros(&k)) { F->err = TPTEX_E_LIMIT; return; } /* degenerate (all-zero) kernel */
  F->weight = sk_weight(&k);
  sep_split_and_apply(F, &k, faceid, &f);
}

/* ------------------------------------------------------------------------- */
/* point filters                                                             */

static void point_eval(tptex_filter* F, int faceid, float u, float v) {
  tptex_face_info f;
  int ok;
  f = adj_fi(F, faceid, &ok);
  if (!ok) { F->err = TPTEX_E_RANGE; return; }
  if (F->info->mesh_type == TPTEX_MESH_QUAD) {
    int resu = res_u(f.res), resv = res_v(f.res);
    int ui = tptex__fl_to_int(u * (float)resu), vi = tptex__fl_to_int(v * (float)resv);
    ui = ui < 0 ? 0 : (ui > resu - 1 ? resu - 1 : ui);
    vi = vi < 0 ? 0 : (vi > resv - 1 ? resv - 1 : vi);
    F->err = tptex_get_pixel(F->tx, faceid, ui, vi, F->result, F->firstchan, F->nchan);
  } else {
    int res = res_u(f.res), resm1 = res - 1, ui, vi;
    float ut = u * (float)res, vt = v * (float)res, uf, vf;
    ui = tptex__fl_to_int(ut);
    vi = tptex__fl_to_int(vt);
    ui = ui < 0 ? 0 : (ui > resm1 ? resm1 : ui);
    vi = vi < 0 ? 0 : (vi > resm1 ? resm1 : vi);
    uf = ut - (float)ui;
    vf = vt - (float)vi;
    if (uf + vf <= 1.0f) F->err = tptex_get_pixel(F->tx, faceid, ui, vi, F->result, F->firstchan, F->nchan);
    else F->err = tptex_get_pixel(F->tx, faceid, resm1 - vi, resm1 - ui, F->result, F->firstchan, F->nchan);
  }
}

/* ------------------------------------------------------------------------- */
/* public                                                                    */

void tptex_filter_options_init(tptex_filter_options* o) {
  if (!o) return;
  memset(o, 0, sizeof *o);
  o->filter = TPTEX_FILTER_BOX;
}

tptex_status tptex_filter_create(tptex_texture* tx, const tptex_filter_options* options, tptex_filter** out) {
  tptex_filter* F;
  tptex_filter_options def;
  float B;
  size_t n;
  if (out) *out = NULL;
  if (!tx || !out) return TPTEX_E_INVALID_ARG;
  if (!options) { tptex_filter_options_init(&def); options = &def; }
  if ((int)options->filter < 0 || (int)options->filter > 7) return TPTEX_E_INVALID_ARG;
  F = (tptex_filter*)tptex__calloc(&options->allocator, sizeof *F);
  if (!F) return TPTEX_E_NOMEM;
  F->alloc = options->allocator;
  F->tx = tx;
  F->opt = *options;
  F->info = tptex_get_info(tx);
  F->ntxchan = F->info->num_channels;
  F->dt = F->info->data_type;
  F->dtsize = tptex_data_type_size(F->dt);
  F->pixsize = F->dtsize * (size_t)F->ntxchan;
  F->umode = F->info->u_border_mode;
  F->vmode = F->info->v_border_mode;
  F->efm = F->info->edge_filter_mode;
  switch (options->filter) {
    case TPTEX_FILTER_BICUBIC: B = 1.0f - options->sharpness; break;
    case TPTEX_FILTER_BSPLINE: B = 1.0f; break;
    case TPTEX_FILTER_CATMULLROM: B = 0.0f; break;
    case TPTEX_FILTER_MITCHELL: B = 1.0f - 2.0f / 3.0f; break;
    default: B = 1.0f; break;
  }
  F->coeffs[0] = 1.5f - B;
  F->coeffs[1] = 1.5f * B - 2.5f;
  F->coeffs[2] = 1.0f - (float)(1.0 / 3.0) * B;
  F->coeffs[3] = (float)(1.0 / 3.0) * B - 0.5f;
  F->coeffs[4] = 2.5f - 1.5f * B;
  F->coeffs[5] = 2.0f * B - 4.0f;
  F->coeffs[6] = 2.0f - (float)(2.0 / 3.0) * B;
  n = (size_t)F->ntxchan * sizeof(float);
  F->result = (float*)tptex__alloc(&F->alloc, n);
  F->tmp = (float*)tptex__alloc(&F->alloc, n);
  F->row = (float*)tptex__alloc(&F->alloc, n);
  F->pix = (uint8_t*)tptex__alloc(&F->alloc, F->pixsize);
  if (!F->result || !F->tmp || !F->row || !F->pix) { tptex_filter_destroy(F); return TPTEX_E_NOMEM; }
  *out = F;
  return TPTEX_OK;
}

void tptex_filter_destroy(tptex_filter* F) {
  tptex_allocator a;
  if (!F) return;
  a = F->alloc;
  tptex__free(&a, F->result, (size_t)F->ntxchan * sizeof(float));
  tptex__free(&a, F->tmp, (size_t)F->ntxchan * sizeof(float));
  tptex__free(&a, F->row, (size_t)F->ntxchan * sizeof(float));
  tptex__free(&a, F->pix, F->pixsize);
  tptex__free(&a, F, sizeof *F);
}

static int finite_f(float x) { return x - x == 0.0f; }

tptex_status tptex_filter_eval(tptex_filter* F, float* result, int firstchan, int nchannels, int faceid,
                               float u, float v, float uw1, float vw1, float uw2, float vw2,
                               float width, float blur) {
  tptex_face_info f;
  int ok, i;
  if (!F || !result || nchannels <= 0) return TPTEX_E_INVALID_ARG;
  if (faceid < 0 || faceid >= F->info->num_faces) return TPTEX_E_RANGE;
  if (firstchan < 0 || firstchan >= F->ntxchan) return TPTEX_E_INVALID_ARG;
  if (!finite_f(u) || !finite_f(v) || !finite_f(uw1) || !finite_f(vw1) || !finite_f(uw2) ||
      !finite_f(vw2) || !finite_f(width) || !finite_f(blur))
    return TPTEX_E_INVALID_ARG;
  F->firstchan = firstchan;
  F->nchan = nchannels < F->ntxchan - firstchan ? nchannels : F->ntxchan - firstchan;
  F->firstoff = (size_t)firstchan * F->dtsize;
  F->err = TPTEX_OK;
  F->depth = 0;
  F->weight = 0.0f;
  memset(F->result, 0, sizeof(float) * (size_t)F->nchan);

  f = adj_fi(F, faceid, &ok);
  if (!ok) return TPTEX_E_RANGE;
  if (f.flags & TPTEX_FACE_NBCONSTANT) {
    tptex_status st = tptex_get_constant(F->tx, faceid, F->pix);
    if (st != TPTEX_OK) return st;
    tptex_convert_to_float(result, F->pix + F->firstoff, F->dt, F->nchan);
    return TPTEX_OK;
  }

  if (F->opt.filter == TPTEX_FILTER_POINT) {
    point_eval(F, faceid, u, v);
    if (F->err != TPTEX_OK) return F->err;
    memcpy(result, F->result, sizeof(float) * (size_t)F->nchan);
    return TPTEX_OK;
  }
  if (F->info->mesh_type == TPTEX_MESH_TRIANGLE) {
    tptex__tri_eval(F, faceid, u, v, uw1, vw1, uw2, vw2, width, blur);
  } else {
    sep_eval(F, faceid, u, v, uw1, vw1, uw2, vw2, width, blur);
    if (F->depth == -1) { /* border-black early-out: result already zero */
      memcpy(result, F->result, sizeof(float) * (size_t)F->nchan);
      return TPTEX_OK;
    }
  }
  if (F->err != TPTEX_OK) return F->err;
  {
    float scale = 1.0f / (F->weight * tptex_one_value(F->dt));
    for (i = 0; i < F->nchan; ++i) result[i] = (float)(F->result[i] * scale);
  }
  return TPTEX_OK;
}
