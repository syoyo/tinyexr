/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Port of upstream PtexUtils.cpp. Arithmetic order and per-type rounding follow
 * the C++ templates exactly:
 *   - uint8/uint16: sums are `int`; quarter = (sum >> 2), halve = (sum >> 1);
 *   - half: operands are widened to float, summed left-to-right, scaled by
 *     0.25f / 0.5f and narrowed with the upstream half conversion;
 *   - float: the same in single precision.
 * Build with -ffp-contract=off so no multiply-add is fused.
 */
#include "../include/tptex_utils.h"

#include <string.h>

#include "../include/tptex_half.h"

/* ---- element access (host byte order, no alignment assumptions) ---------- */
static inline uint16_t ld16(const uint8_t* p) { uint16_t v; memcpy(&v, p, 2); return v; }
static inline void st16(uint8_t* p, uint16_t v) { memcpy(p, &v, 2); }
static inline float ldf(const uint8_t* p) { float v; memcpy(&v, p, 4); return v; }
static inline void stf(uint8_t* p, float v) { memcpy(p, &v, 4); }

/* Defined float->integer narrowing. x86 cvttss2si yields INT32_MIN for NaN and
 * out-of-range values and the narrow cast keeps the low bits; do the same. */
static inline int32_t f2i32(float f) {
  if (!(f >= -2147483648.0f && f < 2147483648.0f)) return INT32_MIN;
  return (int32_t)f;
}
static inline uint8_t f2u8(float f) { return (uint8_t)(uint32_t)f2i32(f); }
static inline uint16_t f2u16(float f) { return (uint16_t)(uint32_t)f2i32(f); }

static size_t elem_size(tptex_data_type dt) { return tptex_data_type_size(dt); }

float tptex_one_value(tptex_data_type dt) {
  switch (dt) {
    case TPTEX_UINT8: return 255.f;
    case TPTEX_UINT16: return 65535.f;
    case TPTEX_HALF: return 1.f;
    case TPTEX_FLOAT: return 1.f;
  }
  return 1.f;
}
float tptex_one_value_inv(tptex_data_type dt) {
  switch (dt) {
    case TPTEX_UINT8: return 1.f / 255.f;
    case TPTEX_UINT16: return 1.f / 65535.f;
    case TPTEX_HALF: return 1.f;
    case TPTEX_FLOAT: return 1.f;
  }
  return 1.f;
}

int tptex_is_constant(const void* data, size_t stride, int ures, int vres, int pixel_size) {
  const uint8_t* base = (const uint8_t*)data;
  size_t rowlen = (size_t)pixel_size * (size_t)ures;
  int i;
  for (i = 1; i < vres; ++i)
    if (memcmp(base, base + (size_t)i * stride, rowlen) != 0) return 0;
  for (i = 1; i < ures; ++i)
    if (memcmp(base, base + (size_t)i * (size_t)pixel_size, (size_t)pixel_size) != 0) return 0;
  return 1;
}

/* ---- interleave / deinterleave -------------------------------------------- */
void tptex_interleave(const void* src, size_t sstride, int ures, int vres, void* dst,
                      size_t dstride, tptex_data_type dt, int nchannels) {
  const size_t es = elem_size(dt);
  const uint8_t* s = (const uint8_t*)src;
  uint8_t* d = (uint8_t*)dst;
  int c, v, u;
  if (es == 0u) return;
  for (c = 0; c < nchannels; ++c)
    for (v = 0; v < vres; ++v) {
      const uint8_t* srow = s + ((size_t)c * (size_t)vres + (size_t)v) * sstride;
      uint8_t* drow = d + (size_t)v * dstride + (size_t)c * es;
      for (u = 0; u < ures; ++u)
        memcpy(drow + (size_t)u * (size_t)nchannels * es, srow + (size_t)u * es, es);
    }
}

void tptex_deinterleave(const void* src, size_t sstride, int ures, int vres, void* dst,
                        size_t dstride, tptex_data_type dt, int nchannels) {
  const size_t es = elem_size(dt);
  const uint8_t* s = (const uint8_t*)src;
  uint8_t* d = (uint8_t*)dst;
  int c, v, u;
  if (es == 0u) return;
  for (c = 0; c < nchannels; ++c)
    for (v = 0; v < vres; ++v) {
      const uint8_t* srow = s + (size_t)v * sstride + (size_t)c * es;
      uint8_t* drow = d + ((size_t)c * (size_t)vres + (size_t)v) * dstride;
      for (u = 0; u < ures; ++u)
        memcpy(drow + (size_t)u * es, srow + (size_t)u * (size_t)nchannels * es, es);
    }
}

/* ---- difference codec (u8 / u16 only) -------------------------------------- */
void tptex_encode_difference(void* data, size_t size, tptex_data_type dt) {
  uint8_t* p = (uint8_t*)data;
  size_t i, n;
  if (dt == TPTEX_UINT8) {
    uint8_t prev = 0;
    for (i = 0; i < size; ++i) { uint8_t cur = p[i]; p[i] = (uint8_t)(cur - prev); prev = cur; }
  } else if (dt == TPTEX_UINT16) {
    uint16_t prev = 0;
    n = size / 2u;
    for (i = 0; i < n; ++i) {
      uint16_t cur = ld16(p + i * 2u);
      st16(p + i * 2u, (uint16_t)(cur - prev));
      prev = cur;
    }
  }
}
void tptex_decode_difference(void* data, size_t size, tptex_data_type dt) {
  uint8_t* p = (uint8_t*)data;
  size_t i, n;
  if (dt == TPTEX_UINT8) {
    uint8_t prev = 0;
    for (i = 0; i < size; ++i) { prev = (uint8_t)(p[i] + prev); p[i] = prev; }
  } else if (dt == TPTEX_UINT16) {
    uint16_t prev = 0;
    n = size / 2u;
    for (i = 0; i < n; ++i) {
      prev = (uint16_t)(ld16(p + i * 2u) + prev);
      st16(p + i * 2u, prev);
    }
  }
}

/* ---- typed element families ------------------------------------------------
 * LD(p)    : load one element as the arithmetic type (int or float)
 * QUARTER  : quarter(sum);  HALVE: halve(sum)
 * ST(p, v) : narrow and store
 */
#define LD_U8(p) ((int)*(p))
#define LD_U16(p) ((int)ld16(p))
#define LD_HALF(p) tptex_half_to_float(ld16(p))
#define LD_F32(p) ldf(p)
#define QUARTER_I(s) ((s) >> 2)
#define HALVE_I(s) ((s) >> 1)
#define QUARTER_F(s) (0.25f * (s))
#define HALVE_F(s) (0.5f * (s))
#define ST_U8(p, v) (*(p) = (uint8_t)(v))
#define ST_U16(p, v) st16((p), (uint16_t)(v))
#define ST_HALF(p, v) st16((p), tptex_float_to_half(v))
#define ST_F32(p, v) stf((p), (v))

#define DEFINE_REDUCE(NAME, ES, LD, QUARTER, HALVE, ST)                                     \
  static void reduce_##NAME(const uint8_t* src, size_t ss, int uw, int vw, uint8_t* dst,    \
                            size_t ds, int nchan) {                                         \
    const size_t es = (ES), nc = (size_t)nchan;                                             \
    int x, y, c;                                                                            \
    for (y = 0; y < vw / 2; ++y) {                                                          \
      const uint8_t* r0 = src + (size_t)(2 * y) * ss;                                       \
      const uint8_t* r1 = r0 + ss;                                                          \
      uint8_t* d = dst + (size_t)y * ds;                                                    \
      for (x = 0; x < uw / 2; ++x)                                                          \
        for (c = 0; c < nchan; ++c) {                                                       \
          const size_t i0 = ((size_t)(2 * x) * nc + (size_t)c) * es;                        \
          const size_t i1 = i0 + nc * es;                                                   \
          ST(d + ((size_t)x * nc + (size_t)c) * es,                                         \
             QUARTER(LD(r0 + i0) + LD(r0 + i1) + LD(r1 + i0) + LD(r1 + i1)));               \
        }                                                                                   \
    }                                                                                       \
  }                                                                                         \
  static void reduceu_##NAME(const uint8_t* src, size_t ss, int uw, int vw, uint8_t* dst,   \
                             size_t ds, int nchan) {                                        \
    const size_t es = (ES), nc = (size_t)nchan;                                             \
    int x, y, c;                                                                            \
    for (y = 0; y < vw; ++y) {                                                              \
      const uint8_t* r0 = src + (size_t)y * ss;                                             \
      uint8_t* d = dst + (size_t)y * ds;                                                    \
      for (x = 0; x < uw / 2; ++x)                                                          \
        for (c = 0; c < nchan; ++c) {                                                       \
          const size_t i0 = ((size_t)(2 * x) * nc + (size_t)c) * es;                        \
          ST(d + ((size_t)x * nc + (size_t)c) * es,                                         \
             HALVE(LD(r0 + i0) + LD(r0 + i0 + nc * es)));                                   \
        }                                                                                   \
    }                                                                                       \
  }                                                                                         \
  static void reducev_##NAME(const uint8_t* src, size_t ss, int uw, int vw, uint8_t* dst,   \
                             size_t ds, int nchan) {                                        \
    const size_t es = (ES), nc = (size_t)nchan;                                             \
    int x, y, c;                                                                            \
    for (y = 0; y < vw / 2; ++y) {                                                          \
      const uint8_t* r0 = src + (size_t)(2 * y) * ss;                                       \
      uint8_t* d = dst + (size_t)y * ds;                                                    \
      for (x = 0; x < uw; ++x)                                                              \
        for (c = 0; c < nchan; ++c) {                                                       \
          const size_t i0 = ((size_t)x * nc + (size_t)c) * es;                              \
          ST(d + i0, HALVE(LD(r0 + i0) + LD(r0 + ss + i0)));                                \
        }                                                                                   \
    }                                                                                       \
  }                                                                                         \
  /* Packed-triangle reduction. Output (x,y) averages the 2x2 block at                      \
   * (row 2y, col 2x) minus its bottom-right pixel, plus the mirrored pixel                 \
   * (row w-1-2x, col w-1-2y): the upstream pointer walk reduces to this. */                \
  static void reducetri_##NAME(const uint8_t* src, size_t ss, int w, uint8_t* dst,          \
                               size_t ds, int nchan) {                                      \
    const size_t es = (ES), nc = (size_t)nchan;                                             \
    int x, y, c;                                                                            \
    for (y = 0; y < w / 2; ++y) {                                                           \
      const uint8_t* r0 = src + (size_t)(2 * y) * ss;                                       \
      uint8_t* d = dst + (size_t)y * ds;                                                    \
      for (x = 0; x < w / 2; ++x)                                                           \
        for (c = 0; c < nchan; ++c) {                                                       \
          const size_t i0 = ((size_t)(2 * x) * nc + (size_t)c) * es;                        \
          const uint8_t* m = src + (size_t)(w - 1 - 2 * x) * ss +                           \
                             ((size_t)(w - 1 - 2 * y) * nc + (size_t)c) * es;               \
          ST(d + ((size_t)x * nc + (size_t)c) * es,                                         \
             QUARTER(LD(r0 + i0) + LD(r0 + i0 + nc * es) + LD(r0 + ss + i0) + LD(m)));      \
        }                                                                                   \
    }                                                                                       \
  }

DEFINE_REDUCE(u8, 1, LD_U8, QUARTER_I, HALVE_I, ST_U8)
DEFINE_REDUCE(u16, 2, LD_U16, QUARTER_I, HALVE_I, ST_U16)
DEFINE_REDUCE(half, 2, LD_HALF, QUARTER_F, HALVE_F, ST_HALF)
DEFINE_REDUCE(f32, 4, LD_F32, QUARTER_F, HALVE_F, ST_F32)

#define DISPATCH_REDUCE(FN, ...)                                                            \
  switch (dt) {                                                                             \
    case TPTEX_UINT8: FN##_u8(__VA_ARGS__); break;                                          \
    case TPTEX_UINT16: FN##_u16(__VA_ARGS__); break;                                        \
    case TPTEX_HALF: FN##_half(__VA_ARGS__); break;                                         \
    case TPTEX_FLOAT: FN##_f32(__VA_ARGS__); break;                                         \
  }

void tptex_reduce(const void* src, size_t sstride, int ures, int vres, void* dst,
                  size_t dstride, tptex_data_type dt, int nchannels) {
  DISPATCH_REDUCE(reduce, (const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, dstride, nchannels)
}
void tptex_reduce_u(const void* src, size_t sstride, int ures, int vres, void* dst,
                    size_t dstride, tptex_data_type dt, int nchannels) {
  DISPATCH_REDUCE(reduceu, (const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, dstride, nchannels)
}
void tptex_reduce_v(const void* src, size_t sstride, int ures, int vres, void* dst,
                    size_t dstride, tptex_data_type dt, int nchannels) {
  DISPATCH_REDUCE(reducev, (const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, dstride, nchannels)
}
void tptex_reduce_tri(const void* src, size_t sstride, int w, void* dst, size_t dstride,
                      tptex_data_type dt, int nchannels) {
  DISPATCH_REDUCE(reducetri, (const uint8_t*)src, sstride, w, (uint8_t*)dst, dstride, nchannels)
}

/* ---- average ---------------------------------------------------------------- */
#define DEFINE_AVERAGE(NAME, ES, LDF, STF)                                                   \
  static void average_##NAME(const uint8_t* src, size_t ss, int uw, int vw, uint8_t* dst,    \
                             int nchan) {                                                    \
    const size_t es = (ES), nc = (size_t)nchan;                                              \
    const float scale = 1.0f / (float)(uw * vw);                                             \
    int c, x, y;                                                                             \
    /* per-channel sums are accumulated in raster order, as upstream does */                 \
    for (c = 0; c < nchan; ++c) {                                                            \
      float sum = 0.0f;                                                                      \
      for (y = 0; y < vw; ++y)                                                               \
        for (x = 0; x < uw; ++x)                                                             \
          sum += LDF(src + (size_t)y * ss + ((size_t)x * nc + (size_t)c) * es);              \
      STF(dst + (size_t)c * es, sum * scale);                                                \
    }                                                                                        \
  }
#define LDF_U8(p) ((float)*(p))
#define LDF_U16(p) ((float)ld16(p))
#define LDF_HALF(p) tptex_half_to_float(ld16(p))
#define LDF_F32(p) ldf(p)
#define STF_U8(p, v) (*(p) = f2u8(v))
#define STF_U16(p, v) st16((p), f2u16(v))
#define STF_HALF(p, v) st16((p), tptex_float_to_half(v))
#define STF_F32(p, v) stf((p), (v))
DEFINE_AVERAGE(u8, 1, LDF_U8, STF_U8)
DEFINE_AVERAGE(u16, 2, LDF_U16, STF_U16)
DEFINE_AVERAGE(half, 2, LDF_HALF, STF_HALF)
DEFINE_AVERAGE(f32, 4, LDF_F32, STF_F32)

void tptex_average(const void* src, size_t sstride, int ures, int vres, void* dst,
                   tptex_data_type dt, int nchannels) {
  switch (dt) {
    case TPTEX_UINT8: average_u8((const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, nchannels); break;
    case TPTEX_UINT16: average_u16((const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, nchannels); break;
    case TPTEX_HALF: average_half((const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, nchannels); break;
    case TPTEX_FLOAT: average_f32((const uint8_t*)src, sstride, ures, vres, (uint8_t*)dst, nchannels); break;
  }
}

/* ---- fill / copy ------------------------------------------------------------- */
void tptex_fill(const void* pixel, void* dst, size_t dstride, int ures, int vres, int pixel_size) {
  uint8_t* d = (uint8_t*)dst;
  const size_t ps = (size_t)pixel_size;
  const size_t rowlen = (size_t)ures * ps;
  int i, v;
  for (i = 0; i < ures; ++i) memcpy(d + (size_t)i * ps, pixel, ps);
  for (v = 1; v < vres; ++v) memcpy(d + (size_t)v * dstride, d, rowlen);
}

void tptex_copy(const void* src, size_t sstride, void* dst, size_t dstride, int nrows,
                size_t rowlen) {
  const uint8_t* s = (const uint8_t*)src;
  uint8_t* d = (uint8_t*)dst;
  int v;
  if (sstride == rowlen && dstride == rowlen) {
    memcpy(d, s, (size_t)nrows * rowlen);
    return;
  }
  for (v = 0; v < nrows; ++v) memcpy(d + (size_t)v * dstride, s + (size_t)v * sstride, rowlen);
}

/* ---- blend --------------------------------------------------------------------- */
/* dst = T(dst + T(weight * src)): the inner T() narrows first, then the sum is
 * narrowed again. NARROW_IN narrows the weighted source to the element type,
 * ADD combines it with dst. */
#define DEFINE_BLEND(NAME, ES, LDV, NARROW_IN, ADD_ST)                                       \
  static void blend_##NAME(const uint8_t* src, float weight, uint8_t* dst, int flip,         \
                           int rowlen, int nchan) {                                          \
    const size_t es = (ES), nc = (size_t)nchan;                                              \
    int p, c;                                                                                \
    for (p = 0; p < rowlen; ++p) {                                                           \
      const size_t dp = flip ? (size_t)(rowlen - 1 - p) : (size_t)p;                         \
      for (c = 0; c < nchan; ++c) {                                                          \
        const uint8_t* sp = src + ((size_t)p * nc + (size_t)c) * es;                         \
        uint8_t* dpp = dst + (dp * nc + (size_t)c) * es;                                     \
        ADD_ST(dpp, NARROW_IN(weight * LDV(sp)));                                            \
      }                                                                                      \
    }                                                                                        \
  }
#define LDV_U8(p) ((float)*(p))
#define LDV_U16(p) ((float)ld16(p))
#define LDV_HALF(p) tptex_half_to_float(ld16(p))
#define LDV_F32(p) ldf(p)
#define NI_U8(v) f2u8(v)
#define NI_U16(v) f2u16(v)
#define NI_HALF(v) tptex_float_to_half(v)
#define NI_F32(v) (v)
#define ADDST_U8(p, in) (*(p) = (uint8_t)(*(p) + (in)))
#define ADDST_U16(p, in) st16((p), (uint16_t)(ld16(p) + (in)))
#define ADDST_HALF(p, in) st16((p), tptex_float_to_half(tptex_half_to_float(ld16(p)) + tptex_half_to_float(in)))
#define ADDST_F32(p, in) stf((p), ldf(p) + (in))
DEFINE_BLEND(u8, 1, LDV_U8, NI_U8, ADDST_U8)
DEFINE_BLEND(u16, 2, LDV_U16, NI_U16, ADDST_U16)
DEFINE_BLEND(half, 2, LDV_HALF, NI_HALF, ADDST_HALF)
DEFINE_BLEND(f32, 4, LDV_F32, NI_F32, ADDST_F32)

void tptex_blend(const void* src, float weight, void* dst, int flip, int rowlen,
                 tptex_data_type dt, int nchannels) {
  switch (dt) {
    case TPTEX_UINT8: blend_u8((const uint8_t*)src, weight, (uint8_t*)dst, flip, rowlen, nchannels); break;
    case TPTEX_UINT16: blend_u16((const uint8_t*)src, weight, (uint8_t*)dst, flip, rowlen, nchannels); break;
    case TPTEX_HALF: blend_half((const uint8_t*)src, weight, (uint8_t*)dst, flip, rowlen, nchannels); break;
    case TPTEX_FLOAT: blend_f32((const uint8_t*)src, weight, (uint8_t*)dst, flip, rowlen, nchannels); break;
  }
}

/* ---- alpha ------------------------------------------------------------------- */
#define DEFINE_ALPHA(NAME, ES, LDF, STF, ZERO_TEST)                                          \
  static void multalpha_##NAME(uint8_t* data, int npixels, int nchannels, int alphachan,     \
                               float scale) {                                                \
    const size_t es = (ES);                                                                  \
    int aoff, nmul, i, c;                                                                    \
    size_t first;                                                                            \
    if (alphachan == 0) { first = 1u; aoff = 0; nmul = nchannels - 1; }                      \
    else { first = 0u; aoff = alphachan; nmul = alphachan; }                                 \
    for (i = 0; i < npixels; ++i) {                                                          \
      uint8_t* px = data + (size_t)i * (size_t)nchannels * es;                               \
      float aval = scale * LDF(px + (size_t)aoff * es);                                      \
      for (c = 0; c < nmul; ++c) {                                                           \
        uint8_t* cp = px + (first + (size_t)c) * es;                                         \
        STF(cp, LDF(cp) * aval);                                                             \
      }                                                                                      \
    }                                                                                        \
  }                                                                                          \
  static void divalpha_##NAME(uint8_t* data, int npixels, int nchannels, int alphachan,      \
                              float scale) {                                                 \
    const size_t es = (ES);                                                                  \
    int aoff, ndiv, i, c;                                                                    \
    size_t first;                                                                            \
    if (alphachan == 0) { first = 1u; aoff = 0; ndiv = nchannels - 1; }                      \
    else { first = 0u; aoff = alphachan; ndiv = alphachan; }                                 \
    for (i = 0; i < npixels; ++i) {                                                          \
      uint8_t* px = data + (size_t)i * (size_t)nchannels * es;                               \
      float alpha = LDF(px + (size_t)aoff * es);                                             \
      float aval;                                                                            \
      if (ZERO_TEST(alpha)) continue;                                                        \
      aval = scale / alpha;                                                                  \
      for (c = 0; c < ndiv; ++c) {                                                           \
        uint8_t* cp = px + (first + (size_t)c) * es;                                         \
        STF(cp, LDF(cp) * aval);                                                             \
      }                                                                                      \
    }                                                                                        \
  }
#define IS_ZERO(a) ((a) == 0.0f)
DEFINE_ALPHA(u8, 1, LDF_U8, STF_U8, IS_ZERO)
DEFINE_ALPHA(u16, 2, LDF_U16, STF_U16, IS_ZERO)
DEFINE_ALPHA(half, 2, LDF_HALF, STF_HALF, IS_ZERO)
DEFINE_ALPHA(f32, 4, LDF_F32, STF_F32, IS_ZERO)

void tptex_multalpha(void* data, int npixels, tptex_data_type dt, int nchannels, int alphachan) {
  const float scale = tptex_one_value_inv(dt);
  switch (dt) {
    case TPTEX_UINT8: multalpha_u8((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_UINT16: multalpha_u16((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_HALF: multalpha_half((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_FLOAT: multalpha_f32((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
  }
}
void tptex_divalpha(void* data, int npixels, tptex_data_type dt, int nchannels, int alphachan) {
  const float scale = tptex_one_value(dt);
  switch (dt) {
    case TPTEX_UINT8: divalpha_u8((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_UINT16: divalpha_u16((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_HALF: divalpha_half((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
    case TPTEX_FLOAT: divalpha_f32((uint8_t*)data, npixels, nchannels, alphachan, scale); break;
  }
}

/* ---- reduction face ordering ---------------------------------------------------- */
void tptex_gen_rfaceids(const tptex_face_info* faces, uint32_t nfaces, uint32_t* rfaceids,
                        uint32_t* faceids) {
  /* stable counting sort by key = min(ulog2, vlog2) (constant faces: 1),
   * descending; equal keys keep ascending face order (std::stable_sort). */
  uint32_t counts[256];
  uint32_t i, k;
  uint32_t running = 0;
  memset(counts, 0, sizeof counts);
  for (i = 0; i < nfaces; ++i) {
    const tptex_face_info* f = &faces[i];
    int key = tptex_face_is_constant(f) ? 1 : (f->res.ulog2 < f->res.vlog2 ? f->res.ulog2 : f->res.vlog2);
    ++counts[(uint32_t)(127 - key) & 255u]; /* descending key => ascending bucket */
  }
  for (k = 0; k < 256u; ++k) { uint32_t c = counts[k]; counts[k] = running; running += c; }
  for (i = 0; i < nfaces; ++i) {
    const tptex_face_info* f = &faces[i];
    int key = tptex_face_is_constant(f) ? 1 : (f->res.ulog2 < f->res.vlog2 ? f->res.ulog2 : f->res.vlog2);
    uint32_t rank = counts[(uint32_t)(127 - key) & 255u]++;
    faceids[rank] = i;
    rfaceids[i] = rank;
  }
}

/* ---- apply const / conversions ----------------------------------------------------- */
void tptex_apply_const(float weight, float* dst, const void* data, tptex_data_type dt, int nchannels) {
  const uint8_t* p = (const uint8_t*)data;
  int i;
  switch (dt) {
    case TPTEX_UINT8: for (i = 0; i < nchannels; ++i) dst[i] += (float)p[i] * weight; break;
    case TPTEX_UINT16: for (i = 0; i < nchannels; ++i) dst[i] += (float)ld16(p + (size_t)i * 2u) * weight; break;
    case TPTEX_HALF: for (i = 0; i < nchannels; ++i) dst[i] += tptex_half_to_float(ld16(p + (size_t)i * 2u)) * weight; break;
    case TPTEX_FLOAT: for (i = 0; i < nchannels; ++i) dst[i] += ldf(p + (size_t)i * 4u) * weight; break;
  }
}

void tptex_convert_to_float(float* dst, const void* src, tptex_data_type dt, int nchannels) {
  const uint8_t* p = (const uint8_t*)src;
  const float s8 = 1.f / 255.f, s16 = 1.f / 65535.f;
  int i;
  switch (dt) {
    /* `* scale + round` with round == 0: kept literally so -0 becomes +0 as upstream */
    case TPTEX_UINT8: for (i = 0; i < nchannels; ++i) dst[i] = (float)p[i] * s8 + 0.0f; break;
    case TPTEX_UINT16: for (i = 0; i < nchannels; ++i) dst[i] = (float)ld16(p + (size_t)i * 2u) * s16 + 0.0f; break;
    case TPTEX_HALF: for (i = 0; i < nchannels; ++i) dst[i] = tptex_half_to_float(ld16(p + (size_t)i * 2u)) * 1.0f + 0.0f; break;
    case TPTEX_FLOAT: memcpy(dst, src, sizeof(float) * (size_t)nchannels); break;
  }
}

static float clamp01(float x) {
  /* PtexUtils::clamp = min(max(x, 0), 1) with `a > b ? a : b` / `a < b ? a : b` */
  float m = x > 0.0f ? x : 0.0f;
  return m < 1.0f ? m : 1.0f;
}

void tptex_convert_from_float(void* dst, const float* src, tptex_data_type dt, int nchannels) {
  uint8_t* p = (uint8_t*)dst;
  int i;
  switch (dt) {
    case TPTEX_UINT8: for (i = 0; i < nchannels; ++i) p[i] = f2u8(clamp01(src[i]) * 255.0f + 0.5f); break;
    case TPTEX_UINT16: for (i = 0; i < nchannels; ++i) st16(p + (size_t)i * 2u, f2u16(clamp01(src[i]) * 65535.0f + 0.5f)); break;
    case TPTEX_HALF: for (i = 0; i < nchannels; ++i) st16(p + (size_t)i * 2u, tptex_float_to_half(src[i] * 1.0f + 0.0f)); break;
    case TPTEX_FLOAT: memcpy(dst, src, sizeof(float) * (size_t)nchannels); break;
  }
}
