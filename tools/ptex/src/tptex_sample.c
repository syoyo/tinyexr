/* SPDX-License-Identifier: BSD-3-Clause */
/* lptex-sample: stateless Ptex sampling math. See tptex_sample.h.
 *
 * The min/max/clamp helpers reproduce std::min/std::max/std::clamp exactly
 * (including their NaN behaviour), so results are bit-identical to the
 * former C++ sampler for finite inputs. Float-to-int conversions are guarded
 * so NaN/inf inputs are defined behaviour here. */
#include "../include/tptex_sample.h"

#include <math.h>
#include <string.h>

static float maxf(float a, float b) { return (a < b) ? b : a; }
static float minf(float a, float b) { return (b < a) ? b : a; }
static float clampf(float v, float lo, float hi) {
  return (v < lo) ? lo : (hi < v) ? hi : v;
}
static int clampi(int v, int lo, int hi) {
  return (v < lo) ? lo : (hi < v) ? hi : v;
}
static int mini(int a, int b) { return (b < a) ? b : a; }
static uint32_t maxu(uint32_t a, uint32_t b) { return (a < b) ? b : a; }
static uint32_t minu(uint32_t a, uint32_t b) { return (b < a) ? b : a; }

/* floor() as int; NaN maps to 0 and the result saturates to the int range. */
static int floor_to_int(float f) {
  const float r = floorf(f);
  if (isnan(r)) return 0;
  if (r <= -2147483648.0f) return -2147483647 - 1;
  if (r >= 2147483647.0f) return 2147483647;
  return (int)r;
}
static uint32_t float_to_u32(float f) {
  if (!(f >= 0.0f)) return 0;
  if (f >= 4294967040.0f) return 4294967040u;
  return (uint32_t)f;
}

float tptex_sample_half_to_float(uint16_t h) {
  const uint32_t sign = (uint32_t)(h >> 15) << 31;
  const uint32_t exp = (h >> 10) & 0x1fu;
  uint32_t mant = h & 0x3ffu;
  uint32_t bits;
  float out;
  if (exp == 0) {
    if (mant == 0) {
      bits = sign;
    } else {
      int e = -1;
      do {
        ++e;
        mant <<= 1;
      } while ((mant & 0x400u) == 0);
      bits = sign | ((uint32_t)(127 - 15 - e) << 23) | ((mant & 0x3ffu) << 13);
    }
  } else if (exp == 31) {
    bits = sign | 0x7f800000u | (mant << 13);
  } else {
    bits = sign | ((exp + 112u) << 23) | (mant << 13);
  }
  memcpy(&out, &bits, sizeof(out));
  return out;
}

float tptex_srgb_to_linear(float c) {
  if (c <= 0.04045f) return c / 12.92f;
  return powf((c + 0.055f) / 1.055f, 2.4f);
}

static uint32_t face_edge(const tptex_face_info* fi) {
  return maxu(1u << fi->res.ulog2, 1u << fi->res.vlog2);
}

uint32_t tptex_choose_mip(const tptex_face_info* face, uint32_t levels,
                          float uv_per_pixel) {
  float texels, level;
  if (!face || levels == 0) return 0;
  {
  const uint32_t edge = face_edge(face);
  texels = maxf(1.0f, uv_per_pixel * (float)edge);
  level = floorf(log2f(texels));
  if (!(level >= 0.0f)) level = 0.0f; /* also catches NaN */
  return minu(levels - 1u, float_to_u32(level));
  }
}

void tptex_compute_uv_footprint(const tptex_face_info* face, uint32_t levels,
                                const float gu[3], const float gv[3],
                                float world_footprint, tptex_footprint* out) {
  float a, b, c, trace, disc, lmax, lmin, w, dir_len, texels, level, ratio,
      taps;
  uint32_t edge;
  if (!out) return;
  out->major = 0.0f;
  out->minor = 0.0f;
  out->dir_u = 1.0f;
  out->dir_v = 0.0f;
  out->mip = 0;
  out->taps = 1;
  if (!face || levels == 0 || !gu || !gv) return;
  a = gu[0] * gu[0] + gu[1] * gu[1] + gu[2] * gu[2];
  b = gu[0] * gv[0] + gu[1] * gv[1] + gu[2] * gv[2];
  c = gv[0] * gv[0] + gv[1] * gv[1] + gv[2] * gv[2];
  trace = a + c;
  disc = sqrtf(maxf((a - c) * (a - c) + 4.0f * b * b, 0.0f));
  lmax = 0.5f * (trace + disc);
  lmin = 0.5f * (trace - disc);
  if (!(lmax >= 0.0f)) lmax = 0.0f;
  if (!(lmin >= 0.0f)) lmin = 0.0f;
  w = maxf(world_footprint, 0.0f);
  out->major = w * sqrtf(lmax);
  out->minor = w * sqrtf(lmin);
  if (fabsf(b) > 1.0e-12f) {
    out->dir_u = b;
    out->dir_v = lmax - a;
  } else if (a >= c) {
    out->dir_u = 1.0f;
    out->dir_v = 0.0f;
  } else {
    out->dir_u = 0.0f;
    out->dir_v = 1.0f;
  }
  dir_len = sqrtf(out->dir_u * out->dir_u + out->dir_v * out->dir_v);
  if (dir_len > 1.0e-12f) {
    out->dir_u /= dir_len;
    out->dir_v /= dir_len;
  } else {
    out->dir_u = 1.0f;
    out->dir_v = 0.0f;
  }
  edge = face_edge(face);
  texels = maxf(1.0f, out->minor * (float)edge);
  level = floorf(log2f(texels));
  if (!(level >= 0.0f)) level = 0.0f;
  out->mip = minu(levels - 1u, float_to_u32(level));
  ratio = out->minor > 1.0e-9f ? out->major / out->minor : 1.0f;
  taps = ceilf(ratio);
  if (!(taps >= 1.0f)) taps = 1.0f;
  out->taps = float_to_u32(minf(8.0f, taps));
}

uint32_t tptex_footprint_taps(const tptex_footprint* fp) {
  if (!fp || fp->taps <= 1u) return 1u;
  return minu(8u, fp->taps);
}

int tptex_cross_edge(const tptex_face_info* faces, uint32_t nfaces,
                     uint32_t* face, float* u, float* v) {
  const tptex_face_info* fi;
  int edge, adj_edge, rot;
  int32_t adjacent;
  float uu, vv, ru, rv;
  if (!faces || !face || !u || !v || *face >= nfaces) return 0;
  fi = &faces[*face];
  if ((fi->flags & TPTEX_FACE_SUBFACE) != 0) return 0;
  if (*u < 0.0f) edge = 3;       /* left */
  else if (*u > 1.0f) edge = 1;  /* right */
  else if (*v < 0.0f) edge = 0;  /* bottom */
  else if (*v > 1.0f) edge = 2;  /* top */
  else return 0;
  adjacent = fi->adjfaces[edge];
  if (adjacent < 0 || (uint32_t)adjacent >= nfaces) return 0;
  adj_edge = (fi->adjedges >> (2 * edge)) & 3;
  uu = *u;
  vv = *v;
  if (edge == 3) uu += 1.0f;
  else if (edge == 1) uu -= 1.0f;
  else if (edge == 0) vv += 1.0f;
  else vv -= 1.0f;
  rot = (edge - adj_edge + 2) & 3;
  ru = uu;
  rv = vv;
  if (rot == 1) {
    ru = vv;
    rv = 1.0f - uu;
  } else if (rot == 2) {
    ru = 1.0f - uu;
    rv = 1.0f - vv;
  } else if (rot == 3) {
    ru = 1.0f - vv;
    rv = uu;
  }
  *face = (uint32_t)adjacent;
  *u = ru;
  *v = rv;
  return 1;
}

int tptex_resolve_tap(const tptex_face_info* faces, uint32_t nfaces,
                      uint32_t* face, float* u, float* v) {
  int hop, crossed = 0;
  for (hop = 0; hop < 2; ++hop) {
    if (*u >= 0.0f && *u <= 1.0f && *v >= 0.0f && *v <= 1.0f) break;
    if (!tptex_cross_edge(faces, nfaces, face, u, v)) break;
    crossed = 1;
  }
  return crossed;
}

void tptex_page_bilinear(uint32_t w, uint32_t h, float u, float v,
                         tptex_bilinear* out) {
  const float fx = clampf(u, 0.0f, 1.0f) * (float)w - 0.5f;
  const float fy = clampf(v, 0.0f, 1.0f) * (float)h - 0.5f;
  const int wi = w > 0x7fffffffu ? 0x7fffffff : (int)w;
  const int hi = h > 0x7fffffffu ? 0x7fffffff : (int)h;
  out->x0 = clampi(floor_to_int(fx), 0, wi - 1);
  out->y0 = clampi(floor_to_int(fy), 0, hi - 1);
  out->x1 = mini(out->x0 + 1, wi - 1);
  out->y1 = mini(out->y0 + 1, hi - 1);
  out->tx = clampf(fx - floorf(fx), 0.0f, 1.0f);
  out->ty = clampf(fy - floorf(fy), 0.0f, 1.0f);
}

static int page_ok(const tptex_image* page) {
  return page && page->width && page->height && page->channels &&
         page->data &&
         page->size / page->width / page->height >= page->channels;
}

static void texel_rgb(const tptex_image* page, int x, int y, float out[3]) {
  const size_t index =
      ((size_t)y * page->width + (size_t)x) * page->channels;
  const uint8_t* px = page->data + index;
  const float r = (float)px[0] / 255.0f;
  const float g = page->channels > 1 ? (float)px[1] / 255.0f : r;
  const float b = page->channels > 2 ? (float)px[2] / 255.0f : r;
  out[0] = r;
  out[1] = g;
  out[2] = b;
}

void tptex_sample_page_rgb(const tptex_image* page, float u, float v,
                           float out[3]) {
  tptex_bilinear t;
  float c00[3], c10[3], c01[3], c11[3];
  int c;
  if (!page_ok(page)) {
    out[0] = out[1] = out[2] = 0.0f;
    return;
  }
  tptex_page_bilinear(page->width, page->height, u, v, &t);
  texel_rgb(page, t.x0, t.y0, c00);
  texel_rgb(page, t.x1, t.y0, c10);
  texel_rgb(page, t.x0, t.y1, c01);
  texel_rgb(page, t.x1, t.y1, c11);
  for (c = 0; c < 3; ++c) {
    const float top = c00[c] * (1.0f - t.tx) + c10[c] * t.tx;
    const float bot = c01[c] * (1.0f - t.tx) + c11[c] * t.tx;
    out[c] = top * (1.0f - t.ty) + bot * t.ty;
  }
}

static float texel_channel(const tptex_image* page, int x, int y, int c) {
  return (float)page->data[((size_t)y * page->width + (size_t)x) *
                               page->channels +
                           (size_t)c] /
         255.0f;
}

void tptex_sample_page_channel(const tptex_image* page, float u, float v,
                               int channel, float* out) {
  tptex_bilinear t;
  float top, bot;
  int c;
  if (!page_ok(page)) {
    *out = 0.0f;
    return;
  }
  tptex_page_bilinear(page->width, page->height, u, v, &t);
  c = clampi(channel, 0, (int)page->channels - 1);
  top = texel_channel(page, t.x0, t.y0, c) * (1.0f - t.tx) +
        texel_channel(page, t.x1, t.y0, c) * t.tx;
  bot = texel_channel(page, t.x0, t.y1, c) * (1.0f - t.tx) +
        texel_channel(page, t.x1, t.y1, c) * t.tx;
  *out = top * (1.0f - t.ty) + bot * t.ty;
}

/* Fetch a tap page with the mip clamped to the last level. */
static int fetch_tap(const tptex_sample_source* src, uint32_t face,
                     uint32_t mip, tptex_image* page) {
  const uint32_t m = src->levels ? minu(mip, src->levels - 1u) : 0u;
  if (face >= src->nfaces) return 0;
  return src->fetch(src->user, face, m, page);
}

static void tap_rgb(const tptex_sample_source* src, uint32_t face,
                    uint32_t mip, float u, float v, float out[3],
                    uint64_t* cross_taps) {
  tptex_image page;
  if (tptex_resolve_tap(src->faces, src->nfaces, &face, &u, &v) && cross_taps)
    ++*cross_taps;
  memset(&page, 0, sizeof(page));
  if (!fetch_tap(src, face, mip, &page)) {
    out[0] = out[1] = out[2] = 0.0f;
    return;
  }
  tptex_sample_page_rgb(&page, u, v, out);
}

static void tap_channel(const tptex_sample_source* src, uint32_t face,
                        uint32_t mip, float u, float v, int channel,
                        float* out, uint64_t* cross_taps) {
  tptex_image page;
  if (tptex_resolve_tap(src->faces, src->nfaces, &face, &u, &v) && cross_taps)
    ++*cross_taps;
  memset(&page, 0, sizeof(page));
  if (!fetch_tap(src, face, mip, &page)) {
    *out = 0.0f;
    return;
  }
  tptex_sample_page_channel(&page, u, v, channel, out);
}

/* Base-page lattice shared by the RGB and channel samplers. */
typedef struct lattice {
  float u0, u1, v0, v1, tx, ty;
} lattice;

static int base_lattice(const tptex_sample_source* src, uint32_t face,
                        uint32_t mip, float u, float v, lattice* l,
                        uint16_t* channels) {
  tptex_image page;
  float fx, fy;
  int ix0, iy0;
  uint32_t w, h;
  if (!src || !src->fetch || face >= src->nfaces) return 0;
  memset(&page, 0, sizeof(page));
  if (!src->fetch(src->user, face, mip, &page)) return 0;
  if (page.type != TPTEX_UINT8) return 0;
  w = page.width;
  h = page.height;
  if (!w || !h || page.channels == 0) return 0;
  *channels = page.channels;
  fx = clampf(u, 0.0f, 1.0f) * (float)w - 0.5f;
  fy = clampf(v, 0.0f, 1.0f) * (float)h - 0.5f;
  ix0 = floor_to_int(fx);
  iy0 = floor_to_int(fy);
  /* A filter tap outside [0,1] follows the Ptex adjacency into the
   * neighbouring face instead of clamping at the seam. */
  l->u0 = ((float)ix0 + 0.5f) / (float)w;
  l->u1 = ((float)(ix0 + 1) + 0.5f) / (float)w;
  l->v0 = ((float)iy0 + 0.5f) / (float)h;
  l->v1 = ((float)(iy0 + 1) + 0.5f) / (float)h;
  l->tx = clampf(fx - floorf(fx), 0.0f, 1.0f);
  l->ty = clampf(fy - floorf(fy), 0.0f, 1.0f);
  return 1;
}

int tptex_sample_rgb(const tptex_sample_source* src, uint32_t face,
                     uint32_t mip, float u, float v, int srgb, float out[3],
                     uint64_t* cross_taps) {
  lattice l;
  uint16_t channels = 0;
  float c00[3], c10[3], c01[3], c11[3];
  int c;
  if (!base_lattice(src, face, mip, u, v, &l, &channels)) return 0;
  tap_rgb(src, face, mip, l.u0, l.v0, c00, cross_taps);
  tap_rgb(src, face, mip, l.u1, l.v0, c10, cross_taps);
  tap_rgb(src, face, mip, l.u0, l.v1, c01, cross_taps);
  tap_rgb(src, face, mip, l.u1, l.v1, c11, cross_taps);
  for (c = 0; c < 3; ++c) {
    const float top = c00[c] * (1.0f - l.tx) + c10[c] * l.tx;
    const float bot = c01[c] * (1.0f - l.tx) + c11[c] * l.tx;
    float value = top * (1.0f - l.ty) + bot * l.ty;
    if (srgb) value = tptex_srgb_to_linear(value);
    out[c] = value;
  }
  return 1;
}

int tptex_sample_channel(const tptex_sample_source* src, uint32_t face,
                         uint32_t mip, float u, float v, int channel,
                         float* out, uint64_t* cross_taps) {
  lattice l;
  uint16_t channels = 0;
  float c00 = 0.0f, c10 = 0.0f, c01 = 0.0f, c11 = 0.0f, top, bot;
  int c;
  if (!base_lattice(src, face, mip, u, v, &l, &channels)) return 0;
  c = clampi(channel, 0, (int)channels - 1);
  tap_channel(src, face, mip, l.u0, l.v0, c, &c00, cross_taps);
  tap_channel(src, face, mip, l.u1, l.v0, c, &c10, cross_taps);
  tap_channel(src, face, mip, l.u0, l.v1, c, &c01, cross_taps);
  tap_channel(src, face, mip, l.u1, l.v1, c, &c11, cross_taps);
  top = c00 * (1.0f - l.tx) + c10 * l.tx;
  bot = c01 * (1.0f - l.tx) + c11 * l.tx;
  *out = top * (1.0f - l.ty) + bot * l.ty;
  return 1;
}

int tptex_sample_footprint_rgb(const tptex_sample_source* src, uint32_t face,
                               const tptex_footprint* fp, float u, float v,
                               int srgb, float out[3], uint64_t* cross_taps,
                               uint32_t* samples) {
  uint32_t n, i, ok = 0;
  float step, center, inv, weight_sum = 0.0f;
  float sum[3] = {0.0f, 0.0f, 0.0f};
  int c;
  if (samples) *samples = 0;
  if (!fp) return 0;
  if (fp->taps <= 1u) {
    const int r = tptex_sample_rgb(src, face, fp->mip, u, v, srgb, out,
                                   cross_taps);
    if (samples) *samples = r ? 1u : 0u;
    return r;
  }
  n = tptex_footprint_taps(fp);
  step = maxf(fp->minor, 1.0e-6f);
  center = 0.5f * (float)(n - 1u);
  for (i = 0; i < n; ++i) {
    const float offset = ((float)i - center) * step;
    const float weight = (float)n * 0.5f - fabsf((float)i - center);
    float tap[3] = {0.0f, 0.0f, 0.0f};
    if (!tptex_sample_rgb(src, face, fp->mip, u + offset * fp->dir_u,
                          v + offset * fp->dir_v, 0, tap, cross_taps))
      continue;
    ++ok;
    sum[0] += tap[0] * weight;
    sum[1] += tap[1] * weight;
    sum[2] += tap[2] * weight;
    weight_sum += weight;
  }
  inv = weight_sum > 0.0f ? 1.0f / weight_sum : 0.0f;
  for (c = 0; c < 3; ++c) {
    float value = sum[c] * inv;
    if (srgb) value = tptex_srgb_to_linear(value);
    out[c] = value;
  }
  if (samples) *samples = ok;
  return 1;
}

int tptex_sample_footprint_channel(const tptex_sample_source* src,
                                   uint32_t face, const tptex_footprint* fp,
                                   float u, float v, int channel, float* out,
                                   uint64_t* cross_taps, uint32_t* samples) {
  uint32_t n, i, ok = 0;
  float step, center, sum = 0.0f, weight_sum = 0.0f;
  if (samples) *samples = 0;
  if (!fp) return 0;
  if (fp->taps <= 1u) {
    const int r = tptex_sample_channel(src, face, fp->mip, u, v, channel, out,
                                       cross_taps);
    if (samples) *samples = r ? 1u : 0u;
    return r;
  }
  n = tptex_footprint_taps(fp);
  step = maxf(fp->minor, 1.0e-6f);
  center = 0.5f * (float)(n - 1u);
  for (i = 0; i < n; ++i) {
    const float offset = ((float)i - center) * step;
    const float weight = (float)n * 0.5f - fabsf((float)i - center);
    float tap = 0.0f;
    if (tptex_sample_channel(src, face, fp->mip, u + offset * fp->dir_u,
                             v + offset * fp->dir_v, channel, &tap,
                             cross_taps))
      ++ok;
    sum += tap * weight;
    weight_sum += weight;
  }
  *out = weight_sum > 0.0f ? sum / weight_sum : 0.0f;
  if (samples) *samples = ok;
  return 1;
}
