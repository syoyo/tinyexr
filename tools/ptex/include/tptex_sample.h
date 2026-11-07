/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * lptex-sample: stateless Ptex sampling math in C11.
 *
 * Edge adjacency (including the two-hop corner case), texel addressing,
 * bilinear page sampling, the anisotropic footprint (minor-axis mip plus
 * tent-weighted taps along the major axis), sRGB decode and half-to-float.
 * Pages come from a caller callback, so cache policy (LRU, locking) stays
 * with the caller. Only 8-bit pages are filtered, matching the CPU preview.
 * Ported unchanged in behaviour from LightUSD's lptex-sample (Apache-2.0, same author).
 */
#ifndef TPTEX_SAMPLE_H_
#define TPTEX_SAMPLE_H_

#include <stddef.h>
#include <stdint.h>

#include "tptex.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Decoded page: channels interleaved, rows v-major starting at v=0. */
typedef struct tptex_image {
  uint32_t width;
  uint32_t height;
  uint16_t channels;
  tptex_data_type type;
  uint8_t* data;
  size_t size; /* bytes */
} tptex_image;

typedef struct tptex_footprint {
  float major;   /* largest UV extent per pixel */
  float minor;   /* smallest UV extent per pixel */
  float dir_u;   /* unit major direction in (u,v) */
  float dir_v;
  uint32_t mip;  /* selected from the minor axis */
  uint32_t taps; /* clamp(ceil(major/minor), 1, 8) */
} tptex_footprint;

float tptex_sample_half_to_float(uint16_t h);
float tptex_srgb_to_linear(float c);

/* Mip whose texel size matches `uv_per_pixel` for this face. */
uint32_t tptex_choose_mip(const tptex_face_info* face, uint32_t levels,
                          float uv_per_pixel);

/* Footprint of an isotropic world-space pixel disk of radius
 * `world_footprint` under the world->UV gradients gu = du/dP, gv = dv/dP.
 * `face` NULL or levels == 0 yields the default footprint. */
void tptex_compute_uv_footprint(const tptex_face_info* face, uint32_t levels,
                                const float gu[3], const float gv[3],
                                float world_footprint, tptex_footprint* out);

/* Move a UV point that left the face across one edge using the Ptex
 * adjacency (PtexSeparableFilter::applyAcrossEdge rotation). Returns 0 when
 * there is no neighbour, the face uses subface adjacency, or (u,v) is
 * inside; the point is then unchanged. The other axis is left unclamped. */
int tptex_cross_edge(const tptex_face_info* faces, uint32_t nfaces,
                     uint32_t* face, float* u, float* v);

/* Up to two tptex_cross_edge() hops (edge then diagonal corner). Returns 1
 * when at least one hop happened. */
int tptex_resolve_tap(const tptex_face_info* faces, uint32_t nfaces,
                      uint32_t* face, float* u, float* v);

/* Clamped bilinear texel addressing inside one w x h page. */
typedef struct tptex_bilinear {
  int x0, y0, x1, y1;
  float tx, ty;
} tptex_bilinear;
void tptex_page_bilinear(uint32_t w, uint32_t h, float u, float v,
                         tptex_bilinear* out);

/* 8-bit page bilinear lookups; (u,v) clamped to the page. Channels beyond
 * the page replicate channel 0 for RGB. */
void tptex_sample_page_rgb(const tptex_image* page, float u, float v,
                           float out[3]);
void tptex_sample_page_channel(const tptex_image* page, float u, float v,
                               int channel, float* out);

/* Page provider: fill *page (borrowed until the next call) and return 1, or
 * return 0 when the page is unavailable. */
typedef int (*tptex_fetch_fn)(void* user, uint32_t face, uint32_t mip,
                              tptex_image* page);

typedef struct tptex_sample_source {
  const tptex_face_info* faces;
  uint32_t nfaces;
  uint32_t levels;
  tptex_fetch_fn fetch;
  void* user;
} tptex_sample_source;

/* Seam-aware bilinear sample at one mip: each of the four taps that leaves
 * the face follows the adjacency into the neighbour. Return 1 on success
 * (8-bit base page available). *cross_taps (optional) counts remapped taps. */
int tptex_sample_rgb(const tptex_sample_source* src, uint32_t face,
                     uint32_t mip, float u, float v, int srgb, float out[3],
                     uint64_t* cross_taps);
int tptex_sample_channel(const tptex_sample_source* src, uint32_t face,
                         uint32_t mip, float u, float v, int channel,
                         float* out, uint64_t* cross_taps);

/* Footprint sample. Isotropic footprints are one tptex_sample_*() call;
 * anisotropic ones take fp->taps (<= 8) taps one minor extent apart along
 * the major axis, tent-weighted. Returns 1 on success. *samples (optional)
 * receives the number of successful bilinear samples taken. */
int tptex_sample_footprint_rgb(const tptex_sample_source* src, uint32_t face,
                               const tptex_footprint* fp, float u, float v,
                               int srgb, float out[3], uint64_t* cross_taps,
                               uint32_t* samples);
int tptex_sample_footprint_channel(const tptex_sample_source* src,
                                   uint32_t face, const tptex_footprint* fp,
                                   float u, float v, int channel, float* out,
                                   uint64_t* cross_taps, uint32_t* samples);

/* Number of taps an anisotropic footprint sample takes (1 if isotropic). */
uint32_t tptex_footprint_taps(const tptex_footprint* fp);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_SAMPLE_H_ */
