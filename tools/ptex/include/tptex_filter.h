/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Ptex filters (PtexFilter): point, bilinear, box, gaussian, bicubic family for
 * quad meshes, and the elliptical gaussian triangle filter for triangle meshes.
 * A filter is not thread-safe (it owns scratch); create one per thread. Pixel
 * sums are accumulated in float; results match upstream to rounding (tiles are
 * applied as one face rather than tile by tile, which only changes sum order).
 */
#ifndef TPTEX_FILTER_H_
#define TPTEX_FILTER_H_

#include "tptex.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum tptex_filter_type {
  TPTEX_FILTER_POINT = 0,
  TPTEX_FILTER_BILINEAR = 1,
  TPTEX_FILTER_BOX = 2,
  TPTEX_FILTER_GAUSSIAN = 3,
  TPTEX_FILTER_BICUBIC = 4,   /* uses sharpness */
  TPTEX_FILTER_BSPLINE = 5,   /* sharpness 0 */
  TPTEX_FILTER_CATMULLROM = 6,/* sharpness 1 */
  TPTEX_FILTER_MITCHELL = 7   /* sharpness 2/3 */
} tptex_filter_type;

typedef struct tptex_filter_options {
  tptex_filter_type filter;
  int lerp;          /* interpolate between mip levels */
  float sharpness;   /* 0..1, bicubic only */
  int noedgeblend;   /* disable cross-face filtering */
  tptex_allocator allocator;
} tptex_filter_options;

typedef struct tptex_filter tptex_filter;

void tptex_filter_options_init(tptex_filter_options* options); /* box, no lerp */

/* The texture must outlive the filter. */
tptex_status tptex_filter_create(tptex_texture* texture, const tptex_filter_options* options,
                                 tptex_filter** out);
void tptex_filter_destroy(tptex_filter* filter);

/* Filter `nchannels` channels from `firstchan` into result. (u,v) is the centre in
 * face uv; (uw1,vw1) and (uw2,vw2) are the two parallelogram axes; the final
 * footprint is axes*width + blur. Non-finite input returns TPTEX_E_INVALID_ARG
 * with result untouched; an out-of-range face is TPTEX_E_RANGE (result untouched,
 * as in upstream). */
tptex_status tptex_filter_eval(tptex_filter* filter, float* result, int firstchan, int nchannels,
                               int faceid, float u, float v, float uw1, float vw1, float uw2,
                               float vw2, float width, float blur);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_FILTER_H_ */
