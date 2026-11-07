/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Shared state of the quad (separable) and triangle filters.
 */
#ifndef TPTEX_FILTER_INTERNAL_H_
#define TPTEX_FILTER_INTERNAL_H_

#include "../include/tptex_filter.h"
#include "tptex_internal.h"

#define TPTEX_FILTER_MAX_DEPTH 64

struct tptex_filter {
  tptex_allocator alloc;
  tptex_texture* tx;
  tptex_filter_options opt;
  const tptex_info* info;
  int ntxchan;
  tptex_data_type dt;
  size_t dtsize, pixsize;
  tptex_border_mode umode, vmode;
  tptex_edge_filter_mode efm;
  float coeffs[7]; /* bicubic */

  /* per-eval state */
  float* result;   /* ntxchan floats, accumulated */
  float* tmp;      /* ntxchan floats, tangent-vector temp */
  float* row;      /* ntxchan floats, row accumulator */
  uint8_t* pix;    /* one pixel of constant data */
  float weight;
  int firstchan, nchan;
  size_t firstoff; /* byte offset of first channel */
  tptex_status err;
  int depth;
};

/* helpers shared by both filters */
float tptex__fl_floor(float x);
float tptex__fl_ceil(float x);
int tptex__fl_to_int(float x);
int tptex__fl_calc_res_from_width(float w);
float tptex__fl_reciprocal_pow2(int power);
float tptex__fl_rd(const uint8_t* p, tptex_data_type dt);
int tptex__fl_adj_ok(const tptex_filter* f, int faceid);

/* triangle filter entry (tptex_trifilter.c) */
void tptex__tri_eval(tptex_filter* f, int faceid, float u, float v, float uw1, float vw1,
                     float uw2, float vw2, float width, float blur);

#endif /* TPTEX_FILTER_INTERNAL_H_ */
