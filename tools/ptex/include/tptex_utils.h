/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Pixel-buffer utilities ported from upstream PtexUtils. Buffers hold channel-
 * interleaved pixels of one tptex_data_type in HOST byte order; strides are in
 * bytes. These routines never assume alignment (all element access goes
 * through memcpy) and every float-to-integer conversion is defined: out-of-
 * range or NaN values wrap the way the upstream code behaves on x86 (the value
 * is truncated through a 32-bit integer, out-of-range yields 0).
 */
#ifndef TPTEX_UTILS_H_
#define TPTEX_UTILS_H_

#include <stddef.h>
#include <stdint.h>

#include "tptex.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Scale between the integer range and 1.0 (255, 65535, 1, 1) and its inverse. */
float tptex_one_value(tptex_data_type dt);
float tptex_one_value_inv(tptex_data_type dt);

/* 1 if every pixel equals the first. */
int tptex_is_constant(const void* data, size_t stride, int ures, int vres, int pixel_size);

/* Channel-planar <-> pixel-interleaved copies (element-wise, no arithmetic). */
void tptex_interleave(const void* src, size_t sstride, int ures, int vres, void* dst,
                      size_t dstride, tptex_data_type dt, int nchannels);
void tptex_deinterleave(const void* src, size_t sstride, int ures, int vres, void* dst,
                        size_t dstride, tptex_data_type dt, int nchannels);

/* In-place running-difference codec for 8/16-bit data (no-op for half/float).
 * `size` is in bytes. */
void tptex_encode_difference(void* data, size_t size, tptex_data_type dt);
void tptex_decode_difference(void* data, size_t size, tptex_data_type dt);

/* 2x2 box reduction to (ures/2 x vres/2); u-only (ures/2 x vres); v-only
 * (ures x vres/2); and the packed-triangle reduction (ures == vres == w). */
void tptex_reduce(const void* src, size_t sstride, int ures, int vres, void* dst,
                  size_t dstride, tptex_data_type dt, int nchannels);
void tptex_reduce_u(const void* src, size_t sstride, int ures, int vres, void* dst,
                    size_t dstride, tptex_data_type dt, int nchannels);
void tptex_reduce_v(const void* src, size_t sstride, int ures, int vres, void* dst,
                    size_t dstride, tptex_data_type dt, int nchannels);
void tptex_reduce_tri(const void* src, size_t sstride, int w, void* dst, size_t dstride,
                      tptex_data_type dt, int nchannels);

/* Per-channel mean of an ures x vres block into dst[nchannels]. */
void tptex_average(const void* src, size_t sstride, int ures, int vres, void* dst,
                   tptex_data_type dt, int nchannels);

void tptex_fill(const void* pixel, void* dst, size_t dstride, int ures, int vres, int pixel_size);
void tptex_copy(const void* src, size_t sstride, void* dst, size_t dstride, int nrows,
                size_t rowlen);

/* dst += weight * src over `rowlen` pixels; `flip` walks dst backwards. */
void tptex_blend(const void* src, float weight, void* dst, int flip, int rowlen,
                 tptex_data_type dt, int nchannels);

/* Premultiply / un-premultiply by the alpha channel. */
void tptex_multalpha(void* data, int npixels, tptex_data_type dt, int nchannels, int alphachan);
void tptex_divalpha(void* data, int npixels, tptex_data_type dt, int nchannels, int alphachan);

/* Reduction-face ordering: stable sort of face ids by min(ures,vres) log2
 * descending (constant faces count as 1). rfaceids[face] = rank; faceids[rank]
 * = face. Both arrays hold nfaces entries. */
void tptex_gen_rfaceids(const tptex_face_info* faces, uint32_t nfaces, uint32_t* rfaceids,
                        uint32_t* faceids);

/* dst[i] += data[i] * weight (raw element value, not normalised). */
void tptex_apply_const(float weight, float* dst, const void* data, tptex_data_type dt, int nchannels);

/* Normalising conversions (u8/u16 map 0..max to 0..1). */
void tptex_convert_to_float(float* dst, const void* src, tptex_data_type dt, int nchannels);
void tptex_convert_from_float(void* dst, const float* src, tptex_data_type dt, int nchannels);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_UTILS_H_ */
