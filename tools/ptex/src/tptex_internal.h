/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Private helpers shared by the tptex sources. Not part of the public API.
 */
#ifndef TPTEX_INTERNAL_H_
#define TPTEX_INTERNAL_H_

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "../include/tptex.h"

/* --- explicit little-endian byte access (never struct punning) ---------- */
static inline uint16_t tptex__ld_u16(const uint8_t* p) {
  return (uint16_t)((uint32_t)p[0] | ((uint32_t)p[1] << 8));
}
static inline uint32_t tptex__ld_u32(const uint8_t* p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
         ((uint32_t)p[3] << 24);
}
static inline uint64_t tptex__ld_u64(const uint8_t* p) {
  return (uint64_t)tptex__ld_u32(p) | ((uint64_t)tptex__ld_u32(p + 4) << 32);
}
static inline void tptex__st_u16(uint8_t* p, uint16_t v) {
  p[0] = (uint8_t)v;
  p[1] = (uint8_t)(v >> 8);
}
static inline void tptex__st_u32(uint8_t* p, uint32_t v) {
  p[0] = (uint8_t)v;
  p[1] = (uint8_t)(v >> 8);
  p[2] = (uint8_t)(v >> 16);
  p[3] = (uint8_t)(v >> 24);
}
static inline void tptex__st_u64(uint8_t* p, uint64_t v) {
  tptex__st_u32(p, (uint32_t)v);
  tptex__st_u32(p + 4, (uint32_t)(v >> 32));
}

/* --- overflow-checked 64-bit arithmetic: return 1 on success, 0 on overflow */
static inline int tptex__add_u64(uint64_t a, uint64_t b, uint64_t* out) {
  if (a > UINT64_MAX - b) return 0;
  *out = a + b;
  return 1;
}
static inline int tptex__mul_u64(uint64_t a, uint64_t b, uint64_t* out) {
  if (a != 0u && b > UINT64_MAX / a) return 0;
  *out = a * b;
  return 1;
}
/* Narrow to size_t only when it fits (matters on 32-bit targets). */
static inline int tptex__to_size(uint64_t v, size_t* out) {
  if (v > (uint64_t)SIZE_MAX) return 0;
  *out = (size_t)v;
  return 1;
}

/* --- allocator wrappers (NULL hooks mean the C library) ------------------ */
void* tptex__alloc(const tptex_allocator* a, size_t size);
void* tptex__calloc(const tptex_allocator* a, size_t size);
void* tptex__realloc(const tptex_allocator* a, void* ptr, size_t old_size, size_t new_size);
void tptex__free(const tptex_allocator* a, void* ptr, size_t size);

/* --- deflate backend (tptex_inflate.c) ------------------------------------ */
/* Inflate to exactly `dst_size` bytes; `ops` may be NULL for the built-in. */
tptex_status tptex__inflate(const tptex_zlib_ops* ops, const void* src, size_t src_size,
                            void* dst, size_t dst_size);
tptex_status tptex__deflate(const tptex_zlib_ops* ops, int level, const void* src,
                            size_t src_size, void* dst, size_t dst_capacity, size_t* out_size);

/* --- host byte order -------------------------------------------------------- */
static inline int tptex__host_is_big_endian(void) {
  const uint16_t probe = 0x0102u;
  uint8_t first;
  memcpy(&first, &probe, 1);
  return first == 0x01u;
}
/* Reverse each `elem_size`-byte element in place (file data is little-endian;
 * call this only on big-endian hosts). elem_size is 2, 4 or 8. */
static inline void tptex__swap_elems(void* buf, size_t nelems, size_t elem_size) {
  uint8_t* p = (uint8_t*)buf;
  size_t i, k;
  if (elem_size < 2u) return;
  for (i = 0; i < nelems; ++i, p += elem_size)
    for (k = 0; k < elem_size / 2u; ++k) {
      uint8_t t = p[k];
      p[k] = p[elem_size - 1u - k];
      p[elem_size - 1u - k] = t;
    }
}
/* File (little-endian) -> host order for `nbytes` of `es`-byte elements. */
static inline void tptex__le_to_host(void* buf, size_t nbytes, size_t es) {
  if (es > 1u && tptex__host_is_big_endian()) tptex__swap_elems(buf, nbytes / es, es);
}

#endif /* TPTEX_INTERNAL_H_ */
