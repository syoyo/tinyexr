/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Deflate backend shim. By default the vendored miniz is used; define
 * TPTEX_ZLIB_HOOK to drop that dependency and require tptex_options.zlib.
 */
#include <limits.h>

#include "tptex_internal.h"

#ifndef TPTEX_ZLIB_HOOK
#define MINIZ_NO_ZLIB_COMPATIBLE_NAMES
/* Override with -DTPTEX_MINIZ_HEADER="path/to/miniz.h" when it is not on the include path. */
#ifndef TPTEX_MINIZ_HEADER
#define TPTEX_MINIZ_HEADER "miniz.h"
#endif
#include TPTEX_MINIZ_HEADER
#endif

tptex_status tptex__inflate(const tptex_zlib_ops* ops, const void* src, size_t src_size,
                            void* dst, size_t dst_size) {
  if (ops && ops->inflate) return ops->inflate(ops->ctx, src, src_size, dst, dst_size);
#ifdef TPTEX_ZLIB_HOOK
  (void)src; (void)src_size; (void)dst; (void)dst_size;
  return TPTEX_E_UNSUPPORTED;
#else
  {
    mz_ulong n;
    unsigned char dummy = 0;
#if SIZE_MAX > ULONG_MAX
    if (dst_size > (size_t)ULONG_MAX || src_size > (size_t)ULONG_MAX) return TPTEX_E_LIMIT;
#endif
    n = (mz_ulong)dst_size;
    if (mz_uncompress(dst_size ? (unsigned char*)dst : &dummy, &n, (const unsigned char*)src,
                      (mz_ulong)src_size) != MZ_OK ||
        n != (mz_ulong)dst_size)
      return TPTEX_E_INFLATE;
    return TPTEX_OK;
  }
#endif
}

tptex_status tptex__deflate(const tptex_zlib_ops* ops, int level, const void* src,
                            size_t src_size, void* dst, size_t dst_capacity, size_t* out_size) {
  if (ops && ops->deflate) return ops->deflate(ops->ctx, level, src, src_size, dst, dst_capacity, out_size);
#ifdef TPTEX_ZLIB_HOOK
  (void)level; (void)src; (void)src_size; (void)dst; (void)dst_capacity; (void)out_size;
  return TPTEX_E_UNSUPPORTED;
#else
  {
    mz_ulong n;
#if SIZE_MAX > ULONG_MAX
    if (dst_capacity > (size_t)ULONG_MAX || src_size > (size_t)ULONG_MAX) return TPTEX_E_LIMIT;
#endif
    n = (mz_ulong)dst_capacity;
    if (mz_compress2((unsigned char*)dst, &n, (const unsigned char*)src, (mz_ulong)src_size, level) != MZ_OK)
      return TPTEX_E_LIMIT;
    *out_size = (size_t)n;
    return TPTEX_OK;
  }
#endif
}
