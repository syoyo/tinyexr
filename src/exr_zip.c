/*
 * TinyEXR - ZIP/ZIPS codec glue (inflate + predictor + interleave).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr_internal.h"

/* Inflate into dst (the pre-reconstruction buffer); no predictor/interleave. */
exr_result exr_zip_inflate_only(const uint8_t *src, size_t src_size,
                                uint8_t *dst, size_t dst_size) {
    size_t out_size = 0;
    exr_result rc = exr_zlib_inflate(src, src_size, dst, dst_size, &out_size);
    if (EXR_OK(rc) && out_size != dst_size) rc = EXR_ERROR_CORRUPT;
    return rc;
}

exr_result exr_zip_decompress(const exr_allocator *a, const uint8_t *src,
                              size_t src_size, uint8_t *dst, size_t dst_size) {
    uint8_t *tmp;
    size_t tmp_size;
    exr_result rc;
    if (!a || !src || !dst) return EXR_ERROR_INVALID_ARGUMENT;
    if (!exr_allocator_valid((exr_allocator *)a)) return EXR_ERROR_INVALID_ARGUMENT;
    if (dst_size == 0) return EXR_ERROR_INVALID_ARGUMENT;
    if (exr_add_ovf(dst_size, 8, &tmp_size)) return EXR_ERROR_OUT_OF_MEMORY;
    tmp = (uint8_t *)exr_malloc(a, tmp_size ? tmp_size : 1);
    if (!tmp) return EXR_ERROR_OUT_OF_MEMORY;

    {
        size_t out_size = 0;
        rc = exr_zlib_inflate(src, src_size, tmp, tmp_size, &out_size);
        if (EXR_OK(rc) && out_size != dst_size) rc = EXR_ERROR_CORRUPT;
    }
    if (EXR_OK(rc)) {
        exr_predictor_decode(tmp, dst_size);
        exr_interleave_decode(tmp, dst, dst_size);
    }
    exr_free(a, tmp);
    return rc;
}

exr_result exr_zip_compress(const exr_allocator *a, const uint8_t *src, size_t n,
                            uint8_t **out_data, size_t *out_size) {
    uint8_t *tmp, *comp = NULL;
    size_t clen = 0;
    exr_result rc;
    *out_data = NULL;
    *out_size = 0;
    if (n == 0) {
        *out_data = (uint8_t *)exr_malloc(a, 1);
        if (!*out_data) return EXR_ERROR_OUT_OF_MEMORY;
        return EXR_SUCCESS;
    }
    tmp = (uint8_t *)exr_malloc(a, n);
    if (!tmp) return EXR_ERROR_OUT_OF_MEMORY;
    exr_interleave_encode(src, tmp, n);
    exr_predictor_encode(tmp, n);

    rc = exr_zlib_deflate(a, tmp, n, &comp, &clen);
    exr_free(a, tmp);

    if (!EXR_OK(rc) || clen >= n) { /* store original canonical block raw */
        exr_free(a, comp);
        *out_data = (uint8_t *)exr_malloc(a, n);
        if (!*out_data) return EXR_ERROR_OUT_OF_MEMORY;
        memcpy(*out_data, src, n);
        *out_size = n;
        return EXR_SUCCESS;
    }
    *out_data = comp;
    *out_size = clen;
    return EXR_SUCCESS;
}
