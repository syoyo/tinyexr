/* SPDX-License-Identifier: Apache 2.0 */
/* Copyright 2023 - Present, Light Transport Entertainment Inc. */

/* TODO:
 *
 * - [ ] Stream decoding API
 * - [ ] Encoding API
 *   - [ ] Stream encoding API
 *
 */

#ifndef NANOZDEC_H_
#define NANOZDEC_H_

#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum nanoz_status {
  NANOZ_SUCCESS = 0,
  NANOZ_ERROR = -1,  // general error code.
  NANOZ_ERROR_INVALID_ARGUMENT = -2,
  NANOZ_ERROR_CORRUPTED = -3,
  NANOZ_ERROR_INTERNAL = -4,
} nanoz_status_t;

#if 0 // TODO
/* Up to 4GB chunk. */
typedef (*nanoz_stream_read)(const uint8_t *addr, uint8_t *dst_addr, const uint32_t read_bytes, const void *user_ptr);
typedef (*nanoz_stream_write)(const uint8_t *addr, const uint32_t write_bytes, const void *user_ptr);
#endif

/*
 * @param[in] src_addr Source buffer address containing compressed data.
 * @param[in] src_size Source buffer bytes.
 * @param[in] uncompressed_size Bytes after uncompress.
 * @param[out] dst_addr Destination buffer address. Must have enough memory to
 * contain `uncompressed_size` bytes.
 * @return NANOZ_SUCCESS upon success.
 *
 * TODO: return error message string.
 */
nanoz_status_t nanoz_uncompress(const unsigned char *src_addr,
                                const uint64_t src_size,
                                const uint64_t uncompressed_size,
                                unsigned char *dst_addr);


#if 0 // TODO
nanoz_status_t nanoz_stream_uncompress(nanoz_stream_read *reader, nanoz_stream_writer *writer);
#endif

#ifdef __cplusplus
}
#endif

#if defined(NANOZDEC_IMPLEMENTATION)

#define WUFFS_IMPLEMENTATION

#define WUFFS_CONFIG__STATIC_FUNCTIONS

#define WUFFS_CONFIG__MODULES
#define WUFFS_CONFIG__MODULE__BASE
#define WUFFS_CONFIG__MODULE__CRC32
#define WUFFS_CONFIG__MODULE__ADLER32
#define WUFFS_CONFIG__MODULE__DEFLATE
#define WUFFS_CONFIG__MODULE__ZLIB

#include "wuffs-v0.3-zlib.c"

#define WORK_BUFFER_ARRAY_SIZE \
  WUFFS_ZLIB__DECODER_WORKBUF_LEN_MAX_INCL_WORST_CASE

nanoz_status_t nanoz_uncompress(const unsigned char *src_addr,
                                const uint64_t src_size,
                                const uint64_t uncompressed_size,
                                unsigned char *dst_addr) {
// WUFFS_ZLIB__DECODER_WORKBUF_LEN_MAX_INCL_WORST_CASE = 1, its tiny bytes and
// safe to alloc worbuf at heap location.
#if WORK_BUFFER_ARRAY_SIZE > 0
  uint8_t work_buffer_array[WORK_BUFFER_ARRAY_SIZE];
#else
  // Not all C/C++ compilers support 0-length arrays.
  uint8_t work_buffer_array[1];
#endif

  if (!src_addr) {
    return NANOZ_ERROR_INVALID_ARGUMENT;
  }

  if (src_size < 4) {
    return NANOZ_ERROR_INVALID_ARGUMENT;
  }

  if (!dst_addr) {
    return NANOZ_ERROR_INVALID_ARGUMENT;
  }

  if (uncompressed_size < 1) {
    return NANOZ_ERROR_INVALID_ARGUMENT;
  }

  wuffs_zlib__decoder dec;
  wuffs_base__status status =
      wuffs_zlib__decoder__initialize(&dec, sizeof dec, WUFFS_VERSION, 0);
  if (!wuffs_base__status__is_ok(&status)) {
    // wuffs_base__status__message(&status);
    return NANOZ_ERROR_INTERNAL;
  }

  // TODO: Streamed decoding?

  wuffs_base__io_buffer dst;
  dst.data.ptr = dst_addr;
  dst.data.len = uncompressed_size;
  dst.meta.wi = 0;
  dst.meta.ri = 0;
  dst.meta.pos = 0;
  dst.meta.closed = false;

  wuffs_base__io_buffer src;
  src.data.ptr = const_cast<uint8_t *>(src_addr);  // remove const
  src.data.len = src_size;
  src.meta.wi = src_size;
  src.meta.ri = 0;
  src.meta.pos = 0;
  src.meta.closed = false;

  status = wuffs_zlib__decoder__transform_io(
      &dec, &dst, &src,
      wuffs_base__make_slice_u8(work_buffer_array, WORK_BUFFER_ARRAY_SIZE));

  if (dst.meta.wi) {
    dst.meta.ri = dst.meta.wi;
    wuffs_base__io_buffer__compact(&dst);
  }

  if (status.repr == wuffs_base__suspension__short_read) {
    // ok
  } else if (status.repr == wuffs_base__suspension__short_write) {
    // read&write should succeed at once.
    return NANOZ_ERROR_CORRUPTED;
  }

  const char *stat_msg = wuffs_base__status__message(&status);
  if (stat_msg) {
    return NANOZ_ERROR_INTERNAL;
  }

  return NANOZ_SUCCESS;
}
#endif  // NANOZDEC_IMPLEMENTATION

#endif /* NANOZDEC_H_ */
