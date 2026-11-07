/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * tptex writer: the equivalent of PtexMainWriter (write a texture from scratch,
 * optionally generating mip reductions). The whole file is assembled in memory
 * and delivered to a sink (or returned as a buffer), so no temp files, seeks or
 * stdio are needed. Face pixels are interleaved, host byte order. Compressed
 * bytes differ from upstream's zlib output; decoded content is identical.
 *
 * Deliberate differences from upstream: a file is always produced (faces never
 * written are constant black), and the 8-byte compatibility barrier is written
 * even when there is no metadata (so edit blocks appended later are located).
 */
#ifndef TPTEX_WRITE_H_
#define TPTEX_WRITE_H_

#include "tptex.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tptex_writer tptex_writer;

typedef struct tptex_write_config {
  tptex_allocator allocator; /* zeroed = malloc/free */
  const tptex_zlib_ops* zlib; /* NULL = built-in */
  tptex_mesh_type mesh_type;
  tptex_data_type data_type;
  int num_channels;
  int alpha_channel; /* -1 for none; alpha colours are premultiplied for reductions */
  int num_faces;
  int gen_mipmaps;
  int compression_level; /* 0 = store, 1..9, -1 = default */
  uint64_t max_block_bytes; /* 0 = 1 GiB */
} tptex_write_config;

typedef struct tptex_sink {
  void* user;
  tptex_status (*write)(void* user, const void* data, size_t size);
} tptex_sink;

void tptex_write_config_init(tptex_write_config* config);
tptex_status tptex_writer_create(const tptex_write_config* config, tptex_writer** out);
void tptex_writer_destroy(tptex_writer* writer); /* NULL is a no-op */

tptex_status tptex_writer_set_border_modes(tptex_writer* w, tptex_border_mode u, tptex_border_mode v);
tptex_status tptex_writer_set_edge_filter_mode(tptex_writer* w, tptex_edge_filter_mode mode);

/* Metadata. Keys are limited to 255 bytes; re-using a key replaces its value.
 * `count` is the number of elements (numeric types). */
tptex_status tptex_writer_meta_string(tptex_writer* w, const char* key, const char* value);
tptex_status tptex_writer_meta(tptex_writer* w, const char* key, tptex_meta_type type,
                               const void* data, int count);

/* Write a face (stride 0 = tight rows). A constant face is stored as such. */
tptex_status tptex_writer_write_face(tptex_writer* w, int faceid, const tptex_face_info* info,
                                     const void* data, size_t stride);
tptex_status tptex_writer_write_constant_face(tptex_writer* w, int faceid,
                                              const tptex_face_info* info, const void* pixel);

/* Finish: deliver the file once; the writer is then spent. */
tptex_status tptex_writer_finish(tptex_writer* w, const tptex_sink* sink);
/* Returns a buffer owned by the caller: free with tptex_free(allocator, data, size). */
tptex_status tptex_writer_finish_memory(tptex_writer* w, void** data, size_t* size);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_WRITE_H_ */
