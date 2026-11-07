/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * tptex: a pure-C11, portability-first port of the Ptex texture library.
 *
 * Design rules (see README.md):
 *  - C11 only; no atomics, volatile, threads or alloca. The core needs only
 *    <stdint.h>, <stddef.h> and <string.h>; <math.h> is used in the filter
 *    units alone and <stdio.h> only in the optional tptex_file.c.
 *  - Every size read from a file is overflow-checked before use; multi-byte
 *    fields are loaded with explicit little-endian byte loads.
 *  - Memory comes from a caller-supplied allocator (NULL means malloc/free).
 *  - Errors are returned as tptex_status; nothing is printed.
 */
#ifndef TPTEX_H_
#define TPTEX_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TPTEX_VERSION_MAJOR 0
#define TPTEX_VERSION_MINOR 1

/* Upstream Ptex release this port tracks (data format + algorithms). */
#define TPTEX_UPSTREAM_TAG "v2.4.3"
#define TPTEX_UPSTREAM_COMMIT "4aa2c35f9f25f025014fbbbf41cef669881b4172"

typedef enum tptex_status {
  TPTEX_OK = 0,
  TPTEX_E_INVALID_ARG = -1,
  TPTEX_E_NOMEM = -2,
  TPTEX_E_IO = -3,
  TPTEX_E_BAD_MAGIC = -4,
  TPTEX_E_BAD_VERSION = -5,
  TPTEX_E_CORRUPT = -6,
  TPTEX_E_OVERFLOW = -7,
  TPTEX_E_INFLATE = -8,
  TPTEX_E_RANGE = -9,
  TPTEX_E_UNSUPPORTED = -10,
  TPTEX_E_NOT_FOUND = -11,
  TPTEX_E_LIMIT = -12
} tptex_status;

/* Static, never-NULL description of a status code. */
const char* tptex_status_str(tptex_status status);

/* NULL alloc/free/realloc means malloc/free/realloc. `free` and `realloc`
 * receive the block's size so size-tracking allocators need no header. */
typedef struct tptex_allocator {
  void* (*alloc)(void* ctx, size_t size);                       /* NULL on failure */
  void* (*realloc)(void* ctx, void* ptr, size_t old_size, size_t new_size);
  void (*free)(void* ctx, void* ptr, size_t size);              /* ptr may be NULL */
  void* ctx;
} tptex_allocator;

/* Mirrors Ptex::MeshType / DataType / BorderMode / EdgeFilterMode. */
typedef enum tptex_mesh_type { TPTEX_MESH_TRIANGLE = 0, TPTEX_MESH_QUAD = 1 } tptex_mesh_type;
typedef enum tptex_data_type {
  TPTEX_UINT8 = 0,
  TPTEX_UINT16 = 1,
  TPTEX_HALF = 2,
  TPTEX_FLOAT = 3
} tptex_data_type;
typedef enum tptex_border_mode {
  TPTEX_BORDER_CLAMP = 0,
  TPTEX_BORDER_BLACK = 1,
  TPTEX_BORDER_PERIODIC = 2
} tptex_border_mode;
typedef enum tptex_edge_filter_mode {
  TPTEX_EDGE_FILTER_NONE = 0,
  TPTEX_EDGE_FILTER_TANGENT = 1
} tptex_edge_filter_mode;

/* Release memory obtained from tptex (e.g. tptex_writer_finish_memory) with the
 * allocator that produced it (NULL = the C library). */
void tptex_free(const tptex_allocator* allocator, void* ptr, size_t size);

/* Bytes per channel value of a data type; 0 for an invalid value. */
size_t tptex_data_type_size(tptex_data_type type);

/* Edge ids, CCW from the bottom edge (Ptex::EdgeId). */
typedef enum tptex_edge_id {
  TPTEX_EDGE_BOTTOM = 0,
  TPTEX_EDGE_RIGHT = 1,
  TPTEX_EDGE_TOP = 2,
  TPTEX_EDGE_LEFT = 3
} tptex_edge_id;

/* Face resolution in log2 texels (Ptex::Res). Negative values are reserved. */
typedef struct tptex_res {
  int8_t ulog2;
  int8_t vlog2;
} tptex_res;

static inline tptex_res tptex_make_res(int ulog2, int vlog2) {
  tptex_res r;
  r.ulog2 = (int8_t)ulog2;
  r.vlog2 = (int8_t)vlog2;
  return r;
}
static inline int tptex_res_equal(tptex_res a, tptex_res b) {
  return a.ulog2 == b.ulog2 && a.vlog2 == b.vlog2;
}

/* Face flags (Ptex::FaceInfo::flag_*). */
#define TPTEX_FACE_CONSTANT 1u
#define TPTEX_FACE_HASEDITS 2u
#define TPTEX_FACE_NBCONSTANT 4u
#define TPTEX_FACE_SUBFACE 8u

/* Ptex::FaceInfo. adjfaces are -1 when a neighbour is absent; adjedges packs
 * the neighbour's edge id for each of this face's edges, 2 bits per edge. */
typedef struct tptex_face_info {
  tptex_res res;
  uint8_t adjedges;
  uint8_t flags;
  int32_t adjfaces[4];
} tptex_face_info;

static inline tptex_edge_id tptex_face_adjedge(const tptex_face_info* f, int eid) {
  return (tptex_edge_id)((f->adjedges >> (2 * eid)) & 3);
}
static inline int tptex_face_is_constant(const tptex_face_info* f) {
  return (f->flags & TPTEX_FACE_CONSTANT) != 0u;
}
static inline int tptex_face_is_subface(const tptex_face_info* f) {
  return (f->flags & TPTEX_FACE_SUBFACE) != 0u;
}

/* ------------------------------------------------------------------------- *
 * Input
 * ------------------------------------------------------------------------- */

/* Random-access byte source (replaces PtexInputHandler's seek+read with a
 * stateless pread-style call, so a handle carries no hidden position). `path`
 * of open() may be NULL for a fixed source. `size` is optional; when absent
 * the file size is unknown and bounds are enforced by short reads. */
typedef struct tptex_input {
  void* user;
  tptex_status (*open)(void* user, const char* path, void** handle);
  tptex_status (*size)(void* user, void* handle, uint64_t* out_size);
  tptex_status (*read_at)(void* user, void* handle, uint64_t offset, void* dst, size_t n,
                          size_t* got);
  void (*close)(void* user, void* handle);
} tptex_input;

/* A fixed memory block. Both the block and this record must outlive any texture
 * opened from it (tptex_open_memory manages this for you). */
typedef struct tptex_memory_source {
  const void* data;
  size_t size;
} tptex_memory_source;

/* Input that serves `source` (stateless: the handle is the source pointer). */
tptex_status tptex_input_from_memory(tptex_input* out, const tptex_memory_source* source);

/* Deflate backend. The default (unless TPTEX_ZLIB_HOOK is defined) is the
 * vendored miniz. inflate must produce exactly dst_size bytes or fail. */
typedef struct tptex_zlib_ops {
  tptex_status (*inflate)(void* ctx, const void* src, size_t src_size, void* dst,
                          size_t dst_size);
  tptex_status (*deflate)(void* ctx, int level, const void* src, size_t src_size, void* dst,
                          size_t dst_capacity, size_t* out_size);
  void* ctx;
} tptex_zlib_ops;

/* Hostile-input caps. Zero fields take the defaults of tptex_options_init(). */
typedef struct tptex_limits {
  uint64_t max_faces;       /* faces in a texture */
  uint64_t max_block_bytes; /* any single compressed or decoded block */
  uint64_t max_meta_bytes;  /* total metadata bytes held in memory */
} tptex_limits;

#define TPTEX_OPEN_PREMULTIPLY 1u /* multiply colour by alpha when reading level 0 */
#define TPTEX_OPEN_NO_EDITS 2u    /* ignore edit blocks */

typedef struct tptex_options {
  tptex_allocator allocator;
  const tptex_zlib_ops* zlib; /* NULL = built-in default */
  tptex_limits limits;
  uint32_t flags;
} tptex_options;

/* Fill with defaults (malloc/free, built-in zlib, generous limits, no flags). */
void tptex_options_init(tptex_options* options);

/* ------------------------------------------------------------------------- *
 * Texture
 * ------------------------------------------------------------------------- */

typedef struct tptex_info {
  tptex_mesh_type mesh_type;
  tptex_data_type data_type;
  int32_t alpha_channel; /* -1 when absent */
  int32_t num_channels;
  int32_t num_faces;
  int32_t num_levels;
  tptex_border_mode u_border_mode;
  tptex_border_mode v_border_mode;
  tptex_edge_filter_mode edge_filter_mode;
  int has_edits;
  int has_mipmaps; /* more than one level stored */
} tptex_info;

typedef struct tptex_texture tptex_texture;

/* Open through an input (path passed to input->open). On failure *out is NULL. */
tptex_status tptex_open(const tptex_input* input, const char* path, const tptex_options* options,
                        tptex_texture** out);
tptex_status tptex_open_memory(const void* data, size_t size, const tptex_options* options,
                               tptex_texture** out);
void tptex_close(tptex_texture* texture); /* NULL is a no-op */

const tptex_info* tptex_get_info(const tptex_texture* texture);
tptex_status tptex_get_face_info(const tptex_texture* texture, int faceid, tptex_face_info* out);

/* Bytes of one pixel (channels * data type size). */
size_t tptex_pixel_size(const tptex_texture* texture);

/* Decode a face at resolution `res` into `buffer` (stride in bytes; 0 means a
 * tight row). Resolutions below the stored one are produced from the file's
 * reduction levels or generated on the fly exactly as upstream does; a face
 * that cannot be produced fills the buffer with zeros and returns the error
 * (upstream fills the same zero "error pixel" silently). The buffer must hold
 * stride * (1 << res.vlog2) bytes. */
tptex_status tptex_get_data(tptex_texture* texture, int faceid, tptex_res res, void* buffer,
                            size_t stride);

/* The stored average pixel of a face (one pixel, pixel_size bytes). */
tptex_status tptex_get_constant(tptex_texture* texture, int faceid, void* pixel);

/* One pixel converted to float: `nchannels` values starting at `firstchan`,
 * missing channels are zero. u,v are texel coordinates at `res` (the stored
 * resolution of the face for tptex_get_pixel). */
tptex_status tptex_get_pixel(tptex_texture* texture, int faceid, int u, int v, float* result,
                             int firstchan, int nchannels);
tptex_status tptex_get_pixel_res(tptex_texture* texture, int faceid, int u, int v, float* result,
                                 int firstchan, int nchannels, tptex_res res);

/* ------------------------------------------------------------------------- *
 * Metadata (borrowed from the texture; valid until it is closed)
 * ------------------------------------------------------------------------- */

typedef enum tptex_meta_type {
  TPTEX_META_STRING = 0,
  TPTEX_META_INT8 = 1,
  TPTEX_META_INT16 = 2,
  TPTEX_META_INT32 = 3,
  TPTEX_META_FLOAT = 4,
  TPTEX_META_DOUBLE = 5
} tptex_meta_type;

/* Number of keys (entries keep first-seen order; later definitions of a key,
 * such as metadata edits, replace the value in place). Loads metadata lazily. */
tptex_status tptex_meta_count(tptex_texture* texture, int* count);
/* Key and type of entry `index` (key is NUL-terminated). */
tptex_status tptex_meta_key(tptex_texture* texture, int index, const char** key,
                            tptex_meta_type* type);
tptex_status tptex_meta_find(tptex_texture* texture, const char* key, int* index,
                             tptex_meta_type* type);
/* Value of entry `index`: `data` points at host-order elements; for strings
 * count is the byte length including the terminating NUL. Large metadata is
 * read from the file on first access. */
tptex_status tptex_meta_value(tptex_texture* texture, int index, const void** data, int* count);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_H_ */
