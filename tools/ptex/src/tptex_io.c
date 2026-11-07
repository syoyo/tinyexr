/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Memory input source and option defaults. No stdio, no allocation.
 */
#include "tptex_internal.h"

static tptex_status mem_open(void* user, const char* path, void** handle) {
  (void)path;
  if (!user || !handle) return TPTEX_E_INVALID_ARG;
  *handle = user;
  return TPTEX_OK;
}

static tptex_status mem_size(void* user, void* handle, uint64_t* out_size) {
  const tptex_memory_source* s = (const tptex_memory_source*)handle;
  (void)user;
  if (!s || !out_size) return TPTEX_E_INVALID_ARG;
  *out_size = (uint64_t)s->size;
  return TPTEX_OK;
}

static tptex_status mem_read_at(void* user, void* handle, uint64_t offset, void* dst, size_t n,
                                size_t* got) {
  const tptex_memory_source* s = (const tptex_memory_source*)handle;
  size_t avail = 0, take = 0;
  (void)user;
  if (!s || !got) return TPTEX_E_INVALID_ARG;
  if (offset < (uint64_t)s->size) avail = s->size - (size_t)offset;
  take = n < avail ? n : avail;
  if (take) memcpy(dst, (const uint8_t*)s->data + (size_t)offset, take);
  *got = take;
  return TPTEX_OK;
}

static void mem_close(void* user, void* handle) {
  (void)user;
  (void)handle;
}

tptex_status tptex_input_from_memory(tptex_input* out, const tptex_memory_source* source) {
  if (!out || !source || (!source->data && source->size)) return TPTEX_E_INVALID_ARG;
  out->user = (void*)source;
  out->open = mem_open;
  out->size = mem_size;
  out->read_at = mem_read_at;
  out->close = mem_close;
  return TPTEX_OK;
}

void tptex_options_init(tptex_options* o) {
  if (!o) return;
  memset(o, 0, sizeof *o);
  o->limits.max_faces = (uint64_t)1 << 26;           /* 67M faces */
  o->limits.max_block_bytes = (uint64_t)1 << 30;     /* 1 GiB per block */
  o->limits.max_meta_bytes = (uint64_t)1 << 30;      /* 1 GiB of metadata */
}
