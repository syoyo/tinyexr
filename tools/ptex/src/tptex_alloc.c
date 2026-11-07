/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Allocator plumbing. This is the only core file that touches <stdlib.h>, and
 * defining TPTEX_NO_LIBC_ALLOC removes that dependency: a NULL allocator is
 * then an error (allocation returns NULL), which the freestanding gate uses.
 */
#include "tptex_internal.h"

#ifndef TPTEX_NO_LIBC_ALLOC
#include <stdlib.h>
#endif

void* tptex__alloc(const tptex_allocator* a, size_t size) {
  if (size == 0u) size = 1u;
  if (a && a->alloc) return a->alloc(a->ctx, size);
#ifndef TPTEX_NO_LIBC_ALLOC
  return malloc(size);
#else
  return NULL;
#endif
}

void* tptex__calloc(const tptex_allocator* a, size_t size) {
  void* p = tptex__alloc(a, size);
  if (p) memset(p, 0, size == 0u ? 1u : size);
  return p;
}

void* tptex__realloc(const tptex_allocator* a, void* ptr, size_t old_size, size_t new_size) {
  if (!ptr) return tptex__alloc(a, new_size);
  if (a && a->realloc) return a->realloc(a->ctx, ptr, old_size, new_size);
  if (a && a->alloc) { /* alloc/free pair without realloc: copy */
    void* np = a->alloc(a->ctx, new_size == 0u ? 1u : new_size);
    if (!np) return NULL;
    memcpy(np, ptr, old_size < new_size ? old_size : new_size);
    if (a->free) a->free(a->ctx, ptr, old_size);
    return np;
  }
#ifndef TPTEX_NO_LIBC_ALLOC
  return realloc(ptr, new_size == 0u ? 1u : new_size);
#else
  return NULL;
#endif
}

void tptex__free(const tptex_allocator* a, void* ptr, size_t size) {
  if (!ptr) return;
  if (a && a->free) {
    a->free(a->ctx, ptr, size);
    return;
  }
  if (a && a->alloc) return; /* custom allocator without free: arena semantics */
#ifndef TPTEX_NO_LIBC_ALLOC
  free(ptr);
#endif
}
