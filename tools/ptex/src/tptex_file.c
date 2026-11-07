/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Filesystem input for tptex. Excluded from the freestanding/no-fileio build.
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif

#include "../include/tptex_file.h"

#include <stdio.h>
#include <stdlib.h>

#if !defined(_WIN32) && (defined(__unix__) || defined(__APPLE__))
#define TPTEX_POSIX_IO 1
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

typedef struct file_handle {
#ifdef TPTEX_POSIX_IO
  int fd;
#else
  FILE* fp;
#endif
  uint64_t size;
} file_handle;

static tptex_status f_open(void* user, const char* path, void** handle) {
  file_handle* h;
  (void)user;
  if (!path || !handle) return TPTEX_E_INVALID_ARG;
  h = (file_handle*)malloc(sizeof *h);
  if (!h) return TPTEX_E_NOMEM;
#ifdef TPTEX_POSIX_IO
  {
    struct stat st;
    h->fd = open(path, O_RDONLY);
    if (h->fd < 0) { free(h); return TPTEX_E_IO; }
    if (fstat(h->fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(h->fd); free(h); return TPTEX_E_IO; }
    h->size = (uint64_t)st.st_size;
  }
#else
  {
    long long n;
    h->fp = fopen(path, "rb");
    if (!h->fp) { free(h); return TPTEX_E_IO; }
#if defined(_MSC_VER)
    if (_fseeki64(h->fp, 0, SEEK_END) != 0 || (n = _ftelli64(h->fp)) < 0) { fclose(h->fp); free(h); return TPTEX_E_IO; }
#else
    if (fseek(h->fp, 0, SEEK_END) != 0 || (n = (long long)ftell(h->fp)) < 0) { fclose(h->fp); free(h); return TPTEX_E_IO; }
#endif
    h->size = (uint64_t)n;
  }
#endif
  *handle = h;
  return TPTEX_OK;
}

static tptex_status f_size(void* user, void* handle, uint64_t* out) {
  (void)user;
  *out = ((file_handle*)handle)->size;
  return TPTEX_OK;
}

static tptex_status f_read_at(void* user, void* handle, uint64_t offset, void* dst, size_t n, size_t* got) {
  file_handle* h = (file_handle*)handle;
  size_t total = 0;
  (void)user;
#ifdef TPTEX_POSIX_IO
  while (total < n) {
    ssize_t r = pread(h->fd, (char*)dst + total, n - total, (off_t)(offset + total));
    if (r < 0) return TPTEX_E_IO;
    if (r == 0) break;
    total += (size_t)r;
  }
#else
#if defined(_MSC_VER)
  if (_fseeki64(h->fp, (__int64)offset, SEEK_SET) != 0) return TPTEX_E_IO;
#else
  if (fseek(h->fp, (long)offset, SEEK_SET) != 0) return TPTEX_E_IO;
#endif
  total = fread(dst, 1, n, h->fp);
#endif
  *got = total;
  return TPTEX_OK;
}

static void f_close(void* user, void* handle) {
  file_handle* h = (file_handle*)handle;
  (void)user;
  if (!h) return;
#ifdef TPTEX_POSIX_IO
  close(h->fd);
#else
  fclose(h->fp);
#endif
  free(h);
}

void tptex_input_file(tptex_input* out) {
  if (!out) return;
  out->user = NULL;
  out->open = f_open;
  out->size = f_size;
  out->read_at = f_read_at;
  out->close = f_close;
}

tptex_status tptex_open_file(const char* path, const tptex_options* options, tptex_texture** out) {
  tptex_input in;
  tptex_input_file(&in);
  return tptex_open(&in, path, options, out);
}
