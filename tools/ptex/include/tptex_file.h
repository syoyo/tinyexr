/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Optional filesystem input (the only part of tptex that uses stdio/POSIX I/O).
 * On POSIX the input uses pread(), so a NO_LAZY texture opened from it can be
 * read from several threads; elsewhere it falls back to stdio (single thread).
 */
#ifndef TPTEX_FILE_H_
#define TPTEX_FILE_H_

#include "tptex.h"

#ifdef __cplusplus
extern "C" {
#endif

/* An input that reads the file named by the path given to tptex_open(). */
void tptex_input_file(tptex_input* out);

/* Convenience: tptex_open() with tptex_input_file(). */
tptex_status tptex_open_file(const char* path, const tptex_options* options, tptex_texture** out);

#ifdef __cplusplus
}
#endif

#endif /* TPTEX_FILE_H_ */
