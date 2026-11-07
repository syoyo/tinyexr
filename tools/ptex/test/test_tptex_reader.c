/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Reader error paths (no writer yet: positive reads are covered by the
 * upstream-written fixtures in compare/cmp_reader.cc).
 */
#include <string.h>

#include "../include/tptex.h"
#include "tptex_test.h"

void test_reader(void) {
  tptex_texture* t = (tptex_texture*)1;
  unsigned char junk[64];
  tptex_options opt;

  TPTEX_CHECK(tptex_open_memory(NULL, 0, NULL, &t) == TPTEX_E_BAD_MAGIC);
  TPTEX_CHECK(t == NULL);

  memset(junk, 0, sizeof junk);
  TPTEX_CHECK(tptex_open_memory(junk, sizeof junk, NULL, &t) == TPTEX_E_BAD_MAGIC);

  memcpy(junk, "Ptex", 4);
  junk[4] = 2; /* unsupported version */
  TPTEX_CHECK(tptex_open_memory(junk, sizeof junk, NULL, &t) == TPTEX_E_BAD_VERSION);

  junk[4] = 1; /* valid magic+version, truncated header */
  TPTEX_CHECK(tptex_open_memory(junk, 40, NULL, &t) != TPTEX_OK);
  TPTEX_CHECK(t == NULL);

  TPTEX_CHECK(tptex_open_memory(junk, sizeof junk, NULL, NULL) == TPTEX_E_INVALID_ARG);

  tptex_options_init(&opt);
  TPTEX_CHECK(opt.limits.max_faces > 0 && opt.limits.max_block_bytes > 0);
  tptex_close(NULL); /* no-op */
}
