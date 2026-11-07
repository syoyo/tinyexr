/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Writer -> reader round trips (self-contained; the upstream differential lives
 * in compare/cmp_write.cc).
 */
#include <stdlib.h>
#include <string.h>

#include "../include/tptex.h"
#include <stdio.h>

#include "../include/tptex_file.h"
#include "../include/tptex_write.h"
#include "tptex_test.h"

static void fill_info(tptex_face_info* f, int ul, int vl) {
  memset(f, 0, sizeof *f);
  f->res = tptex_make_res(ul, vl);
  f->adjfaces[0] = f->adjfaces[1] = f->adjfaces[2] = f->adjfaces[3] = -1;
}

static void roundtrip(tptex_data_type dt, int nch, int alpha, int mips, int ulog2, int vlog2) {
  tptex_write_config cfg;
  tptex_writer* w = NULL;
  tptex_texture* t = NULL;
  tptex_face_info fi;
  size_t es = tptex_data_type_size(dt), npix = (size_t)1 << (ulog2 + vlog2), n = npix * (size_t)nch;
  unsigned char* px = (unsigned char*)malloc(n * es);
  unsigned char* back = (unsigned char*)malloc(n * es);
  void* file = NULL;
  size_t fsize = 0, i;
  for (i = 0; i < n * es; ++i) px[i] = (unsigned char)((i * 2654435761u) >> 13);
  if (dt == TPTEX_FLOAT) { /* keep floats finite */
    float* f = (float*)px;
    for (i = 0; i < n; ++i) f[i] = (float)(i % 251) / 251.0f;
  }
  if (dt == TPTEX_HALF) {
    unsigned short* h = (unsigned short*)px;
    for (i = 0; i < n; ++i) h[i] = (unsigned short)(0x3000u + (i % 0x700u));
  }
  tptex_write_config_init(&cfg);
  cfg.data_type = dt; cfg.num_channels = nch; cfg.alpha_channel = alpha; cfg.num_faces = 2; cfg.gen_mipmaps = mips;
  TPTEX_CHECK(tptex_writer_create(&cfg, &w) == TPTEX_OK);
  fill_info(&fi, ulog2, vlog2);
  TPTEX_CHECK(tptex_writer_write_face(w, 0, &fi, px, 0) == TPTEX_OK);
  /* face 1 left unwritten -> constant black */
  TPTEX_CHECK(tptex_writer_meta_string(w, "k", "v") == TPTEX_OK);
  TPTEX_CHECK(tptex_writer_finish_memory(w, &file, &fsize) == TPTEX_OK);
  { void* d2 = NULL; size_t s2 = 0; TPTEX_CHECK(tptex_writer_finish_memory(w, &d2, &s2) != TPTEX_OK && d2 == NULL); } /* spent */
  tptex_writer_destroy(w);

  TPTEX_CHECK(tptex_open_memory(file, fsize, NULL, &t) == TPTEX_OK);
  if (t) {
    TPTEX_CHECK(tptex_get_info(t)->num_faces == 2);
    TPTEX_CHECK(tptex_get_data(t, 0, tptex_make_res(ulog2, vlog2), back, 0) == TPTEX_OK);
    TPTEX_CHECK(memcmp(px, back, n * es) == 0);
    {
      tptex_face_info g;
      TPTEX_CHECK(tptex_get_face_info(t, 1, &g) == TPTEX_OK && tptex_face_is_constant(&g));
    }
    {
      int idx; tptex_meta_type mt; const void* d; int cnt;
      TPTEX_CHECK(tptex_meta_find(t, "k", &idx, &mt) == TPTEX_OK && mt == TPTEX_META_STRING);
      TPTEX_CHECK(tptex_meta_value(t, idx, &d, &cnt) == TPTEX_OK && cnt == 2 && ((const char*)d)[0] == 'v');
    }
    tptex_close(t);
  }
  /* NO_LAZY open and a real file round trip give the same pixels */
  {
    tptex_options opt;
    tptex_texture* t2 = NULL;
    const char* dir = getenv("TPTEX_TEST_TMPDIR");
    char path[512];
    FILE* fp;
    snprintf(path, sizeof path, "%s/tptex_test_roundtrip.ptx", dir ? dir : "build");
    tptex_options_init(&opt);
    opt.flags = TPTEX_OPEN_NO_LAZY;
    TPTEX_CHECK(tptex_open_memory(file, fsize, &opt, &t2) == TPTEX_OK);
    if (t2) {
      memset(back, 0, n * es);
      TPTEX_CHECK(tptex_get_data(t2, 0, tptex_make_res(ulog2, vlog2), back, 0) == TPTEX_OK);
      TPTEX_CHECK(memcmp(px, back, n * es) == 0);
      tptex_close(t2);
    }
    fp = fopen(path, "wb");
    if (fp) {
      fwrite(file, 1, fsize, fp);
      fclose(fp);
      t2 = NULL;
      TPTEX_CHECK(tptex_open_file(path, &opt, &t2) == TPTEX_OK);
      if (t2) {
        memset(back, 0, n * es);
        TPTEX_CHECK(tptex_get_data(t2, 0, tptex_make_res(ulog2, vlog2), back, 0) == TPTEX_OK);
        TPTEX_CHECK(memcmp(px, back, n * es) == 0);
        tptex_close(t2);
      }
      remove(path);
    }
    TPTEX_CHECK(tptex_open_file("/nonexistent-dir/does-not-exist.ptx", NULL, &t2) != TPTEX_OK);
  }
  tptex_free(NULL, file, fsize);
  free(px); free(back);
}

void test_write(void) {
  tptex_data_type dts[4] = {TPTEX_UINT8, TPTEX_UINT16, TPTEX_HALF, TPTEX_FLOAT};
  int d;
  for (d = 0; d < 4; ++d) {
    roundtrip(dts[d], 3, -1, 0, 3, 3);
    roundtrip(dts[d], 4, 3, 1, 5, 4);
    roundtrip(dts[d], 1, -1, 1, 8, 8); /* big enough to tile */
  }
  { /* argument validation */
    tptex_write_config cfg;
    tptex_writer* w = NULL;
    tptex_write_config_init(&cfg);
    cfg.num_channels = 0;
    TPTEX_CHECK(tptex_writer_create(&cfg, &w) == TPTEX_E_INVALID_ARG && w == NULL);
    cfg.num_channels = 3; cfg.num_faces = 1;
    TPTEX_CHECK(tptex_writer_create(&cfg, &w) == TPTEX_OK);
    {
      tptex_face_info fi; unsigned char px[3];
      memset(px, 0, sizeof px);
      fill_info(&fi, 0, 0);
      TPTEX_CHECK(tptex_writer_write_constant_face(w, 5, &fi, px) == TPTEX_E_RANGE);
      TPTEX_CHECK(tptex_writer_meta_string(w, "", "x") != TPTEX_OK);
    }
    tptex_writer_destroy(w);
  }
}
