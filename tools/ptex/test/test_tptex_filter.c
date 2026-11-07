/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * Filter sanity and hostile-mesh robustness (the upstream differential lives in
 * compare/cmp_filter.cc).
 */
#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "../include/tptex_filter.h"
#include "../include/tptex_write.h"
#include "tptex_test.h"

static uint32_t g_s = 0x9e3779b9u;
static uint32_t rnd(void) { g_s ^= g_s << 13; g_s ^= g_s >> 17; g_s ^= g_s << 5; return g_s; }
static float frand(void) { return (float)(rnd() >> 8) * (1.0f / 16777216.0f); }

/* build a texture of n faces; chaos != 0 scrambles adjacency (incl. out of range) */
static void* build(int mesh, int n, int chaos, size_t* size) {
  tptex_write_config cfg;
  tptex_writer* w = NULL;
  void* file = NULL;
  int f, i;
  unsigned char* px = (unsigned char*)malloc((size_t)3 << 12);
  tptex_write_config_init(&cfg);
  cfg.mesh_type = mesh ? TPTEX_MESH_QUAD : TPTEX_MESH_TRIANGLE;
  cfg.data_type = TPTEX_UINT8;
  cfg.num_channels = 3;
  cfg.num_faces = n;
  cfg.gen_mipmaps = 1;
  if (tptex_writer_create(&cfg, &w) != TPTEX_OK) { free(px); return NULL; }
  for (f = 0; f < n; ++f) {
    tptex_face_info fi;
    int ul = 1 + (int)(rnd() % 5), vl = mesh ? 1 + (int)(rnd() % 5) : ul;
    memset(&fi, 0, sizeof fi);
    fi.res = tptex_make_res(ul, vl);
    for (i = 0; i < 4; ++i) fi.adjfaces[i] = chaos ? (int)(rnd() % (unsigned)(n + 6)) - 2 : -1;
    fi.adjedges = (uint8_t)(chaos ? rnd() : 0);
    if (chaos && (rnd() & 3) == 0) fi.flags = TPTEX_FACE_SUBFACE;
    for (i = 0; i < (3 << (ul + vl)); ++i) px[i] = (unsigned char)(rnd() >> 7);
    if (tptex_writer_write_face(w, f, &fi, px, 0) != TPTEX_OK) break;
  }
  if (tptex_writer_finish_memory(w, &file, size) != TPTEX_OK) file = NULL;
  tptex_writer_destroy(w);
  free(px);
  return file;
}

void test_filter(void) {
  int mesh, chaos, ft;
  /* a constant, isolated face filters to its colour with every filter */
  {
    tptex_write_config cfg;
    tptex_writer* w = NULL;
    void* file = NULL;
    size_t size = 0;
    tptex_texture* t = NULL;
    tptex_face_info fi;
    unsigned char pix[3] = {51, 102, 204};
    tptex_write_config_init(&cfg);
    cfg.num_faces = 1;
    TPTEX_CHECK(tptex_writer_create(&cfg, &w) == TPTEX_OK);
    memset(&fi, 0, sizeof fi);
    fi.res = tptex_make_res(3, 3);
    fi.adjfaces[0] = fi.adjfaces[1] = fi.adjfaces[2] = fi.adjfaces[3] = -1;
    TPTEX_CHECK(tptex_writer_write_constant_face(w, 0, &fi, pix) == TPTEX_OK);
    TPTEX_CHECK(tptex_writer_finish_memory(w, &file, &size) == TPTEX_OK);
    tptex_writer_destroy(w);
    TPTEX_CHECK(tptex_open_memory(file, size, NULL, &t) == TPTEX_OK);
    for (ft = 0; ft < 8; ++ft) {
      tptex_filter_options fo;
      tptex_filter* flt = NULL;
      float r[3] = {0, 0, 0};
      tptex_filter_options_init(&fo);
      fo.filter = (tptex_filter_type)ft;
      TPTEX_CHECK(tptex_filter_create(t, &fo, &flt) == TPTEX_OK);
      TPTEX_CHECK(tptex_filter_eval(flt, r, 0, 3, 0, 0.4f, 0.6f, 0.05f, 0.0f, 0.0f, 0.05f, 1.0f, 0.0f) == TPTEX_OK);
      TPTEX_CHECK(fabsf(r[0] - 0.2f) < 1e-5f && fabsf(r[1] - 0.4f) < 1e-5f && fabsf(r[2] - 0.8f) < 1e-5f);
      /* argument validation */
      TPTEX_CHECK(tptex_filter_eval(flt, r, 0, 3, 5, 0.4f, 0.6f, 0.1f, 0, 0, 0.1f, 1, 0) == TPTEX_E_RANGE);
      TPTEX_CHECK(tptex_filter_eval(flt, r, 0, 3, 0, NAN, 0.6f, 0.1f, 0, 0, 0.1f, 1, 0) == TPTEX_E_INVALID_ARG);
      tptex_filter_destroy(flt);
    }
    tptex_close(t);
    tptex_free(NULL, file, size);
  }
  /* hostile adjacency: every filter, many footprints; must never crash or loop */
  for (mesh = 0; mesh < 2; ++mesh)
    for (chaos = 0; chaos < 6; ++chaos) {
      size_t size = 0;
      void* file = build(mesh, 7, 1, &size);
      tptex_texture* t = NULL;
      int it;
      TPTEX_CHECK(file != NULL);
      if (!file) continue;
      TPTEX_CHECK(tptex_open_memory(file, size, NULL, &t) == TPTEX_OK);
      for (ft = 0; t && ft < 8; ++ft) {
        tptex_filter_options fo;
        tptex_filter* flt = NULL;
        tptex_filter_options_init(&fo);
        fo.filter = (tptex_filter_type)ft;
        fo.lerp = ft & 1;
        TPTEX_CHECK(tptex_filter_create(t, &fo, &flt) == TPTEX_OK);
        for (it = 0; it < 200; ++it) {
          float r[3];
          float wd = powf(10.0f, -4.0f * frand()), ang = frand() * 6.2831853f;
          (void)tptex_filter_eval(flt, r, 0, 3, (int)(rnd() % 7), frand() * 1.4f - 0.2f, frand() * 1.4f - 0.2f,
                                  wd * cosf(ang), wd * sinf(ang), -0.3f * wd * sinf(ang), 0.3f * wd * cosf(ang),
                                  1.0f, frand() * 0.02f);
        }
        tptex_filter_destroy(flt);
      }
      tptex_close(t);
      tptex_free(NULL, file, size);
    }
}
