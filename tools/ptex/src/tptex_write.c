/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Ptex writer: a C11 port of upstream PtexMainWriter. Everything upstream keeps in
 * temp files (face data, reductions, tiles, large metadata) lives in memory here,
 * and the final file is assembled into one buffer, so there is no file I/O.
 */
#include <limits.h>

#include "../include/tptex_utils.h"
#include "../include/tptex_write.h"
#include "tptex_internal.h"

enum { HEADER_SIZE = 64, EXT_HEADER_SIZE = 40, LEVEL_INFO_SIZE = 16, FACE_INFO_SIZE = 20 };
enum { ENC_CONSTANT = 0, ENC_ZIPPED = 1, ENC_DIFFZIPPED = 2, ENC_TILED = 3 };
#define MIN_REDUCTION_LOG2 2
#define TILE_SIZE 65536u
#define META_THRESHOLD 1024u
#define MAX_RES_LOG2 30

typedef struct bytebuf {
  uint8_t* data;
  size_t len, cap;
} bytebuf;

typedef struct level_rec {
  uint32_t n;
  uint64_t* pos; /* offsets of each face block within blob */
  uint32_t* fdh;
  bytebuf blob;
} level_rec;

typedef struct meta_ent {
  char* key;
  size_t keylen;
  uint8_t type;
  uint8_t* data;
  uint32_t size;
} meta_ent;

struct tptex_writer {
  tptex_allocator alloc;
  tptex_zlib_ops zlib_copy;
  const tptex_zlib_ops* zlib;
  tptex_mesh_type mesh;
  tptex_data_type dt;
  uint32_t nch, nfaces;
  int32_t alpha;
  int gen_mips, level;
  uint64_t max_block;
  size_t pixsize, dtsize;
  tptex_status st; /* sticky error */
  int finished;

  uint16_t ubord, vbord, edgemode;
  tptex_face_info* faces;
  uint8_t* have;
  uint8_t* constdata;
  uint8_t** red; /* current reduction of each face (host order) */
  size_t* redsize;
  level_rec* levels;
  size_t nlevels, caplevels;
  uint32_t* rfaceids;
  uint32_t* faceids_r;

  meta_ent* meta;
  size_t nmeta, capmeta;
};

#define WALLOC(w, n) tptex__alloc(&(w)->alloc, (n))
#define WFREE(w, p, n) tptex__free(&(w)->alloc, (p), (n))

void tptex_write_config_init(tptex_write_config* c) {
  if (!c) return;
  memset(c, 0, sizeof *c);
  c->mesh_type = TPTEX_MESH_QUAD;
  c->data_type = TPTEX_UINT8;
  c->num_channels = 3;
  c->alpha_channel = -1;
  c->compression_level = -1;
}

/* ------------------------------------------------------------------------- */
/* growable buffer                                                           */

static tptex_status bb_reserve(tptex_writer* w, bytebuf* b, size_t add) {
  size_t need, ncap;
  uint8_t* nd;
  if (add > SIZE_MAX - b->len) return TPTEX_E_OVERFLOW;
  need = b->len + add;
  if (need <= b->cap) return TPTEX_OK;
  ncap = b->cap ? b->cap : 256u;
  while (ncap < need) {
    if (ncap > SIZE_MAX / 2u) { ncap = need; break; }
    ncap *= 2u;
  }
  nd = (uint8_t*)tptex__realloc(&w->alloc, b->data, b->cap, ncap);
  if (!nd) return TPTEX_E_NOMEM;
  b->data = nd;
  b->cap = ncap;
  return TPTEX_OK;
}

static tptex_status bb_append(tptex_writer* w, bytebuf* b, const void* src, size_t n) {
  tptex_status st = bb_reserve(w, b, n);
  if (st != TPTEX_OK) return st;
  if (n) memcpy(b->data + b->len, src, n);
  b->len += n;
  return TPTEX_OK;
}

static void bb_free(tptex_writer* w, bytebuf* b) {
  WFREE(w, b->data, b->cap);
  b->data = NULL;
  b->len = b->cap = 0;
}

static tptex_status fail(tptex_writer* w, tptex_status st) {
  if (w->st == TPTEX_OK) w->st = st;
  return st;
}

/* Deflate src into the tail of out; *zsize receives the compressed size. */
static tptex_status zip_append(tptex_writer* w, bytebuf* out, const void* src, size_t n, size_t* zsize) {
  size_t bound, got = 0;
  tptex_status st;
  static const uint8_t empty = 0;
  if (n > SIZE_MAX / 2u - 4096u) return TPTEX_E_OVERFLOW;
  bound = n + n / 4u + 128u;
  if ((st = bb_reserve(w, out, bound)) != TPTEX_OK) return st;
  st = tptex__deflate(w->zlib, w->level, n ? src : &empty, n, out->data + out->len, bound, &got);
  if (st != TPTEX_OK) return st;
  out->len += got;
  if (zsize) *zsize = got;
  return TPTEX_OK;
}

static uint32_t fdh_make(size_t size, unsigned enc) { return (uint32_t)size | ((uint32_t)enc << 30); }
static uint32_t fdh_size(uint32_t v) { return v & 0x3fffffffu; }

/* ------------------------------------------------------------------------- */
/* create / destroy                                                          */

tptex_status tptex_writer_create(const tptex_write_config* c, tptex_writer** out) {
  tptex_writer* w;
  uint32_t i;
  tptex_write_config def;
  if (out) *out = NULL;
  if (!out) return TPTEX_E_INVALID_ARG;
  if (!c) { tptex_write_config_init(&def); c = &def; }
  if ((int)c->mesh_type < 0 || (int)c->mesh_type > 1 || (int)c->data_type < 0 || (int)c->data_type > 3 ||
      c->num_channels <= 0 || c->num_channels > 65535 || c->num_faces < 0 ||
      (c->alpha_channel != -1 && (c->alpha_channel < 0 || c->alpha_channel >= c->num_channels)))
    return TPTEX_E_INVALID_ARG;
  w = (tptex_writer*)tptex__calloc(&c->allocator, sizeof *w);
  if (!w) return TPTEX_E_NOMEM;
  w->alloc = c->allocator;
  if (c->zlib) { w->zlib_copy = *c->zlib; w->zlib = &w->zlib_copy; }
  w->mesh = c->mesh_type;
  w->dt = c->data_type;
  w->nch = (uint32_t)c->num_channels;
  w->alpha = c->alpha_channel;
  w->nfaces = (uint32_t)c->num_faces;
  w->gen_mips = c->gen_mipmaps != 0;
  w->level = c->compression_level;
  w->max_block = c->max_block_bytes ? c->max_block_bytes : ((uint64_t)1 << 30);
  w->dtsize = tptex_data_type_size(w->dt);
  w->pixsize = w->dtsize * w->nch;
  w->faces = (tptex_face_info*)tptex__calloc(&w->alloc, (size_t)w->nfaces * sizeof(tptex_face_info));
  w->have = (uint8_t*)tptex__calloc(&w->alloc, (size_t)w->nfaces);
  w->constdata = (uint8_t*)tptex__calloc(&w->alloc, (size_t)w->nfaces * w->pixsize);
  w->red = (uint8_t**)tptex__calloc(&w->alloc, (size_t)w->nfaces * sizeof(uint8_t*));
  w->redsize = (size_t*)tptex__calloc(&w->alloc, (size_t)w->nfaces * sizeof(size_t));
  w->levels = (level_rec*)tptex__calloc(&w->alloc, sizeof(level_rec));
  if (!w->faces || !w->have || !w->constdata || !w->red || !w->redsize || !w->levels) {
    tptex_writer_destroy(w);
    return TPTEX_E_NOMEM;
  }
  w->caplevels = 1;
  w->nlevels = 1;
  w->levels[0].n = w->nfaces;
  w->levels[0].pos = (uint64_t*)tptex__calloc(&w->alloc, (size_t)w->nfaces * sizeof(uint64_t));
  w->levels[0].fdh = (uint32_t*)tptex__calloc(&w->alloc, (size_t)w->nfaces * sizeof(uint32_t));
  if (!w->levels[0].pos || !w->levels[0].fdh) { tptex_writer_destroy(w); return TPTEX_E_NOMEM; }
  for (i = 0; i < w->nfaces; ++i) {
    int e;
    for (e = 0; e < 4; ++e) w->faces[i].adjfaces[e] = -1;
  }
  *out = w;
  return TPTEX_OK;
}

void tptex_writer_destroy(tptex_writer* w) {
  size_t i;
  if (!w) return;
  if (w->red)
    for (i = 0; i < w->nfaces; ++i) WFREE(w, w->red[i], w->redsize[i]);
  WFREE(w, w->red, (size_t)w->nfaces * sizeof(uint8_t*));
  WFREE(w, w->redsize, (size_t)w->nfaces * sizeof(size_t));
  WFREE(w, w->faces, (size_t)w->nfaces * sizeof(tptex_face_info));
  WFREE(w, w->have, (size_t)w->nfaces);
  WFREE(w, w->constdata, (size_t)w->nfaces * w->pixsize);
  WFREE(w, w->rfaceids, (size_t)w->nfaces * sizeof(uint32_t));
  WFREE(w, w->faceids_r, (size_t)w->nfaces * sizeof(uint32_t));
  if (w->levels) {
    for (i = 0; i < w->nlevels; ++i) {
      WFREE(w, w->levels[i].pos, (size_t)w->levels[i].n * sizeof(uint64_t));
      WFREE(w, w->levels[i].fdh, (size_t)w->levels[i].n * sizeof(uint32_t));
      bb_free(w, &w->levels[i].blob);
    }
    WFREE(w, w->levels, w->caplevels * sizeof(level_rec));
  }
  for (i = 0; i < w->nmeta; ++i) {
    WFREE(w, w->meta[i].key, w->meta[i].keylen + 1u);
    WFREE(w, w->meta[i].data, w->meta[i].size);
  }
  WFREE(w, w->meta, w->capmeta * sizeof(meta_ent));
  {
    tptex_allocator a = w->alloc;
    tptex__free(&a, w, sizeof *w);
  }
}

tptex_status tptex_writer_set_border_modes(tptex_writer* w, tptex_border_mode u, tptex_border_mode v) {
  if (!w || (int)u < 0 || (int)u > 2 || (int)v < 0 || (int)v > 2) return TPTEX_E_INVALID_ARG;
  w->ubord = (uint16_t)u;
  w->vbord = (uint16_t)v;
  return TPTEX_OK;
}

tptex_status tptex_writer_set_edge_filter_mode(tptex_writer* w, tptex_edge_filter_mode m) {
  if (!w || (int)m < 0 || (int)m > 1) return TPTEX_E_INVALID_ARG;
  w->edgemode = (uint16_t)m;
  return TPTEX_OK;
}

/* ------------------------------------------------------------------------- */
/* metadata                                                                  */

static size_t meta_esize(int type) {
  switch (type) {
    case TPTEX_META_INT16: return 2u;
    case TPTEX_META_INT32:
    case TPTEX_META_FLOAT: return 4u;
    case TPTEX_META_DOUBLE: return 8u;
    default: return 1u;
  }
}

static tptex_status meta_put(tptex_writer* w, const char* key, int type, const void* data, size_t size) {
  size_t klen, i;
  meta_ent* e = NULL;
  uint8_t* copy;
  if (!w || !key || (!data && size)) return TPTEX_E_INVALID_ARG;
  if (w->st != TPTEX_OK) return w->st;
  klen = strlen(key);
  if (klen == 0u || klen > 255u || size == 0u || size > 0xffffffffu) return fail(w, TPTEX_E_INVALID_ARG);
  copy = (uint8_t*)WALLOC(w, size);
  if (!copy) return fail(w, TPTEX_E_NOMEM);
  memcpy(copy, data, size);
  for (i = 0; i < w->nmeta; ++i)
    if (w->meta[i].keylen == klen && memcmp(w->meta[i].key, key, klen) == 0) { e = &w->meta[i]; break; }
  if (e) {
    WFREE(w, e->data, e->size);
  } else {
    if (w->nmeta == w->capmeta) {
      size_t ncap = w->capmeta ? w->capmeta * 2u : 8u;
      meta_ent* n = (meta_ent*)tptex__realloc(&w->alloc, w->meta, w->capmeta * sizeof(meta_ent), ncap * sizeof(meta_ent));
      if (!n) { WFREE(w, copy, size); return fail(w, TPTEX_E_NOMEM); }
      w->meta = n;
      w->capmeta = ncap;
    }
    e = &w->meta[w->nmeta];
    e->key = (char*)WALLOC(w, klen + 1u);
    if (!e->key) { WFREE(w, copy, size); return fail(w, TPTEX_E_NOMEM); }
    memcpy(e->key, key, klen + 1u);
    e->keylen = klen;
    ++w->nmeta;
  }
  e->type = (uint8_t)type;
  e->data = copy;
  e->size = (uint32_t)size;
  return TPTEX_OK;
}

tptex_status tptex_writer_meta_string(tptex_writer* w, const char* key, const char* value) {
  if (!value) return TPTEX_E_INVALID_ARG;
  return meta_put(w, key, TPTEX_META_STRING, value, strlen(value) + 1u);
}

tptex_status tptex_writer_meta(tptex_writer* w, const char* key, tptex_meta_type type, const void* data, int count) {
  size_t esz, total;
  if (!w || (int)type < 0 || (int)type > 5 || count <= 0) return TPTEX_E_INVALID_ARG;
  esz = meta_esize((int)type);
  if ((uint64_t)count > 0xffffffffu / esz) return TPTEX_E_LIMIT;
  total = (size_t)count * esz;
  return meta_put(w, key, (int)type, data, total);
}

/* ------------------------------------------------------------------------- */
/* face data blocks                                                          */

static unsigned floor_log2(uint32_t x) {
  unsigned r = 0;
  while (x > 1u) { x >>= 1; ++r; }
  return r;
}

static tptex_res calc_tile_res(const tptex_writer* w, tptex_res faceres) {
  uint64_t facesize = ((uint64_t)1 << (faceres.ulog2 + faceres.vlog2)) * w->pixsize;
  uint32_t q = (uint32_t)(facesize / TILE_SIZE > 0xffffffffu ? 0xffffffffu : facesize / TILE_SIZE);
  int ntileslog2 = (int)floor_log2(q), n, tu, tv;
  tptex_res t;
  if (ntileslog2 == 0) return faceres;
  n = faceres.ulog2 + faceres.vlog2 - ntileslog2;
  tu = (n + 1) / 2;
  if (tu > faceres.ulog2) tu = faceres.ulog2;
  tv = n - tu;
  if (tv > faceres.vlog2) tv = faceres.vlog2;
  t.ulog2 = (int8_t)tu;
  t.vlog2 = (int8_t)tv;
  return t;
}

static tptex_status check_res(const tptex_writer* w, tptex_res r, size_t* bytes) {
  uint64_t px, total;
  if (r.ulog2 < 0 || r.vlog2 < 0 || r.ulog2 > MAX_RES_LOG2 || r.vlog2 > MAX_RES_LOG2) return TPTEX_E_RANGE;
  px = ((uint64_t)1 << r.ulog2) * ((uint64_t)1 << r.vlog2);
  if (!tptex__mul_u64(px, w->pixsize, &total) || total > w->max_block) return TPTEX_E_LIMIT;
  if (!tptex__to_size(total, bytes)) return TPTEX_E_LIMIT;
  return TPTEX_OK;
}

static tptex_status write_const_block(tptex_writer* w, bytebuf* out, const void* pixel, uint32_t* fdh) {
  uint8_t tmp[256];
  uint8_t* p = tmp;
  tptex_status st;
  if (w->pixsize > sizeof tmp) {
    p = (uint8_t*)WALLOC(w, w->pixsize);
    if (!p) return TPTEX_E_NOMEM;
  }
  memcpy(p, pixel, w->pixsize);
  tptex__le_to_host(p, w->pixsize, w->dtsize); /* host -> LE (the swap is symmetric) */
  st = bb_append(w, out, p, w->pixsize);
  if (p != tmp) WFREE(w, p, w->pixsize);
  if (st == TPTEX_OK) *fdh = fdh_make(w->pixsize, ENC_CONSTANT);
  return st;
}

static tptex_status write_face_block(tptex_writer* w, bytebuf* out, const void* data, size_t stride,
                                     tptex_res res, uint32_t* fdh) {
  size_t bytes, zsize = 0;
  uint8_t* buf;
  int diff = w->dt == TPTEX_UINT8 || w->dt == TPTEX_UINT16;
  tptex_status st = check_res(w, res, &bytes);
  if (st != TPTEX_OK) return st;
  buf = (uint8_t*)WALLOC(w, bytes);
  if (!buf) return TPTEX_E_NOMEM;
  tptex_deinterleave(data, stride, 1 << res.ulog2, 1 << res.vlog2, buf, (size_t)(1u << res.ulog2) * w->dtsize,
                     w->dt, (int)w->nch);
  if (diff) tptex_encode_difference(buf, bytes, w->dt);
  tptex__le_to_host(buf, bytes, w->dtsize);
  st = zip_append(w, out, buf, bytes, &zsize);
  WFREE(w, buf, bytes);
  if (st != TPTEX_OK) return st;
  if (zsize >= 0x40000000u) return TPTEX_E_LIMIT;
  *fdh = fdh_make(zsize, diff ? ENC_DIFFZIPPED : ENC_ZIPPED);
  return TPTEX_OK;
}

static tptex_status write_face_data(tptex_writer* w, bytebuf* out, const void* data, size_t stride,
                                    tptex_res res, uint32_t* fdh) {
  const tptex_res tres = calc_tile_res(w, res);
  const int du = res.ulog2 - tres.ulog2, dv = res.vlog2 - tres.vlog2;
  const size_t ntilesu = (size_t)1 << du, ntilesv = (size_t)1 << dv;
  const size_t ntiles = ntilesu * ntilesv;
  bytebuf tiles, thdr;
  uint32_t* th;
  size_t tu_bytes, tv_stride, ty, tx, i, zsize = 0;
  tptex_status st = TPTEX_OK;
  uint8_t pre[6];
  if (ntiles == 1u) return write_face_block(w, out, data, stride, res, fdh);
  memset(&tiles, 0, sizeof tiles);
  memset(&thdr, 0, sizeof thdr);
  th = (uint32_t*)WALLOC(w, ntiles * sizeof(uint32_t));
  if (!th) return TPTEX_E_NOMEM;
  tu_bytes = (size_t)(1u << tres.ulog2) * w->pixsize;
  tv_stride = (size_t)(1u << tres.vlog2) * stride;
  i = 0;
  for (ty = 0; ty < ntilesv && st == TPTEX_OK; ++ty)
    for (tx = 0; tx < ntilesu && st == TPTEX_OK; ++tx, ++i) {
      const uint8_t* p = (const uint8_t*)data + ty * tv_stride + tx * tu_bytes;
      if (tptex_is_constant(p, stride, 1 << tres.ulog2, 1 << tres.vlog2, (int)w->pixsize))
        st = write_const_block(w, &tiles, p, &th[i]);
      else
        st = write_face_block(w, &tiles, p, stride, tres, &th[i]);
    }
  if (st == TPTEX_OK) {
    uint8_t* raw = (uint8_t*)WALLOC(w, ntiles * 4u);
    if (!raw) st = TPTEX_E_NOMEM;
    else {
      for (i = 0; i < ntiles; ++i) tptex__st_u32(raw + 4u * i, th[i]);
      st = zip_append(w, &thdr, raw, ntiles * 4u, &zsize);
      WFREE(w, raw, ntiles * 4u);
    }
  }
  WFREE(w, th, ntiles * sizeof(uint32_t));
  if (st == TPTEX_OK) {
    size_t total = 6u + thdr.len + tiles.len;
    if (total >= 0x40000000u) st = TPTEX_E_LIMIT;
    else {
      pre[0] = (uint8_t)tres.ulog2;
      pre[1] = (uint8_t)tres.vlog2;
      tptex__st_u32(pre + 2, (uint32_t)thdr.len);
      st = bb_append(w, out, pre, 6u);
      if (st == TPTEX_OK) st = bb_append(w, out, thdr.data, thdr.len);
      if (st == TPTEX_OK) st = bb_append(w, out, tiles.data, tiles.len);
      if (st == TPTEX_OK) *fdh = fdh_make(total, ENC_TILED);
    }
  }
  bb_free(w, &tiles);
  bb_free(w, &thdr);
  return st;
}

/* reduce `data` (res) once into a fresh buffer */
static tptex_status reduce_alloc(tptex_writer* w, const void* data, size_t stride, tptex_res res,
                                 uint8_t** out, size_t* outsize) {
  tptex_res nr = tptex_make_res(res.ulog2 - 1, res.vlog2 - 1);
  size_t bytes;
  uint8_t* buf;
  tptex_status st = check_res(w, nr, &bytes);
  if (st != TPTEX_OK) return st;
  buf = (uint8_t*)WALLOC(w, bytes);
  if (!buf) return TPTEX_E_NOMEM;
  if (w->mesh == TPTEX_MESH_TRIANGLE)
    tptex_reduce_tri(data, stride, 1 << res.ulog2, buf, (size_t)(1u << nr.ulog2) * w->pixsize, w->dt, (int)w->nch);
  else
    tptex_reduce(data, stride, 1 << res.ulog2, 1 << res.vlog2, buf, (size_t)(1u << nr.ulog2) * w->pixsize, w->dt, (int)w->nch);
  *out = buf;
  *outsize = bytes;
  return TPTEX_OK;
}

static int has_alpha(const tptex_writer* w) { return w->alpha >= 0 && (uint32_t)w->alpha < w->nch; }

static void store_const_value(tptex_writer* w, uint32_t faceid, const void* data, size_t stride, tptex_res res) {
  uint8_t* c = w->constdata + (size_t)faceid * w->pixsize;
  tptex_average(data, stride, 1 << res.ulog2, 1 << res.vlog2, c, w->dt, (int)w->nch);
  if (has_alpha(w)) tptex_divalpha(c, 1, w->dt, (int)w->nch, w->alpha);
}

static tptex_status store_face_info(tptex_writer* w, int faceid, const tptex_face_info* src, unsigned flags) {
  tptex_face_info* f;
  if (faceid < 0 || (uint32_t)faceid >= w->nfaces) return TPTEX_E_RANGE;
  if (src->res.ulog2 < 0 || src->res.vlog2 < 0 || src->res.ulog2 > MAX_RES_LOG2 || src->res.vlog2 > MAX_RES_LOG2)
    return TPTEX_E_RANGE;
  if (w->mesh == TPTEX_MESH_TRIANGLE && src->res.ulog2 != src->res.vlog2) return TPTEX_E_UNSUPPORTED;
  f = &w->faces[faceid];
  *f = *src;
  if (w->mesh == TPTEX_MESH_TRIANGLE) {
    f->flags = 0;
    f->adjfaces[3] = -1;
    f->adjedges &= 0x3fu;
  } else {
    f->flags &= TPTEX_FACE_SUBFACE;
  }
  f->flags = (uint8_t)(f->flags | flags);
  w->have[faceid] = 1;
  return TPTEX_OK;
}

tptex_status tptex_writer_write_constant_face(tptex_writer* w, int faceid, const tptex_face_info* info, const void* pixel) {
  tptex_status st;
  if (!w || !info || !pixel) return TPTEX_E_INVALID_ARG;
  if (w->st != TPTEX_OK || w->finished) return w->st != TPTEX_OK ? w->st : TPTEX_E_INVALID_ARG;
  if ((st = store_face_info(w, faceid, info, TPTEX_FACE_CONSTANT)) != TPTEX_OK) return fail(w, st);
  memcpy(w->constdata + (size_t)faceid * w->pixsize, pixel, w->pixsize);
  WFREE(w, w->red[faceid], w->redsize[faceid]);
  w->red[faceid] = NULL;
  w->redsize[faceid] = 0;
  return TPTEX_OK;
}

tptex_status tptex_writer_write_face(tptex_writer* w, int faceid, const tptex_face_info* info, const void* data, size_t stride) {
  size_t bytes;
  const uint8_t* src = (const uint8_t*)data;
  uint8_t* temp = NULL;
  size_t rowlen;
  tptex_status st;
  level_rec* l0;
  if (!w || !info || !data) return TPTEX_E_INVALID_ARG;
  if (w->st != TPTEX_OK || w->finished) return w->st != TPTEX_OK ? w->st : TPTEX_E_INVALID_ARG;
  if ((st = check_res(w, info->res, &bytes)) != TPTEX_OK) return fail(w, st);
  rowlen = (size_t)(1u << info->res.ulog2) * w->pixsize;
  if (stride == 0u) stride = rowlen;
  if (stride < rowlen) return fail(w, TPTEX_E_INVALID_ARG);
  if (tptex_is_constant(data, stride, 1 << info->res.ulog2, 1 << info->res.vlog2, (int)w->pixsize))
    return tptex_writer_write_constant_face(w, faceid, info, data);
  if ((st = store_face_info(w, faceid, info, 0)) != TPTEX_OK) return fail(w, st);
  l0 = &w->levels[0];
  l0->pos[faceid] = l0->blob.len;
  if ((st = write_face_data(w, &l0->blob, data, stride, info->res, &l0->fdh[faceid])) != TPTEX_OK) return fail(w, st);

  /* premultiply before reducing (temp copy) */
  if (has_alpha(w)) {
    temp = (uint8_t*)WALLOC(w, bytes);
    if (!temp) return fail(w, TPTEX_E_NOMEM);
    tptex_copy(data, stride, temp, rowlen, 1 << info->res.vlog2, rowlen);
    tptex_multalpha(temp, 1 << (info->res.ulog2 + info->res.vlog2), w->dt, (int)w->nch, w->alpha);
    src = temp;
    stride = rowlen;
  }
  WFREE(w, w->red[faceid], w->redsize[faceid]);
  w->red[faceid] = NULL;
  w->redsize[faceid] = 0;
  if (w->gen_mips && info->res.ulog2 > MIN_REDUCTION_LOG2 && info->res.vlog2 > MIN_REDUCTION_LOG2)
    st = reduce_alloc(w, src, stride, info->res, &w->red[faceid], &w->redsize[faceid]);
  else
    store_const_value(w, (uint32_t)faceid, src, stride, info->res);
  WFREE(w, temp, bytes);
  return st == TPTEX_OK ? TPTEX_OK : fail(w, st);
}

/* ------------------------------------------------------------------------- */
/* finish                                                                    */

static tptex_status generate_reductions(tptex_writer* w) {
  const uint32_t nfaces = w->nfaces;
  uint32_t rf;
  int cutoff = MIN_REDUCTION_LOG2;
  size_t li;
  tptex_status st;
  w->rfaceids = (uint32_t*)WALLOC(w, (size_t)nfaces * sizeof(uint32_t));
  w->faceids_r = (uint32_t*)WALLOC(w, (size_t)nfaces * sizeof(uint32_t));
  if (!w->rfaceids || !w->faceids_r) return TPTEX_E_NOMEM;
  tptex_gen_rfaceids(w->faces, nfaces, w->rfaceids, w->faceids_r);

  /* levels: count faces larger than each cutoff, scanning smallest-first */
  for (rf = nfaces; rf-- > 0;) {
    const tptex_face_info* f = &w->faces[w->faceids_r[rf]];
    int mn = tptex_face_is_constant(f) ? 1 : (f->res.ulog2 < f->res.vlog2 ? f->res.ulog2 : f->res.vlog2);
    while (mn > cutoff) {
      level_rec* lr;
      if (w->nlevels == w->caplevels) {
        size_t ncap = w->caplevels * 2u;
        level_rec* nl = (level_rec*)tptex__realloc(&w->alloc, w->levels, w->caplevels * sizeof(level_rec), ncap * sizeof(level_rec));
        if (!nl) return TPTEX_E_NOMEM;
        w->levels = nl;
        w->caplevels = ncap;
      }
      lr = &w->levels[w->nlevels++];
      memset(lr, 0, sizeof *lr);
      lr->n = rf + 1u;
      lr->pos = (uint64_t*)tptex__calloc(&w->alloc, (size_t)lr->n * sizeof(uint64_t));
      lr->fdh = (uint32_t*)tptex__calloc(&w->alloc, (size_t)lr->n * sizeof(uint32_t));
      if (!lr->pos || !lr->fdh) return TPTEX_E_NOMEM;
      ++cutoff;
    }
  }

  for (li = 1; li < w->nlevels; ++li) {
    level_rec* lv = &w->levels[li];
    const uint32_t nextsize = li + 1u < w->nlevels ? w->levels[li + 1u].n : 0u;
    for (rf = 0; rf < lv->n; ++rf) {
      const uint32_t faceid = w->faceids_r[rf];
      tptex_res res = w->faces[faceid].res;
      size_t stride;
      uint8_t* cur = w->red[faceid];
      if (!cur) return TPTEX_E_CORRUPT;
      res.ulog2 = (int8_t)(res.ulog2 - (int)li);
      res.vlog2 = (int8_t)(res.vlog2 - (int)li);
      stride = (size_t)(1u << res.ulog2) * w->pixsize;
      lv->pos[rf] = lv->blob.len;
      if ((st = write_face_data(w, &lv->blob, cur, stride, res, &lv->fdh[rf])) != TPTEX_OK) return st;
      if (rf < nextsize) {
        uint8_t* nxt = NULL;
        size_t nsz = 0;
        if ((st = reduce_alloc(w, cur, stride, res, &nxt, &nsz)) != TPTEX_OK) return st;
        WFREE(w, w->red[faceid], w->redsize[faceid]);
        w->red[faceid] = nxt;
        w->redsize[faceid] = nsz;
      } else {
        store_const_value(w, faceid, cur, stride, res);
      }
    }
  }
  return TPTEX_OK;
}

static int const_equal(const tptex_writer* w, uint32_t a, uint32_t b) {
  return memcmp(w->constdata + (size_t)a * w->pixsize, w->constdata + (size_t)b * w->pixsize, w->pixsize) == 0;
}

static void flag_constant_neighborhoods(tptex_writer* w) {
  const int is_tri = w->mesh == TPTEX_MESH_TRIANGLE, nedges = is_tri ? 3 : 4;
  const int maxcount = 10;
  uint32_t faceid;
  for (faceid = 0; faceid < w->nfaces; ++faceid) {
    tptex_face_info* f = &w->faces[faceid];
    int is_const = 1, eid;
    if (!tptex_face_is_constant(f)) continue;
    for (eid = 0; is_const && eid < nedges; ++eid) {
      int prev_sub = tptex_face_is_subface(f);
      int prev_fid = (int)faceid;
      int afid = f->adjfaces[eid];
      int aeid = (int)tptex_face_adjedge(f, eid);
      int count = 0;
      while (afid != (int)faceid && afid >= 0 && (uint32_t)afid < w->nfaces && ++count < maxcount) {
        const tptex_face_info* af = &w->faces[afid];
        int is_sub, is_t;
        if (!tptex_face_is_constant(af) || !const_equal(w, faceid, (uint32_t)afid)) { is_const = 0; break; }
        is_sub = tptex_face_is_subface(af);
        is_t = !is_tri && prev_sub && !is_sub && af->adjfaces[aeid] == prev_fid;
        if (is_t) break;
        prev_sub = is_sub;
        prev_fid = afid;
        aeid = (aeid + 1) % nedges;
        afid = af->adjfaces[aeid];
        aeid = (int)tptex_face_adjedge(af, aeid);
      }
      if (afid < 0) {
        if (w->ubord != (uint16_t)TPTEX_BORDER_CLAMP || w->vbord != (uint16_t)TPTEX_BORDER_CLAMP) is_const = 0;
        if (is_const) {
          aeid = (aeid - 1 + nedges) % nedges;
          afid = f->adjfaces[aeid];
          aeid = (int)tptex_face_adjedge(f, aeid);
          count = 0;
          while (afid != (int)faceid && afid >= 0 && (uint32_t)afid < w->nfaces && ++count < maxcount) {
            const tptex_face_info* af = &w->faces[afid];
            int is_sub;
            if (!tptex_face_is_constant(af) || !const_equal(w, faceid, (uint32_t)afid)) { is_const = 0; break; }
            prev_fid = afid;
            aeid = (aeid - 1 + nedges) % nedges;
            afid = af->adjfaces[aeid];
            aeid = (int)tptex_face_adjedge(af, aeid);
            is_sub = tptex_face_is_subface(af);
            if (is_sub && !prev_sub) {
              aeid = (aeid + 3) % 4;
              afid = af->adjfaces[aeid];
              aeid = ((int)tptex_face_adjedge(af, aeid) + 3) % 4;
            }
            prev_sub = is_sub;
          }
        }
      }
    }
    if (is_const) f->flags = (uint8_t)(f->flags | TPTEX_FACE_NBCONSTANT);
  }
}

static tptex_status meta_block(tptex_writer* w, bytebuf* b, const meta_ent* e, int lmd_header, uint32_t zipsize) {
  uint8_t hdr[16];
  uint8_t ks = (uint8_t)(e->keylen + 1u);
  tptex_status st;
  hdr[0] = ks;
  if ((st = bb_append(w, b, hdr, 1)) != TPTEX_OK) return st;
  if ((st = bb_append(w, b, e->key, (size_t)ks)) != TPTEX_OK) return st;
  hdr[0] = e->type;
  tptex__st_u32(hdr + 1, e->size);
  if (lmd_header) {
    tptex__st_u32(hdr + 5, zipsize);
    return bb_append(w, b, hdr, 9);
  }
  return bb_append(w, b, hdr, 5);
}

static tptex_status build_file(tptex_writer* w, bytebuf* out) {
  uint8_t hdr[HEADER_SIZE], ext[EXT_HEADER_SIZE];
  uint8_t* raw;
  size_t raw_size, zsize = 0, level_info_pos, li, i;
  uint64_t leveldatasize = 0, editpos;
  uint32_t faceinfosize, constdatasize, metazip = 0, metamem = 0, lmdhzip = 0, lmdhmem = 0;
  uint64_t lmddatasize = 0;
  tptex_status st;
  memset(hdr, 0, sizeof hdr);
  memset(ext, 0, sizeof ext);
  if ((st = bb_append(w, out, hdr, HEADER_SIZE)) != TPTEX_OK) return st;
  if ((st = bb_append(w, out, ext, EXT_HEADER_SIZE)) != TPTEX_OK) return st;

  /* face info */
  raw_size = (size_t)w->nfaces * FACE_INFO_SIZE;
  raw = (uint8_t*)WALLOC(w, raw_size);
  if (!raw) return TPTEX_E_NOMEM;
  for (i = 0; i < w->nfaces; ++i) {
    uint8_t* p = raw + i * FACE_INFO_SIZE;
    const tptex_face_info* f = &w->faces[i];
    int e;
    p[0] = (uint8_t)f->res.ulog2;
    p[1] = (uint8_t)f->res.vlog2;
    p[2] = f->adjedges;
    p[3] = f->flags;
    for (e = 0; e < 4; ++e) tptex__st_u32(p + 4 + 4 * e, (uint32_t)f->adjfaces[e]);
  }
  st = zip_append(w, out, raw, raw_size, &zsize);
  WFREE(w, raw, raw_size);
  if (st != TPTEX_OK) return st;
  faceinfosize = (uint32_t)zsize;

  /* constant data */
  raw_size = (size_t)w->nfaces * w->pixsize;
  raw = (uint8_t*)WALLOC(w, raw_size);
  if (!raw) return TPTEX_E_NOMEM;
  memcpy(raw, w->constdata, raw_size);
  tptex__le_to_host(raw, raw_size, w->dtsize);
  st = zip_append(w, out, raw, raw_size, &zsize);
  WFREE(w, raw, raw_size);
  if (st != TPTEX_OK) return st;
  constdatasize = (uint32_t)zsize;

  /* level info placeholder */
  level_info_pos = out->len;
  {
    size_t n = w->nlevels * LEVEL_INFO_SIZE;
    if ((st = bb_reserve(w, out, n)) != TPTEX_OK) return st;
    memset(out->data + out->len, 0, n);
    out->len += n;
  }
  for (li = 0; li < w->nlevels; ++li) {
    level_rec* lv = &w->levels[li];
    size_t hzip = 0, f;
    uint64_t ldsize;
    uint8_t* lh = (uint8_t*)WALLOC(w, (size_t)lv->n * 4u + 1u);
    if (!lh) return TPTEX_E_NOMEM;
    for (f = 0; f < lv->n; ++f) tptex__st_u32(lh + 4u * f, lv->fdh[f]);
    st = zip_append(w, out, lh, (size_t)lv->n * 4u, &hzip);
    WFREE(w, lh, (size_t)lv->n * 4u + 1u);
    if (st != TPTEX_OK) return st;
    ldsize = hzip;
    for (f = 0; f < lv->n; ++f) {
      size_t bs = fdh_size(lv->fdh[f]);
      if (!bs) continue;
      if (lv->pos[f] + bs > lv->blob.len) return TPTEX_E_CORRUPT;
      if ((st = bb_append(w, out, lv->blob.data + lv->pos[f], bs)) != TPTEX_OK) return st;
      ldsize += bs;
    }
    tptex__st_u64(out->data + level_info_pos + li * LEVEL_INFO_SIZE, ldsize);
    tptex__st_u32(out->data + level_info_pos + li * LEVEL_INFO_SIZE + 8, (uint32_t)hzip);
    tptex__st_u32(out->data + level_info_pos + li * LEVEL_INFO_SIZE + 12, lv->n);
    leveldatasize += ldsize;
  }

  /* metadata: small entries in one zip block, barrier, then large entries */
  {
    bytebuf mb, lh, ld;
    size_t nlarge = 0, lzip;
    memset(&mb, 0, sizeof mb);
    memset(&lh, 0, sizeof lh);
    memset(&ld, 0, sizeof ld);
    st = TPTEX_OK;
    for (i = 0; i < w->nmeta && st == TPTEX_OK; ++i) {
      const meta_ent* e = &w->meta[i];
      uint8_t* tmp;
      if (e->size > META_THRESHOLD) { ++nlarge; continue; }
      if ((st = meta_block(w, &mb, e, 0, 0)) != TPTEX_OK) break;
      tmp = (uint8_t*)WALLOC(w, e->size);
      if (!tmp) { st = TPTEX_E_NOMEM; break; }
      memcpy(tmp, e->data, e->size);
      tptex__le_to_host(tmp, e->size, meta_esize(e->type));
      st = bb_append(w, &mb, tmp, e->size);
      WFREE(w, tmp, e->size);
    }
    if (st == TPTEX_OK && mb.len) {
      metamem = (uint32_t)mb.len;
      st = zip_append(w, out, mb.data, mb.len, &zsize);
      metazip = (uint32_t)zsize;
    }
    if (st == TPTEX_OK) { /* compatibility barrier */
      static const uint8_t zeros[8] = {0, 0, 0, 0, 0, 0, 0, 0};
      st = bb_append(w, out, zeros, sizeof zeros);
    }
    if (st == TPTEX_OK && nlarge) {
      for (i = 0; i < w->nmeta && st == TPTEX_OK; ++i) {
        const meta_ent* e = &w->meta[i];
        uint8_t* tmp;
        size_t zs = 0;
        if (e->size <= META_THRESHOLD) continue;
        tmp = (uint8_t*)WALLOC(w, e->size);
        if (!tmp) { st = TPTEX_E_NOMEM; break; }
        memcpy(tmp, e->data, e->size);
        tptex__le_to_host(tmp, e->size, meta_esize(e->type));
        st = zip_append(w, &ld, tmp, e->size, &zs);
        WFREE(w, tmp, e->size);
        if (st != TPTEX_OK) break;
        st = meta_block(w, &lh, e, 1, (uint32_t)zs);
      }
      if (st == TPTEX_OK) {
        lmdhmem = (uint32_t)lh.len;
        st = zip_append(w, out, lh.data, lh.len, &lzip);
        lmdhzip = (uint32_t)lzip;
      }
      if (st == TPTEX_OK) {
        st = bb_append(w, out, ld.data, ld.len);
        lmddatasize = ld.len;
      }
    }
    bb_free(w, &mb);
    bb_free(w, &lh);
    bb_free(w, &ld);
    if (st != TPTEX_OK) return st;
  }
  editpos = out->len;

  /* header + extended header */
  tptex__st_u32(hdr + 0, (uint32_t)('P' | ('t' << 8) | ('e' << 16) | ((uint32_t)'x' << 24)));
  tptex__st_u32(hdr + 4, 1u);
  tptex__st_u32(hdr + 8, (uint32_t)w->mesh);
  tptex__st_u32(hdr + 12, (uint32_t)w->dt);
  tptex__st_u32(hdr + 16, (uint32_t)w->alpha);
  tptex__st_u16(hdr + 20, (uint16_t)w->nch);
  tptex__st_u16(hdr + 22, (uint16_t)w->nlevels);
  tptex__st_u32(hdr + 24, w->nfaces);
  tptex__st_u32(hdr + 28, EXT_HEADER_SIZE);
  tptex__st_u32(hdr + 32, faceinfosize);
  tptex__st_u32(hdr + 36, constdatasize);
  tptex__st_u32(hdr + 40, (uint32_t)(w->nlevels * LEVEL_INFO_SIZE));
  tptex__st_u32(hdr + 44, 4u); /* minor version */
  tptex__st_u64(hdr + 48, leveldatasize);
  tptex__st_u32(hdr + 56, metazip);
  tptex__st_u32(hdr + 60, metamem);
  tptex__st_u16(ext + 0, w->ubord);
  tptex__st_u16(ext + 4, w->vbord);
  tptex__st_u16(ext + 6, w->edgemode);
  tptex__st_u32(ext + 8, lmdhzip);
  tptex__st_u32(ext + 12, lmdhmem);
  tptex__st_u64(ext + 16, lmddatasize);
  tptex__st_u64(ext + 24, 0u);
  tptex__st_u64(ext + 32, editpos);
  memcpy(out->data, hdr, HEADER_SIZE);
  memcpy(out->data + HEADER_SIZE, ext, EXT_HEADER_SIZE);
  return TPTEX_OK;
}

static tptex_status finish_build(tptex_writer* w, bytebuf* out) {
  uint32_t i;
  tptex_status st;
  if (!w) return TPTEX_E_INVALID_ARG;
  if (w->st != TPTEX_OK) return w->st;
  if (w->finished) return TPTEX_E_INVALID_ARG;
  w->finished = 1;
  for (i = 0; i < w->nfaces; ++i)
    if (!w->have[i]) w->faces[i].flags = (uint8_t)TPTEX_FACE_CONSTANT;
  if (w->gen_mips && (st = generate_reductions(w)) != TPTEX_OK) return fail(w, st);
  flag_constant_neighborhoods(w);
  if ((st = build_file(w, out)) != TPTEX_OK) return fail(w, st);
  return TPTEX_OK;
}

tptex_status tptex_writer_finish(tptex_writer* w, const tptex_sink* sink) {
  bytebuf out;
  tptex_status st;
  if (!w || !sink || !sink->write) return TPTEX_E_INVALID_ARG;
  memset(&out, 0, sizeof out);
  st = finish_build(w, &out);
  if (st == TPTEX_OK) {
    size_t off = 0;
    while (st == TPTEX_OK && off < out.len) {
      size_t n = out.len - off < 65536u ? out.len - off : 65536u;
      st = sink->write(sink->user, out.data + off, n);
      off += n;
    }
  }
  bb_free(w, &out);
  return st;
}

tptex_status tptex_writer_finish_memory(tptex_writer* w, void** data, size_t* size) {
  bytebuf out;
  tptex_status st;
  if (!w || !data || !size) return TPTEX_E_INVALID_ARG;
  *data = NULL;
  *size = 0;
  memset(&out, 0, sizeof out);
  st = finish_build(w, &out);
  if (st != TPTEX_OK) { bb_free(w, &out); return st; }
  if (out.cap != out.len) { /* shrink so the caller's free size equals the length */
    uint8_t* nd = (uint8_t*)tptex__realloc(&w->alloc, out.data, out.cap, out.len);
    if (nd) { out.data = nd; out.cap = out.len; }
  }
  *data = out.data;
  *size = out.len;
  return TPTEX_OK;
}
