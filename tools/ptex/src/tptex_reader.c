/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 * Portions derived from Ptex, Copyright 2014 Disney Enterprises, Inc. (NOTICE).
 *
 * Ptex container reader: a C11 port of upstream PtexReader.cpp.
 *
 * Differences from upstream, all deliberate:
 *  - no atomics, volatile or threads; the texture is internally mutable (lazy
 *    level headers, large metadata) so one texture must not be read from two
 *    threads at once (use one texture per thread, or a lock around it);
 *  - explicit little-endian parsing and byte swapping, so big-endian hosts work
 *    (upstream refuses them);
 *  - every size/offset is overflow-checked and bounded by tptex_limits and, when
 *    known, the input size; malformed files fail with a status instead of
 *    reading out of bounds;
 *  - tiled faces are assembled whole when read or reduced (upstream reduces tile
 *    by tile to stay lazy); the pixels produced are identical.
 *
 * On-disk layout (all fields little-endian): 64-byte header, extended header
 * (40 bytes, zero-filled when shorter), zipped face-info block, zipped constant
 * (average colour) block, level-info table, level data, zipped metadata,
 * 8-byte compatibility barrier, large-metadata headers + data, edit blocks.
 */
#include <limits.h>

#include "../include/tptex_utils.h"
#include "tptex_internal.h"

enum {
  HEADER_SIZE = 64,
  EXT_HEADER_SIZE = 40,
  LEVEL_INFO_SIZE = 16,
  FACE_INFO_SIZE = 20,
  EDIT_FACE_HEADER_SIZE = 28,
  EDIT_META_HEADER_SIZE = 8
};
enum { ENC_CONSTANT = 0, ENC_ZIPPED = 1, ENC_DIFFZIPPED = 2, ENC_TILED = 3 };
enum { EDIT_FACE_DATA = 0, EDIT_META_DATA = 1 };
#define MAX_RES_LOG2 30

typedef struct level_info {
  uint64_t data_size;
  uint32_t header_size;
  uint32_t nfaces;
} level_info;

typedef struct level {
  int loaded;
  uint32_t nfaces;
  uint32_t* fdh;      /* face data headers (bits 0..29 block size, 30..31 encoding) */
  uint64_t* offsets;  /* absolute file offsets of each face's data */
} level;

typedef struct face_edit {
  uint64_t pos;
  uint32_t faceid;
  uint32_t fdh;
} face_edit;

typedef struct meta_edit {
  uint64_t pos;
  uint32_t zipsize;
  uint32_t memsize;
} meta_edit;

typedef struct meta_entry {
  char* key; /* NUL-terminated, keylen bytes before the NUL */
  size_t keylen;
  uint8_t type;
  uint32_t datasize;
  uint8_t* data;     /* NULL until loaded for large metadata */
  int is_lmd;
  uint64_t lmd_pos;
  uint32_t lmd_zipsize;
} meta_entry;

struct tptex_texture {
  tptex_allocator alloc;
  tptex_limits limits;
  uint32_t flags;
  tptex_zlib_ops zlib_copy;
  const tptex_zlib_ops* zlib; /* NULL = built-in */
  tptex_input in;
  void* handle;
  int have_size;
  uint64_t file_size;

  uint32_t meshtype, datatype, nchannels, nlevels, nfaces;
  int32_t alphachan;
  uint32_t extheadersize, faceinfosize, constdatasize, levelinfosize, metadatazipsize,
      metadatamemsize;
  uint64_t leveldatasize;
  uint16_t ubordermode, vbordermode, edgefiltermode;
  uint32_t lmdheaderzipsize, lmdheadermemsize;
  uint64_t lmddatasize, editdatasize, editdatapos;

  uint64_t faceinfopos, constdatapos, levelinfopos, leveldatapos, metadatapos, lmdheaderpos,
      lmddatapos, editpos;
  size_t pixelsize;
  tptex_info info;

  tptex_face_info* faces;
  uint32_t* rfaceids;
  uint8_t* constdata;
  level_info* levelinfo;
  uint64_t* levelpos;
  level* levels;

  face_edit* faceedits;
  size_t nfaceedits, capfaceedits;
  meta_edit* metaedits;
  size_t nmetaedits, capmetaedits;
  int has_edits;

  int meta_loaded;
  meta_entry* meta;
  size_t nmeta, capmeta;
  uint64_t meta_bytes;

  tptex_memory_source mem; /* backing store for tptex_open_memory */
};

/* decoded face payload: one pixel when is_const, otherwise a full image */
typedef struct fbuf {
  uint8_t* data;
  size_t size;
  int is_const;
  int owned;
} fbuf;

/* ------------------------------------------------------------------------- */
/* allocation and I/O helpers                                                */

#define TALLOC(t, n) tptex__alloc(&(t)->alloc, (n))
#define TFREE(t, p, n) tptex__free(&(t)->alloc, (p), (n))

static tptex_status rd(const tptex_texture* t, uint64_t off, void* dst, size_t n) {
  size_t got = 0;
  tptex_status st;
  if (n == 0u) return TPTEX_OK;
  if (t->have_size) {
    uint64_t end;
    if (!tptex__add_u64(off, (uint64_t)n, &end) || end > t->file_size) return TPTEX_E_CORRUPT;
  }
  st = t->in.read_at(t->in.user, t->handle, off, dst, n, &got);
  if (st != TPTEX_OK) return st;
  return got == n ? TPTEX_OK : TPTEX_E_CORRUPT;
}

static tptex_status check_block_size(const tptex_texture* t, uint64_t n) {
  size_t tmp;
  if (n > t->limits.max_block_bytes) return TPTEX_E_LIMIT;
  return tptex__to_size(n, &tmp) ? TPTEX_OK : TPTEX_E_LIMIT;
}

/* Read a zlib block of `zipsize` bytes at `off` and inflate to exactly
 * `dst_size` bytes (the file's data is not yet host-ordered). */
static tptex_status read_zip(tptex_texture* t, uint64_t off, uint64_t zipsize, void* dst,
                             size_t dst_size) {
  uint8_t* tmp;
  tptex_status st = check_block_size(t, zipsize);
  size_t zs;
  if (st != TPTEX_OK) return st;
  if (dst_size == 0u && zipsize == 0u) return TPTEX_OK;
  zs = (size_t)zipsize;
  tmp = (uint8_t*)TALLOC(t, zs);
  if (!tmp) return TPTEX_E_NOMEM;
  st = rd(t, off, tmp, zs);
  if (st == TPTEX_OK) st = tptex__inflate(t->zlib, tmp, zs, dst, dst_size);
  TFREE(t, tmp, zs);
  return st;
}

static int has_alpha(const tptex_texture* t) {
  return t->alphachan >= 0 && (uint32_t)t->alphachan < t->nchannels;
}
static int premultiply_on(const tptex_texture* t) {
  return (t->flags & TPTEX_OPEN_PREMULTIPLY) != 0u && has_alpha(t);
}
static size_t es(const tptex_texture* t) { return tptex_data_type_size((tptex_data_type)t->datatype); }

/* ------------------------------------------------------------------------- */
/* teardown                                                                  */

static void meta_free(tptex_texture* t) {
  size_t i;
  for (i = 0; i < t->nmeta; ++i) {
    TFREE(t, t->meta[i].key, t->meta[i].keylen + 1u);
    TFREE(t, t->meta[i].data, t->meta[i].datasize);
  }
  TFREE(t, t->meta, t->capmeta * sizeof(meta_entry));
  t->meta = NULL;
  t->nmeta = t->capmeta = 0;
}

void tptex_close(tptex_texture* t) {
  uint32_t i;
  if (!t) return;
  if (t->handle && t->in.close) t->in.close(t->in.user, t->handle);
  if (t->levels) {
    for (i = 0; i < t->nlevels; ++i) {
      TFREE(t, t->levels[i].fdh, (size_t)t->levels[i].nfaces * sizeof(uint32_t));
      TFREE(t, t->levels[i].offsets, (size_t)t->levels[i].nfaces * sizeof(uint64_t));
    }
    TFREE(t, t->levels, (size_t)t->nlevels * sizeof(level));
  }
  TFREE(t, t->levelinfo, (size_t)t->nlevels * sizeof(level_info));
  TFREE(t, t->levelpos, (size_t)t->nlevels * sizeof(uint64_t));
  TFREE(t, t->faces, (size_t)t->nfaces * sizeof(tptex_face_info));
  TFREE(t, t->rfaceids, (size_t)t->nfaces * sizeof(uint32_t));
  TFREE(t, t->constdata, (size_t)t->nfaces * t->pixelsize);
  TFREE(t, t->faceedits, t->capfaceedits * sizeof(face_edit));
  TFREE(t, t->metaedits, t->capmetaedits * sizeof(meta_edit));
  meta_free(t);
  {
    tptex_allocator a = t->alloc;
    tptex__free(&a, t, sizeof *t);
  }
}

/* ------------------------------------------------------------------------- */
/* open                                                                      */

static tptex_status parse_face_info_block(tptex_texture* t) {
  size_t raw_size = 0;
  uint8_t* raw;
  uint32_t i;
  uint64_t need;
  tptex_status st;
  if (!tptex__mul_u64(t->nfaces, FACE_INFO_SIZE, &need) || !tptex__to_size(need, &raw_size))
    return TPTEX_E_OVERFLOW;
  if ((st = check_block_size(t, need)) != TPTEX_OK) return st;
  t->faces = (tptex_face_info*)TALLOC(t, (size_t)t->nfaces * sizeof(tptex_face_info));
  t->rfaceids = (uint32_t*)TALLOC(t, (size_t)t->nfaces * sizeof(uint32_t));
  raw = (uint8_t*)TALLOC(t, raw_size);
  if (!t->faces || !t->rfaceids || !raw) { TFREE(t, raw, raw_size); return TPTEX_E_NOMEM; }
  st = read_zip(t, t->faceinfopos, t->faceinfosize, raw, raw_size);
  if (st == TPTEX_OK) {
    for (i = 0; i < t->nfaces; ++i) {
      const uint8_t* p = raw + (size_t)i * FACE_INFO_SIZE;
      tptex_face_info* f = &t->faces[i];
      int e;
      f->res.ulog2 = (int8_t)p[0];
      f->res.vlog2 = (int8_t)p[1];
      f->adjedges = p[2];
      f->flags = p[3];
      for (e = 0; e < 4; ++e) f->adjfaces[e] = (int32_t)tptex__ld_u32(p + 4 + 4 * e);
      if (f->res.ulog2 < 0 || f->res.vlog2 < 0 || f->res.ulog2 > MAX_RES_LOG2 ||
          f->res.vlog2 > MAX_RES_LOG2) {
        st = TPTEX_E_CORRUPT;
        break;
      }
    }
  }
  TFREE(t, raw, raw_size);
  if (st != TPTEX_OK) return st;
  {
    uint32_t* scratch = (uint32_t*)TALLOC(t, (size_t)t->nfaces * sizeof(uint32_t));
    if (!scratch) return TPTEX_E_NOMEM;
    tptex_gen_rfaceids(t->faces, t->nfaces, t->rfaceids, scratch);
    TFREE(t, scratch, (size_t)t->nfaces * sizeof(uint32_t));
  }
  return TPTEX_OK;
}

static tptex_status parse_const_data(tptex_texture* t) {
  uint64_t need;
  size_t n;
  tptex_status st;
  if (!tptex__mul_u64(t->nfaces, t->pixelsize, &need) || !tptex__to_size(need, &n))
    return TPTEX_E_OVERFLOW;
  if ((st = check_block_size(t, need)) != TPTEX_OK) return st;
  t->constdata = (uint8_t*)TALLOC(t, n);
  if (!t->constdata) return TPTEX_E_NOMEM;
  st = read_zip(t, t->constdatapos, t->constdatasize, t->constdata, n);
  if (st != TPTEX_OK) return st;
  tptex__le_to_host(t->constdata, n, es(t));
  if (premultiply_on(t))
    tptex_multalpha(t->constdata, (int)t->nfaces, (tptex_data_type)t->datatype, (int)t->nchannels,
                    t->alphachan);
  return TPTEX_OK;
}

static tptex_status parse_levels(tptex_texture* t) {
  uint8_t* raw;
  size_t raw_size = 0;
  uint64_t need, pos;
  uint32_t i;
  tptex_status st;
  if (t->nlevels == 0u) return t->nfaces ? TPTEX_E_CORRUPT : TPTEX_OK;
  if (!tptex__mul_u64(t->nlevels, LEVEL_INFO_SIZE, &need) || !tptex__to_size(need, &raw_size))
    return TPTEX_E_OVERFLOW;
  t->levelinfo = (level_info*)TALLOC(t, (size_t)t->nlevels * sizeof(level_info));
  t->levelpos = (uint64_t*)TALLOC(t, (size_t)t->nlevels * sizeof(uint64_t));
  t->levels = (level*)tptex__calloc(&t->alloc, (size_t)t->nlevels * sizeof(level));
  raw = (uint8_t*)TALLOC(t, raw_size);
  if (!t->levelinfo || !t->levelpos || !t->levels || !raw) { TFREE(t, raw, raw_size); return TPTEX_E_NOMEM; }
  st = rd(t, t->levelinfopos, raw, raw_size);
  if (st == TPTEX_OK) {
    pos = t->leveldatapos;
    for (i = 0; i < t->nlevels; ++i) {
      const uint8_t* p = raw + (size_t)i * LEVEL_INFO_SIZE;
      t->levelinfo[i].data_size = tptex__ld_u64(p);
      t->levelinfo[i].header_size = tptex__ld_u32(p + 8);
      t->levelinfo[i].nfaces = tptex__ld_u32(p + 12);
      t->levelpos[i] = pos;
      if (!tptex__add_u64(pos, t->levelinfo[i].data_size, &pos)) { st = TPTEX_E_OVERFLOW; break; }
      /* level 0 indexes faces by id; reduction levels hold a prefix of faces */
      if (i == 0u ? t->levelinfo[0].nfaces != t->nfaces : t->levelinfo[i].nfaces > t->nfaces) {
        st = TPTEX_E_CORRUPT;
        break;
      }
    }
  }
  TFREE(t, raw, raw_size);
  return st;
}

static tptex_status push_face_edit(tptex_texture* t, uint64_t pos, uint32_t faceid, uint32_t fdh) {
  if (t->nfaceedits == t->capfaceedits) {
    size_t ncap = t->capfaceedits ? t->capfaceedits * 2u : 8u;
    face_edit* n = (face_edit*)tptex__realloc(&t->alloc, t->faceedits,
                                              t->capfaceedits * sizeof(face_edit),
                                              ncap * sizeof(face_edit));
    if (!n) return TPTEX_E_NOMEM;
    t->faceedits = n;
    t->capfaceedits = ncap;
  }
  t->faceedits[t->nfaceedits].pos = pos;
  t->faceedits[t->nfaceedits].faceid = faceid;
  t->faceedits[t->nfaceedits].fdh = fdh;
  ++t->nfaceedits;
  return TPTEX_OK;
}

static tptex_status push_meta_edit(tptex_texture* t, uint64_t pos, uint32_t zipsize, uint32_t memsize) {
  if (t->nmetaedits == t->capmetaedits) {
    size_t ncap = t->capmetaedits ? t->capmetaedits * 2u : 4u;
    meta_edit* n = (meta_edit*)tptex__realloc(&t->alloc, t->metaedits,
                                              t->capmetaedits * sizeof(meta_edit),
                                              ncap * sizeof(meta_edit));
    if (!n) return TPTEX_E_NOMEM;
    t->metaedits = n;
    t->capmetaedits = ncap;
  }
  t->metaedits[t->nmetaedits].pos = pos;
  t->metaedits[t->nmetaedits].zipsize = zipsize;
  t->metaedits[t->nmetaedits].memsize = memsize;
  ++t->nmetaedits;
  return TPTEX_OK;
}

/* Scan the edit blocks (face-data and metadata edits). Truncation just ends the
 * scan, as upstream does; an individually malformed edit is skipped. */
static tptex_status read_edit_data(tptex_texture* t) {
  uint64_t pos = t->editpos, endpos;
  if (t->editdatapos > 0u) {
    if (!tptex__add_u64(pos, t->editdatasize, &endpos)) endpos = UINT64_MAX;
  } else {
    endpos = UINT64_MAX;
  }
  while (pos < endpos) {
    uint8_t hdr[5];
    uint32_t editsize;
    uint64_t body, next;
    if (rd(t, pos, hdr, sizeof hdr) != TPTEX_OK) break;
    editsize = tptex__ld_u32(hdr + 1);
    if (!editsize) break;
    t->has_edits = 1;
    body = pos + sizeof hdr;
    if (!tptex__add_u64(body, editsize, &next)) break;
    if (hdr[0] == EDIT_FACE_DATA) {
      uint8_t eh[EDIT_FACE_HEADER_SIZE];
      if (editsize >= EDIT_FACE_HEADER_SIZE && rd(t, body, eh, sizeof eh) == TPTEX_OK) {
        uint32_t faceid = tptex__ld_u32(eh);
        if (faceid < t->nfaces) {
          tptex_face_info f;
          int e;
          uint64_t cpos = body + EDIT_FACE_HEADER_SIZE;
          uint8_t* cd = t->constdata + (size_t)faceid * t->pixelsize;
          f.res.ulog2 = (int8_t)eh[4];
          f.res.vlog2 = (int8_t)eh[5];
          f.adjedges = eh[6];
          f.flags = eh[7];
          for (e = 0; e < 4; ++e) f.adjfaces[e] = (int32_t)tptex__ld_u32(eh + 8 + 4 * e);
          if (f.res.ulog2 >= 0 && f.res.vlog2 >= 0 && f.res.ulog2 <= MAX_RES_LOG2 &&
              f.res.vlog2 <= MAX_RES_LOG2) {
            f.flags |= TPTEX_FACE_HASEDITS;
            t->faces[faceid] = f;
            if (rd(t, cpos, cd, t->pixelsize) == TPTEX_OK) {
              tptex__le_to_host(cd, t->pixelsize, es(t));
              if (premultiply_on(t))
                tptex_multalpha(cd, 1, (tptex_data_type)t->datatype, (int)t->nchannels, t->alphachan);
              if (!tptex_face_is_constant(&f)) {
                tptex_status st = push_face_edit(t, cpos + t->pixelsize, faceid, tptex__ld_u32(eh + 24));
                if (st != TPTEX_OK) return st;
              }
            }
          }
        }
      }
    } else if (hdr[0] == EDIT_META_DATA) {
      uint8_t mh[EDIT_META_HEADER_SIZE];
      if (editsize >= EDIT_META_HEADER_SIZE && rd(t, body, mh, sizeof mh) == TPTEX_OK) {
        tptex_status st = push_meta_edit(t, body + EDIT_META_HEADER_SIZE, tptex__ld_u32(mh),
                                         tptex__ld_u32(mh + 4));
        if (st != TPTEX_OK) return st;
      }
    }
    pos = next;
  }
  return TPTEX_OK;
}

static tptex_status open_impl(tptex_texture* t, const char* path) {
  uint8_t hdr[HEADER_SIZE];
  uint8_t ext[EXT_HEADER_SIZE];
  uint64_t pos;
  size_t ext_read;
  tptex_status st = t->in.open(t->in.user, path, &t->handle);
  if (st != TPTEX_OK) return st;
  if (t->in.size && t->in.size(t->in.user, t->handle, &t->file_size) == TPTEX_OK) t->have_size = 1;

  if ((st = rd(t, 0, hdr, sizeof hdr)) != TPTEX_OK) return st == TPTEX_E_CORRUPT ? TPTEX_E_BAD_MAGIC : st;
  if (tptex__ld_u32(hdr) != (uint32_t)('P' | ('t' << 8) | ('e' << 16) | ((uint32_t)'x' << 24)))
    return TPTEX_E_BAD_MAGIC;
  if (tptex__ld_u32(hdr + 4) != 1u) return TPTEX_E_BAD_VERSION;
  t->meshtype = tptex__ld_u32(hdr + 8);
  t->datatype = tptex__ld_u32(hdr + 12);
  t->alphachan = (int32_t)tptex__ld_u32(hdr + 16);
  t->nchannels = tptex__ld_u16(hdr + 20);
  t->nlevels = tptex__ld_u16(hdr + 22);
  t->nfaces = tptex__ld_u32(hdr + 24);
  t->extheadersize = tptex__ld_u32(hdr + 28);
  t->faceinfosize = tptex__ld_u32(hdr + 32);
  t->constdatasize = tptex__ld_u32(hdr + 36);
  t->levelinfosize = tptex__ld_u32(hdr + 40);
  /* hdr + 44: minor version (unused) */
  t->leveldatasize = tptex__ld_u64(hdr + 48);
  t->metadatazipsize = tptex__ld_u32(hdr + 56);
  t->metadatamemsize = tptex__ld_u32(hdr + 60);

  if (t->meshtype > 1u || t->datatype > 3u || t->nchannels == 0u) return TPTEX_E_CORRUPT;
  if (t->nfaces > t->limits.max_faces) return TPTEX_E_LIMIT;
  t->pixelsize = es(t) * (size_t)t->nchannels;

  memset(ext, 0, sizeof ext);
  ext_read = t->extheadersize < EXT_HEADER_SIZE ? t->extheadersize : (size_t)EXT_HEADER_SIZE;
  if ((st = rd(t, HEADER_SIZE, ext, ext_read)) != TPTEX_OK) return st;
  t->ubordermode = tptex__ld_u16(ext);
  t->vbordermode = tptex__ld_u16(ext + 4);
  t->edgefiltermode = tptex__ld_u16(ext + 6);
  t->lmdheaderzipsize = tptex__ld_u32(ext + 8);
  t->lmdheadermemsize = tptex__ld_u32(ext + 12);
  t->lmddatasize = tptex__ld_u64(ext + 16);
  t->editdatasize = tptex__ld_u64(ext + 24);
  t->editdatapos = tptex__ld_u64(ext + 32);

  /* block offsets, accumulated with overflow checks */
  pos = HEADER_SIZE;
#define ADVANCE(field, amount)                                              \
  do {                                                                      \
    field = pos;                                                            \
    if (!tptex__add_u64(pos, (uint64_t)(amount), &pos)) return TPTEX_E_OVERFLOW; \
  } while (0)
  if (!tptex__add_u64(pos, t->extheadersize, &pos)) return TPTEX_E_OVERFLOW;
  ADVANCE(t->faceinfopos, t->faceinfosize);
  ADVANCE(t->constdatapos, t->constdatasize);
  ADVANCE(t->levelinfopos, t->levelinfosize);
  ADVANCE(t->leveldatapos, t->leveldatasize);
  ADVANCE(t->metadatapos, t->metadatazipsize);
  if (!tptex__add_u64(pos, sizeof(uint64_t), &pos)) return TPTEX_E_OVERFLOW; /* compatibility barrier */
  ADVANCE(t->lmdheaderpos, t->lmdheaderzipsize);
  ADVANCE(t->lmddatapos, t->lmddatasize);
#undef ADVANCE
  /* edit data may not follow immediately when sections were added: honour the
   * extended header's position when it is further along */
  t->editpos = t->editdatapos > pos ? t->editdatapos : pos;

  if ((st = parse_face_info_block(t)) != TPTEX_OK) return st;
  if ((st = parse_const_data(t)) != TPTEX_OK) return st;
  if ((st = parse_levels(t)) != TPTEX_OK) return st;
  if (!(t->flags & TPTEX_OPEN_NO_EDITS)) {
    if ((st = read_edit_data(t)) != TPTEX_OK) return st;
  }

  t->info.mesh_type = (tptex_mesh_type)t->meshtype;
  t->info.data_type = (tptex_data_type)t->datatype;
  t->info.alpha_channel = t->alphachan;
  t->info.num_channels = (int32_t)t->nchannels;
  t->info.num_faces = (int32_t)t->nfaces;
  t->info.num_levels = (int32_t)t->nlevels;
  t->info.u_border_mode = (tptex_border_mode)t->ubordermode;
  t->info.v_border_mode = (tptex_border_mode)t->vbordermode;
  t->info.edge_filter_mode = (tptex_edge_filter_mode)t->edgefiltermode;
  t->info.has_edits = t->has_edits;
  t->info.has_mipmaps = t->nlevels > 1u;
  return TPTEX_OK;
}

tptex_status tptex_open(const tptex_input* input, const char* path, const tptex_options* options,
                        tptex_texture** out) {
  tptex_options def;
  tptex_texture* t;
  tptex_status st;
  if (out) *out = NULL;
  if (!input || !input->open || !input->read_at || !out) return TPTEX_E_INVALID_ARG;
  if (!options) { tptex_options_init(&def); options = &def; }
  t = (tptex_texture*)tptex__calloc(&options->allocator, sizeof *t);
  if (!t) return TPTEX_E_NOMEM;
  t->alloc = options->allocator;
  t->limits = options->limits;
  if (!t->limits.max_faces) t->limits.max_faces = (uint64_t)1 << 26;
  if (!t->limits.max_block_bytes) t->limits.max_block_bytes = (uint64_t)1 << 30;
  if (!t->limits.max_meta_bytes) t->limits.max_meta_bytes = (uint64_t)1 << 30;
  t->flags = options->flags;
  if (options->zlib) { t->zlib_copy = *options->zlib; t->zlib = &t->zlib_copy; }
  t->in = *input;
  st = open_impl(t, path);
  if (st != TPTEX_OK) { tptex_close(t); return st; }
  *out = t;
  return TPTEX_OK;
}

tptex_status tptex_open_memory(const void* data, size_t size, const tptex_options* options,
                               tptex_texture** out) {
  /* The texture must own the source record for its lazy reads, so build it by
   * hand rather than on this function's stack. */
  tptex_options def;
  tptex_texture* t;
  tptex_status st;
  if (out) *out = NULL;
  if (!out || (!data && size)) return TPTEX_E_INVALID_ARG;
  if (!options) { tptex_options_init(&def); options = &def; }
  t = (tptex_texture*)tptex__calloc(&options->allocator, sizeof *t);
  if (!t) return TPTEX_E_NOMEM;
  t->alloc = options->allocator;
  t->limits = options->limits;
  if (!t->limits.max_faces) t->limits.max_faces = (uint64_t)1 << 26;
  if (!t->limits.max_block_bytes) t->limits.max_block_bytes = (uint64_t)1 << 30;
  if (!t->limits.max_meta_bytes) t->limits.max_meta_bytes = (uint64_t)1 << 30;
  t->flags = options->flags;
  if (options->zlib) { t->zlib_copy = *options->zlib; t->zlib = &t->zlib_copy; }
  t->mem.data = data;
  t->mem.size = size;
  st = tptex_input_from_memory(&t->in, &t->mem);
  if (st == TPTEX_OK) st = open_impl(t, NULL);
  if (st != TPTEX_OK) { tptex_close(t); return st; }
  *out = t;
  return TPTEX_OK;
}

const tptex_info* tptex_get_info(const tptex_texture* t) { return t ? &t->info : NULL; }

size_t tptex_pixel_size(const tptex_texture* t) { return t ? t->pixelsize : 0u; }

tptex_status tptex_get_face_info(const tptex_texture* t, int faceid, tptex_face_info* out) {
  if (!t || !out) return TPTEX_E_INVALID_ARG;
  if (faceid < 0 || (uint32_t)faceid >= t->nfaces) return TPTEX_E_RANGE;
  *out = t->faces[faceid];
  return TPTEX_OK;
}

/* ------------------------------------------------------------------------- */
/* face data                                                                 */

static void fbuf_release(tptex_texture* t, fbuf* b) {
  if (b->owned) TFREE(t, b->data, b->size);
  b->data = NULL;
  b->size = 0;
  b->owned = 0;
}

static tptex_status res_bytes(const tptex_texture* t, tptex_res res, uint64_t* npixels, size_t* bytes) {
  uint64_t px, total;
  if (res.ulog2 < 0 || res.vlog2 < 0 || res.ulog2 > MAX_RES_LOG2 || res.vlog2 > MAX_RES_LOG2)
    return TPTEX_E_RANGE;
  px = ((uint64_t)1 << res.ulog2) * ((uint64_t)1 << res.vlog2);
  if (!tptex__mul_u64(px, t->pixelsize, &total)) return TPTEX_E_OVERFLOW;
  if (total > t->limits.max_block_bytes) return TPTEX_E_LIMIT;
  if (!tptex__to_size(total, bytes)) return TPTEX_E_LIMIT;
  *npixels = px;
  return TPTEX_OK;
}

static tptex_status read_const_pixel(tptex_texture* t, uint64_t pos, int levelid, fbuf* out) {
  tptex_status st;
  out->data = (uint8_t*)TALLOC(t, t->pixelsize);
  if (!out->data) return TPTEX_E_NOMEM;
  out->size = t->pixelsize;
  out->is_const = 1;
  out->owned = 1;
  st = rd(t, pos, out->data, t->pixelsize);
  if (st != TPTEX_OK) { fbuf_release(t, out); return st; }
  tptex__le_to_host(out->data, t->pixelsize, es(t));
  if (levelid == 0 && premultiply_on(t))
    tptex_multalpha(out->data, 1, (tptex_data_type)t->datatype, (int)t->nchannels, t->alphachan);
  return TPTEX_OK;
}

/* A non-tiled record: constant, zipped or difference-zipped. */
static tptex_status read_leaf(tptex_texture* t, uint64_t pos, uint32_t fdh, tptex_res res,
                              int levelid, fbuf* out) {
  const uint32_t enc = (fdh >> 30) & 3u, blocksize = fdh & 0x3fffffffu;
  uint64_t npixels;
  size_t bytes;
  uint8_t* tmp;
  tptex_status st;
  if (enc == ENC_CONSTANT) return read_const_pixel(t, pos, levelid, out);
  if (enc != ENC_ZIPPED && enc != ENC_DIFFZIPPED) return TPTEX_E_CORRUPT;
  if ((st = res_bytes(t, res, &npixels, &bytes)) != TPTEX_OK) return st;
  if (npixels > (uint64_t)INT_MAX) return TPTEX_E_LIMIT;
  out->data = (uint8_t*)TALLOC(t, bytes);
  tmp = (uint8_t*)TALLOC(t, bytes);
  if (!out->data || !tmp) { TFREE(t, out->data, bytes); TFREE(t, tmp, bytes); out->data = NULL; return TPTEX_E_NOMEM; }
  out->size = bytes;
  out->is_const = 0;
  out->owned = 1;
  st = read_zip(t, pos, blocksize, tmp, bytes);
  if (st == TPTEX_OK) {
    const size_t esz = es(t);
    tptex__le_to_host(tmp, bytes, esz);
    if (enc == ENC_DIFFZIPPED) tptex_decode_difference(tmp, bytes, (tptex_data_type)t->datatype);
    /* the stored block is channel-planar; interleave it */
    tptex_interleave(tmp, (size_t)(1u << res.ulog2) * esz, 1 << res.ulog2, 1 << res.vlog2, out->data,
                     (size_t)(1u << res.ulog2) * t->pixelsize, (tptex_data_type)t->datatype,
                     (int)t->nchannels);
    if (levelid == 0 && premultiply_on(t))
      tptex_multalpha(out->data, (int)npixels, (tptex_data_type)t->datatype, (int)t->nchannels,
                      t->alphachan);
  }
  TFREE(t, tmp, bytes);
  if (st != TPTEX_OK) fbuf_release(t, out);
  return st;
}

static tptex_status read_record(tptex_texture* t, uint64_t pos, uint32_t fdh, tptex_res res,
                                int levelid, fbuf* out) {
  const uint32_t enc = (fdh >> 30) & 3u;
  uint8_t th[6];
  tptex_res tres;
  uint64_t ntilesu, ntilesv, ntiles, nbytes64, hdr_pos, tpos;
  uint32_t tile_header_size, i;
  uint32_t* tfdh;
  uint8_t* raw;
  size_t raw_size, full_bytes, tile_bytes;
  uint64_t dummy;
  tptex_status st;
  size_t rowlen, tile_rowlen, tu, tv;
  int du, dv;
  if (enc != ENC_TILED) return read_leaf(t, pos, fdh, res, levelid, out);

  if ((st = rd(t, pos, th, sizeof th)) != TPTEX_OK) return st;
  tres.ulog2 = (int8_t)th[0];
  tres.vlog2 = (int8_t)th[1];
  tile_header_size = tptex__ld_u32(th + 2);
  if (tres.ulog2 < 0 || tres.vlog2 < 0 || tres.ulog2 > res.ulog2 || tres.vlog2 > res.vlog2)
    return TPTEX_E_CORRUPT;
  du = res.ulog2 - tres.ulog2;
  dv = res.vlog2 - tres.vlog2;
  if (du + dv > 30) return TPTEX_E_LIMIT;
  ntilesu = (uint64_t)1 << du;
  ntilesv = (uint64_t)1 << dv;
  ntiles = ntilesu * ntilesv;
  if (!tptex__mul_u64(ntiles, 4u, &nbytes64) || nbytes64 > t->limits.max_block_bytes) return TPTEX_E_LIMIT;
  if ((st = res_bytes(t, res, &dummy, &full_bytes)) != TPTEX_OK) return st;
  if ((st = res_bytes(t, tres, &dummy, &tile_bytes)) != TPTEX_OK) return st;
  raw_size = (size_t)nbytes64;
  raw = (uint8_t*)TALLOC(t, raw_size);
  tfdh = (uint32_t*)TALLOC(t, (size_t)ntiles * sizeof(uint32_t));
  out->data = (uint8_t*)TALLOC(t, full_bytes);
  if (!raw || !tfdh || !out->data) {
    TFREE(t, raw, raw_size); TFREE(t, tfdh, (size_t)ntiles * sizeof(uint32_t)); TFREE(t, out->data, full_bytes);
    out->data = NULL;
    return TPTEX_E_NOMEM;
  }
  out->size = full_bytes;
  out->is_const = 0;
  out->owned = 1;
  hdr_pos = pos + sizeof th;
  st = read_zip(t, hdr_pos, tile_header_size, raw, raw_size);
  if (st == TPTEX_OK) {
    if (!tptex__add_u64(hdr_pos, tile_header_size, &tpos)) st = TPTEX_E_OVERFLOW;
  }
  rowlen = (size_t)(1u << res.ulog2) * t->pixelsize;
  tile_rowlen = (size_t)(1u << tres.ulog2) * t->pixelsize;
  tu = (size_t)1 << tres.ulog2;
  tv = (size_t)1 << tres.vlog2;
  for (i = 0; st == TPTEX_OK && i < (uint32_t)ntiles; ++i) {
    fbuf tile;
    uint32_t tf = tptex__ld_u32(raw + (size_t)i * 4u);
    size_t tx = (size_t)(i % (uint32_t)ntilesu), ty = (size_t)(i / (uint32_t)ntilesu);
    uint8_t* dst = out->data + ty * tv * rowlen + tx * tile_rowlen;
    memset(&tile, 0, sizeof tile);
    tfdh[i] = tf;
    if (((tf >> 30) & 3u) == ENC_TILED) { st = TPTEX_E_CORRUPT; break; }
    st = read_leaf(t, tpos, tf, tres, levelid, &tile);
    if (st != TPTEX_OK) break;
    if (tile.is_const) tptex_fill(tile.data, dst, rowlen, (int)tu, (int)tv, (int)t->pixelsize);
    else tptex_copy(tile.data, tile_rowlen, dst, rowlen, (int)tv, tile_rowlen);
    fbuf_release(t, &tile);
    if (!tptex__add_u64(tpos, tf & 0x3fffffffu, &tpos)) st = TPTEX_E_OVERFLOW;
  }
  TFREE(t, raw, raw_size);
  TFREE(t, tfdh, (size_t)ntiles * sizeof(uint32_t));
  if (st != TPTEX_OK) fbuf_release(t, out);
  return st;
}

/* Load a level's face-data-header table and absolute offsets (level 0 also
 * receives the face-edit overrides). */
static tptex_status level_ensure(tptex_texture* t, uint32_t id) {
  level* lv;
  uint8_t* raw;
  size_t raw_size;
  uint64_t need, pos;
  uint32_t i;
  tptex_status st;
  if (id >= t->nlevels) return TPTEX_E_RANGE;
  lv = &t->levels[id];
  if (lv->loaded) return TPTEX_OK;
  if (!tptex__mul_u64(t->levelinfo[id].nfaces, 4u, &need) || !tptex__to_size(need, &raw_size))
    return TPTEX_E_OVERFLOW;
  if ((st = check_block_size(t, need)) != TPTEX_OK) return st;
  raw = (uint8_t*)TALLOC(t, raw_size);
  lv->fdh = (uint32_t*)TALLOC(t, (size_t)t->levelinfo[id].nfaces * sizeof(uint32_t));
  lv->offsets = (uint64_t*)TALLOC(t, (size_t)t->levelinfo[id].nfaces * sizeof(uint64_t));
  lv->nfaces = t->levelinfo[id].nfaces;
  if (!raw || !lv->fdh || !lv->offsets) {
    TFREE(t, raw, raw_size);
    TFREE(t, lv->fdh, (size_t)lv->nfaces * sizeof(uint32_t));
    TFREE(t, lv->offsets, (size_t)lv->nfaces * sizeof(uint64_t));
    lv->fdh = NULL; lv->offsets = NULL; lv->nfaces = 0;
    return TPTEX_E_NOMEM;
  }
  st = read_zip(t, t->levelpos[id], t->levelinfo[id].header_size, raw, raw_size);
  if (st == TPTEX_OK) {
    st = tptex__add_u64(t->levelpos[id], t->levelinfo[id].header_size, &pos) ? TPTEX_OK : TPTEX_E_OVERFLOW;
  }
  for (i = 0; st == TPTEX_OK && i < lv->nfaces; ++i) {
    lv->fdh[i] = tptex__ld_u32(raw + (size_t)i * 4u);
    lv->offsets[i] = pos;
    if (!tptex__add_u64(pos, lv->fdh[i] & 0x3fffffffu, &pos)) st = TPTEX_E_OVERFLOW;
  }
  TFREE(t, raw, raw_size);
  if (st != TPTEX_OK) {
    TFREE(t, lv->fdh, (size_t)lv->nfaces * sizeof(uint32_t));
    TFREE(t, lv->offsets, (size_t)lv->nfaces * sizeof(uint64_t));
    lv->fdh = NULL; lv->offsets = NULL; lv->nfaces = 0;
    return st;
  }
  if (id == 0u) {
    size_t k;
    for (k = 0; k < t->nfaceedits; ++k) {
      lv->fdh[t->faceedits[k].faceid] = t->faceedits[k].fdh;
      lv->offsets[t->faceedits[k].faceid] = t->faceedits[k].pos;
    }
  }
  lv->loaded = 1;
  return TPTEX_OK;
}

static tptex_status level_face(tptex_texture* t, uint32_t levelid, uint32_t idx, tptex_res res, fbuf* out) {
  tptex_status st = level_ensure(t, levelid);
  if (st != TPTEX_OK) return st;
  if (idx >= t->levels[levelid].nfaces) return TPTEX_E_RANGE;
  return read_record(t, t->levels[levelid].offsets[idx], t->levels[levelid].fdh[idx], res,
                     (int)levelid, out);
}

static tptex_status face_buffer(tptex_texture* t, uint32_t faceid, tptex_res res, fbuf* out);

/* Generate a reduction on the fly (upstream getData's dynamic path). */
static tptex_status dynamic_reduce(tptex_texture* t, uint32_t faceid, tptex_res res, int redu,
                                   int redv, fbuf* out) {
  fbuf src;
  tptex_res sres;
  uint64_t npixels, snpixels;
  size_t bytes, sbytes;
  int use_u = 0, tri = t->meshtype == (uint32_t)TPTEX_MESH_TRIANGLE;
  tptex_status st;
  if (res.ulog2 < 0 || res.vlog2 < 0 || redu < 0 || redv < 0) return TPTEX_E_UNSUPPORTED;
  if (tri && redu != redv) return TPTEX_E_UNSUPPORTED;
  if (tri) sres = tptex_make_res(res.ulog2 + 1, res.vlog2 + 1);
  else {
    use_u = redu == redv ? (res.ulog2 & 1) : (redu > redv);
    sres = use_u ? tptex_make_res(res.ulog2 + 1, res.vlog2) : tptex_make_res(res.ulog2, res.vlog2 + 1);
  }
  memset(&src, 0, sizeof src);
  if ((st = face_buffer(t, faceid, sres, &src)) != TPTEX_OK) return st;
  if (src.is_const) { /* a constant stays constant; hand the pixel over */
    *out = src;
    return TPTEX_OK;
  }
  if ((st = res_bytes(t, res, &npixels, &bytes)) != TPTEX_OK || (st = res_bytes(t, sres, &snpixels, &sbytes)) != TPTEX_OK) {
    fbuf_release(t, &src);
    return st;
  }
  if (tri && sres.ulog2 != sres.vlog2) { fbuf_release(t, &src); return TPTEX_E_CORRUPT; }
  out->data = (uint8_t*)TALLOC(t, bytes);
  if (!out->data) { fbuf_release(t, &src); return TPTEX_E_NOMEM; }
  out->size = bytes;
  out->is_const = 0;
  out->owned = 1;
  {
    const size_t sstride = (size_t)(1u << sres.ulog2) * t->pixelsize;
    const size_t dstride = (size_t)(1u << res.ulog2) * t->pixelsize;
    const tptex_data_type dt = (tptex_data_type)t->datatype;
    if (tri) tptex_reduce_tri(src.data, sstride, 1 << sres.ulog2, out->data, dstride, dt, (int)t->nchannels);
    else if (use_u) tptex_reduce_u(src.data, sstride, 1 << sres.ulog2, 1 << sres.vlog2, out->data, dstride, dt, (int)t->nchannels);
    else tptex_reduce_v(src.data, sstride, 1 << sres.ulog2, 1 << sres.vlog2, out->data, dstride, dt, (int)t->nchannels);
  }
  fbuf_release(t, &src);
  return TPTEX_OK;
}

/* upstream PtexReader::getData(faceid, res) */
static tptex_status face_buffer(tptex_texture* t, uint32_t faceid, tptex_res res, fbuf* out) {
  const tptex_face_info* fi = &t->faces[faceid];
  int redu, redv;
  memset(out, 0, sizeof *out);
  if (tptex_face_is_constant(fi) || (res.ulog2 == 0 && res.vlog2 == 0)) {
    out->data = t->constdata + (size_t)faceid * t->pixelsize;
    out->size = t->pixelsize;
    out->is_const = 1;
    out->owned = 0;
    return TPTEX_OK;
  }
  redu = fi->res.ulog2 - res.ulog2;
  redv = fi->res.vlog2 - res.vlog2;
  if (redu == 0 && redv == 0) return level_face(t, 0u, faceid, res, out);
  if (redu == redv && redu > 0 && !(fi->flags & TPTEX_FACE_HASEDITS) && (uint32_t)redu < t->nlevels) {
    const uint32_t rf = t->rfaceids[faceid];
    tptex_status st = level_ensure(t, (uint32_t)redu);
    if (st != TPTEX_OK) return st;
    if (rf < t->levels[redu].nfaces) return level_face(t, (uint32_t)redu, rf, res, out);
  }
  return dynamic_reduce(t, faceid, res, redu, redv, out);
}

tptex_status tptex_get_data(tptex_texture* t, int faceid, tptex_res res, void* buffer, size_t stride) {
  fbuf b;
  tptex_status st;
  size_t rowlen;
  int ru, rv;
  if (!t || !buffer) return TPTEX_E_INVALID_ARG;
  if (res.ulog2 < 0 || res.vlog2 < 0 || res.ulog2 > MAX_RES_LOG2 || res.vlog2 > MAX_RES_LOG2)
    return TPTEX_E_RANGE;
  ru = 1 << res.ulog2;
  rv = 1 << res.vlog2;
  rowlen = (size_t)ru * t->pixelsize;
  if (stride == 0u) stride = rowlen;
  if (stride < rowlen) return TPTEX_E_INVALID_ARG;
  if (faceid < 0 || (uint32_t)faceid >= t->nfaces) {
    /* upstream fills the zero error pixel */
    uint8_t zero[64];
    int r;
    memset(zero, 0, sizeof zero);
    if (t->pixelsize <= sizeof zero) {
      tptex_fill(zero, buffer, stride, ru, rv, (int)t->pixelsize);
    } else {
      for (r = 0; r < rv; ++r) memset((uint8_t*)buffer + (size_t)r * stride, 0, rowlen);
    }
    return TPTEX_E_RANGE;
  }
  st = face_buffer(t, (uint32_t)faceid, res, &b);
  if (st != TPTEX_OK) {
    int r;
    for (r = 0; r < rv; ++r) memset((uint8_t*)buffer + (size_t)r * stride, 0, rowlen);
    return st;
  }
  if (b.is_const) tptex_fill(b.data, buffer, stride, ru, rv, (int)t->pixelsize);
  else tptex_copy(b.data, rowlen, buffer, stride, rv, rowlen);
  fbuf_release(t, &b);
  return TPTEX_OK;
}

tptex_status tptex_get_face_data(tptex_texture* t, int faceid, tptex_res res, tptex_face_data* out) {
  fbuf b;
  tptex_status st;
  if (!t || !out) return TPTEX_E_INVALID_ARG;
  memset(out, 0, sizeof *out);
  if (faceid < 0 || (uint32_t)faceid >= t->nfaces) return TPTEX_E_RANGE;
  if (res.ulog2 < 0 || res.vlog2 < 0 || res.ulog2 > MAX_RES_LOG2 || res.vlog2 > MAX_RES_LOG2)
    return TPTEX_E_RANGE;
  if ((st = face_buffer(t, (uint32_t)faceid, res, &b)) != TPTEX_OK) return st;
  out->data = b.data;
  out->is_constant = b.is_const;
  out->size_ = b.size;
  out->owned_ = b.owned;
  return TPTEX_OK;
}

void tptex_release_face_data(tptex_texture* t, tptex_face_data* d) {
  fbuf b;
  if (!t || !d) return;
  b.data = (uint8_t*)(uintptr_t)d->data;
  b.size = d->size_;
  b.is_const = d->is_constant;
  b.owned = d->owned_;
  fbuf_release(t, &b);
  memset(d, 0, sizeof *d);
}

tptex_status tptex_get_constant(tptex_texture* t, int faceid, void* pixel) {
  if (!t || !pixel) return TPTEX_E_INVALID_ARG;
  if (faceid < 0 || (uint32_t)faceid >= t->nfaces) return TPTEX_E_RANGE;
  memcpy(pixel, t->constdata + (size_t)faceid * t->pixelsize, t->pixelsize);
  return TPTEX_OK;
}

static tptex_status get_pixel_impl(tptex_texture* t, int faceid, int u, int v, float* result,
                                   int firstchan, int nchannels, int use_res, tptex_res res) {
  fbuf b;
  tptex_status st;
  const uint8_t* px;
  int avail, i;
  if (!t || !result) return TPTEX_E_INVALID_ARG;
  for (i = 0; i < nchannels; ++i) result[i] = 0.0f;
  avail = (int)t->nchannels - firstchan;
  if (nchannels > avail) nchannels = avail;
  if (nchannels <= 0) return TPTEX_OK;
  if (faceid < 0 || (uint32_t)faceid >= t->nfaces) return TPTEX_E_RANGE;
  if (!use_res) res = t->faces[faceid].res;
  if (u < 0 || v < 0 || res.ulog2 < 0 || res.vlog2 < 0 || u >= (1 << res.ulog2) || v >= (1 << res.vlog2))
    return TPTEX_E_RANGE;
  st = face_buffer(t, (uint32_t)faceid, res, &b);
  if (st != TPTEX_OK) return st;
  px = b.is_const ? b.data : b.data + ((size_t)v * (size_t)(1 << res.ulog2) + (size_t)u) * t->pixelsize;
  px += (size_t)firstchan * es(t);
  tptex_convert_to_float(result, px, (tptex_data_type)t->datatype, nchannels);
  fbuf_release(t, &b);
  return TPTEX_OK;
}

tptex_status tptex_get_pixel(tptex_texture* t, int faceid, int u, int v, float* result,
                             int firstchan, int nchannels) {
  return get_pixel_impl(t, faceid, u, v, result, firstchan, nchannels, 0, tptex_make_res(0, 0));
}

tptex_status tptex_get_pixel_res(tptex_texture* t, int faceid, int u, int v, float* result,
                                 int firstchan, int nchannels, tptex_res res) {
  return get_pixel_impl(t, faceid, u, v, result, firstchan, nchannels, 1, res);
}

/* ------------------------------------------------------------------------- */
/* metadata                                                                  */

static size_t meta_elem_size(uint8_t type) {
  switch (type) {
    case TPTEX_META_INT16: return 2u;
    case TPTEX_META_INT32:
    case TPTEX_META_FLOAT: return 4u;
    case TPTEX_META_DOUBLE: return 8u;
    default: return 1u;
  }
}

/* Add (or replace in place) an entry; `data` is copied unless is_lmd. */
static tptex_status meta_add(tptex_texture* t, const uint8_t* key, size_t keylen, uint8_t type,
                             uint32_t datasize, const uint8_t* data, int is_lmd, uint64_t lmd_pos,
                             uint32_t lmd_zipsize) {
  size_t i;
  meta_entry* e = NULL;
  uint8_t* copy = NULL;
  if (!is_lmd) {
    if (t->meta_bytes + datasize > t->limits.max_meta_bytes) return TPTEX_E_LIMIT;
    copy = (uint8_t*)TALLOC(t, datasize);
    if (!copy) return TPTEX_E_NOMEM;
    memcpy(copy, data, datasize);
    tptex__le_to_host(copy, datasize, meta_elem_size(type));
  }
  for (i = 0; i < t->nmeta; ++i)
    if (t->meta[i].keylen == keylen && memcmp(t->meta[i].key, key, keylen) == 0) { e = &t->meta[i]; break; }
  if (e) {
    if (e->data) {
      t->meta_bytes -= e->datasize;
      TFREE(t, e->data, e->datasize);
    }
  } else {
    if (t->nmeta == t->capmeta) {
      size_t ncap = t->capmeta ? t->capmeta * 2u : 16u;
      meta_entry* n = (meta_entry*)tptex__realloc(&t->alloc, t->meta, t->capmeta * sizeof(meta_entry),
                                                  ncap * sizeof(meta_entry));
      if (!n) { TFREE(t, copy, datasize); return TPTEX_E_NOMEM; }
      t->meta = n;
      t->capmeta = ncap;
    }
    e = &t->meta[t->nmeta];
    memset(e, 0, sizeof *e);
    e->key = (char*)TALLOC(t, keylen + 1u);
    if (!e->key) { TFREE(t, copy, datasize); return TPTEX_E_NOMEM; }
    memcpy(e->key, key, keylen);
    e->key[keylen] = '\0';
    e->keylen = keylen;
    ++t->nmeta;
  }
  e->type = type;
  e->datasize = datasize;
  e->data = copy;
  e->is_lmd = is_lmd;
  e->lmd_pos = lmd_pos;
  e->lmd_zipsize = lmd_zipsize;
  if (!is_lmd) t->meta_bytes += datasize;
  return TPTEX_OK;
}

/* Primary / edit metadata block: {u8 keysize(+NUL), key, u8 type, u32 size, data}*. */
static tptex_status parse_meta_block(tptex_texture* t, uint64_t pos, uint32_t zipsize, uint32_t memsize) {
  uint8_t* buf;
  size_t n;
  const uint8_t *p, *end;
  tptex_status st;
  if ((st = check_block_size(t, memsize)) != TPTEX_OK) return st;
  n = (size_t)memsize;
  buf = (uint8_t*)TALLOC(t, n);
  if (!buf) return TPTEX_E_NOMEM;
  st = read_zip(t, pos, zipsize, buf, n);
  p = buf;
  end = buf + n;
  while (st == TPTEX_OK && p < end) {
    size_t keysize, avail;
    uint8_t type;
    uint32_t datasize;
    keysize = *p++;
    avail = (size_t)(end - p);
    if (keysize == 0u || keysize + 1u + 4u > avail) { st = TPTEX_E_CORRUPT; break; }
    {
      const uint8_t* key = p;
      p += keysize;
      type = *p++;
      datasize = tptex__ld_u32(p);
      p += 4;
      if ((size_t)(end - p) < datasize) { st = TPTEX_E_CORRUPT; break; }
      st = meta_add(t, key, keysize - 1u, type, datasize, p, 0, 0, 0);
      p += datasize;
    }
  }
  TFREE(t, buf, n);
  return st;
}

static tptex_status parse_lmd_headers(tptex_texture* t) {
  uint8_t* buf;
  size_t n;
  const uint8_t *p, *end;
  uint64_t pos;
  tptex_status st;
  if ((st = check_block_size(t, t->lmdheadermemsize)) != TPTEX_OK) return st;
  n = (size_t)t->lmdheadermemsize;
  buf = (uint8_t*)TALLOC(t, n);
  if (!buf) return TPTEX_E_NOMEM;
  st = read_zip(t, t->lmdheaderpos, t->lmdheaderzipsize, buf, n);
  p = buf;
  end = buf + n;
  pos = t->lmdheaderpos;
  if (st == TPTEX_OK && !tptex__add_u64(pos, t->lmdheaderzipsize, &pos)) st = TPTEX_E_OVERFLOW;
  while (st == TPTEX_OK && p < end) {
    size_t keysize, avail;
    uint8_t type;
    uint32_t datasize, zipsize;
    keysize = *p++;
    avail = (size_t)(end - p);
    if (keysize == 0u || keysize + 1u + 8u > avail) { st = TPTEX_E_CORRUPT; break; }
    {
      const uint8_t* key = p;
      p += keysize;
      type = *p++;
      datasize = tptex__ld_u32(p);
      zipsize = tptex__ld_u32(p + 4);
      p += 8;
      st = meta_add(t, key, keysize - 1u, type, datasize, NULL, 1, pos, zipsize);
      if (st == TPTEX_OK && !tptex__add_u64(pos, zipsize, &pos)) st = TPTEX_E_OVERFLOW;
    }
  }
  TFREE(t, buf, n);
  return st;
}

static tptex_status meta_load(tptex_texture* t) {
  size_t i;
  tptex_status st = TPTEX_OK;
  if (t->meta_loaded) return TPTEX_OK;
  if (t->metadatamemsize) st = parse_meta_block(t, t->metadatapos, t->metadatazipsize, t->metadatamemsize);
  if (st == TPTEX_OK && t->lmdheadermemsize) st = parse_lmd_headers(t);
  for (i = 0; st == TPTEX_OK && i < t->nmetaedits; ++i)
    st = parse_meta_block(t, t->metaedits[i].pos, t->metaedits[i].zipsize, t->metaedits[i].memsize);
  if (st != TPTEX_OK) { meta_free(t); t->meta_bytes = 0; return st; }
  t->meta_loaded = 1;
  return TPTEX_OK;
}

tptex_status tptex_meta_count(tptex_texture* t, int* count) {
  tptex_status st;
  if (!t || !count) return TPTEX_E_INVALID_ARG;
  if ((st = meta_load(t)) != TPTEX_OK) return st;
  *count = (int)t->nmeta;
  return TPTEX_OK;
}

tptex_status tptex_meta_key(tptex_texture* t, int index, const char** key, tptex_meta_type* type) {
  tptex_status st;
  if (!t || !key || !type) return TPTEX_E_INVALID_ARG;
  if ((st = meta_load(t)) != TPTEX_OK) return st;
  if (index < 0 || (size_t)index >= t->nmeta) return TPTEX_E_RANGE;
  *key = t->meta[index].key;
  *type = (tptex_meta_type)t->meta[index].type;
  return TPTEX_OK;
}

tptex_status tptex_meta_find(tptex_texture* t, const char* key, int* index, tptex_meta_type* type) {
  size_t i, klen;
  tptex_status st;
  if (!t || !key || !index || !type) return TPTEX_E_INVALID_ARG;
  if ((st = meta_load(t)) != TPTEX_OK) return st;
  klen = strlen(key);
  for (i = 0; i < t->nmeta; ++i)
    if (t->meta[i].keylen == klen && memcmp(t->meta[i].key, key, klen) == 0) {
      *index = (int)i;
      *type = (tptex_meta_type)t->meta[i].type;
      return TPTEX_OK;
    }
  *index = -1;
  return TPTEX_E_NOT_FOUND;
}

tptex_status tptex_meta_value(tptex_texture* t, int index, const void** data, int* count) {
  meta_entry* e;
  tptex_status st;
  size_t esz;
  if (!t || !data || !count) return TPTEX_E_INVALID_ARG;
  if ((st = meta_load(t)) != TPTEX_OK) return st;
  if (index < 0 || (size_t)index >= t->nmeta) return TPTEX_E_RANGE;
  e = &t->meta[index];
  if (e->is_lmd && !e->data) { /* large metadata: read on first access */
    uint8_t* buf;
    if (t->meta_bytes + e->datasize > t->limits.max_meta_bytes) return TPTEX_E_LIMIT;
    if ((st = check_block_size(t, e->datasize)) != TPTEX_OK) return st;
    buf = (uint8_t*)TALLOC(t, e->datasize);
    if (!buf) return TPTEX_E_NOMEM;
    st = read_zip(t, e->lmd_pos, e->lmd_zipsize, buf, e->datasize);
    if (st != TPTEX_OK) { TFREE(t, buf, e->datasize); return st; }
    tptex__le_to_host(buf, e->datasize, meta_elem_size(e->type));
    e->data = buf;
    t->meta_bytes += e->datasize;
  }
  esz = meta_elem_size(e->type);
  *data = e->data;
  *count = (int)(e->datasize / esz);
  return TPTEX_OK;
}
