/*
 * TinyEXR - range-source, ownership and hostile-geometry regressions.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr_internal.h"
#include <stdio.h>
#include <stdlib.h>
#if defined(EXR_USE_THREADS)
#include <threads.h>
#include <time.h>
#endif

static int failed, passed;
#define REQUIRE(c) do { if (!(c)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #c); ++failed; return; } } while (0)
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #c); ++failed; } else ++passed; } while (0)

typedef struct stats { size_t live, peak, calls, fail_at, wrong; volatile long lock; } stats;
static void stats_lock(stats *s) { exr_input_lock(&s->lock); }
static void stats_unlock(stats *s) { exr_input_unlock(&s->lock); }
typedef union allocation { max_align_t align; struct { stats *owner; size_t size; } v; } allocation;
static void *tracked_alloc(void *u, size_t n) {
    stats *s = (stats *)u;
    allocation *p;
    stats_lock(s);
    if (++s->calls == s->fail_at || n > SIZE_MAX - sizeof(*p)) {
        stats_unlock(s); return NULL;
    }
    stats_unlock(s);
    p = (allocation *)malloc(sizeof(*p) + n);
    if (!p) return NULL;
    p->v.owner = s; p->v.size = n;
    stats_lock(s); s->live += n;
    if (s->live > s->peak) s->peak = s->live;
    stats_unlock(s);
    return p + 1;
}
static void tracked_free(void *u, void *ptr) {
    stats *s = (stats *)u;
    allocation *p;
    if (!ptr) return;
    p = (allocation *)ptr - 1;
    if (p->v.owner != s) { stats_lock(s); ++s->wrong; stats_unlock(s); }
    stats_lock(p->v.owner); p->v.owner->live -= p->v.size; stats_unlock(p->v.owner);
    free(p);
}

typedef struct source {
    const uint8_t *bytes;
    size_t size, requests, max_request;
    uint64_t tail, total, stop_after;
    size_t chunk_offset;
    int blocking, error;
#if defined(EXR_USE_THREADS)
    uint64_t delay_after;
    thrd_t owner;
    int delayed, wrong_thread;
#endif
} source;

static exr_result source_copy(source *s, uint64_t off, size_t len, void *dst) {
    if (off > s->total || len > s->total - off) return EXR_ERROR_CORRUPT;
    if (!s->tail) {
        if (off > s->size || len > s->size - (size_t)off) return EXR_ERROR_CORRUPT;
        memcpy(dst, s->bytes + (size_t)off, len);
    } else {
        size_t i;
        for (i = 0; i < len; ++i) {
            uint64_t at = off + i;
            ((uint8_t *)dst)[i] = at < s->chunk_offset ? s->bytes[(size_t)at] :
                at >= s->tail && at - s->tail < s->size - s->chunk_offset ?
                s->bytes[s->chunk_offset + (size_t)(at - s->tail)] : 0;
        }
    }
    return EXR_SUCCESS;
}
static exr_result source_read(void *u, uint64_t off, uint64_t len, void *dst) {
    source *s = (source *)u;
    ++s->requests;
#if defined(EXR_USE_THREADS)
    if (s->delayed) {
        if (!thrd_equal(s->owner, thrd_current())) ++s->wrong_thread;
        if (off >= s->delay_after) {
            struct timespec delay = {0, 20000000};
            (void)thrd_sleep(&delay, NULL);
        }
    }
#endif
    if (len > s->max_request) s->max_request = (size_t)len;
    if (s->error && (!s->stop_after || off >= s->stop_after)) return EXR_ERROR_IO;
    if (s->blocking && (!s->stop_after || off >= s->stop_after)) return EXR_WOULD_BLOCK;
    if (len > SIZE_MAX) return EXR_ERROR_LIMIT_EXCEEDED;
    return source_copy(s, off, (size_t)len, dst);
}
static exr_result supply(exr_reader *r, source *s, size_t step) {
    exr_pending_read p;
    uint8_t bytes[65536];
    exr_result rc = exr_reader_pending(r, &p);
    size_t n;
    if (rc != EXR_SUCCESS) return rc;
    n = p.size < step ? (size_t)p.size : step;
    if (n > sizeof(bytes)) n = sizeof(bytes);
    rc = source_copy(s, p.offset, n, bytes);
    if (rc != EXR_SUCCESS) return rc;
    return exr_reader_supply(r, p.offset, bytes, n);
}
static exr_result drive_part(exr_reader *r, source *s, int part, exr_part *out, size_t step) {
    exr_result rc;
    size_t attempts = 0;
    do {
        rc = exr_reader_read_part(r, part, out);
        if (rc != EXR_WOULD_BLOCK) return rc;
        if (out->images || out->deep_images || out->header.channels) return EXR_ERROR_CORRUPT;
        rc = supply(r, s, step);
        if (rc != EXR_SUCCESS) return rc;
    } while (++attempts < 1000000);
    return EXR_ERROR_CORRUPT;
}
static exr_result drive_header(exr_reader *r, source *s, size_t step) {
    exr_result rc;
    size_t tries = 0;
    while ((rc = exr_reader_parse_header(r)) == EXR_WOULD_BLOCK) {
        rc = supply(r, s, step);
        if (rc != EXR_SUCCESS) return rc;
        if (++tries > 1000000) return EXR_ERROR_CORRUPT;
    }
    return rc;
}

static int parts_equal(const exr_part *a, const exr_part *b) {
    int c;
    size_t n;
    if (a->width != b->width || a->height != b->height || a->is_deep != b->is_deep ||
        a->header.num_channels != b->header.num_channels) return 0;
    n = (size_t)a->width * a->height;
    if (a->is_deep) {
        if (a->deep_total_samples != b->deep_total_samples ||
            memcmp(a->deep_sample_counts, b->deep_sample_counts, n * sizeof(int32_t))) return 0;
        n = (size_t)a->deep_total_samples;
    }
    for (c = 0; c < a->header.num_channels; ++c) {
        size_t bytes = n * exr_pixel_size(a->header.channels[c].pixel_type);
        if (strcmp(a->header.channels[c].name, b->header.channels[c].name) ||
            memcmp(a->is_deep ? a->deep_images[c] : a->images[c],
                   b->is_deep ? b->deep_images[c] : b->images[c], bytes)) return 0;
    }
    return 1;
}

static exr_result fixture(exr_image *img, int np, int w, int h, int tiled, int deep, int levels) {
    int p, c;
    size_t i, n = (size_t)w * h;
    float *rgb = (float *)malloc(n * 3 * sizeof(float));
    exr_result rc = EXR_SUCCESS;
    memset(img, 0, sizeof(*img)); img->alloc = *exr_default_allocator();
    if (!rgb) return EXR_ERROR_OUT_OF_MEMORY;
    for (i = 0; i < n * 3; ++i) rgb[i] = (float)(i % 79) * 0.125f;
    img->parts = (exr_part *)calloc((size_t)np, sizeof(exr_part));
    if (!img->parts) { free(rgb); return EXR_ERROR_OUT_OF_MEMORY; }
    img->num_parts = np;
    for (p = 0; p < np; ++p) {
        exr_part *pt = &img->parts[p];
        rc = exr_rgba_float_to_part(NULL, rgb, w, h, 3, EXR_PIXEL_FLOAT, pt);
        if (rc != EXR_SUCCESS) break;
        pt->header.name[0] = (char)('a' + p); pt->header.name[1] = 0;
        if (tiled) {
            pt->header.part_type = EXR_PART_TILED; pt->header.tiled = 1;
            pt->header.tile_x_size = 3; pt->header.tile_y_size = 7;
            pt->header.level_mode = (exr_tile_level_mode)levels;
        }
        if (deep) {
            uint64_t total = 0;
            for (c = 0; c < 3; ++c) free(pt->images[c]);
            free(pt->images); pt->images = NULL;
            pt->is_deep = 1;
            pt->header.part_type = tiled ? EXR_PART_DEEP_TILED : EXR_PART_DEEP_SCANLINE;
            pt->deep_sample_counts = (int32_t *)calloc(n, sizeof(int32_t));
            pt->deep_images = (void **)calloc(3, sizeof(void *));
            if (!pt->deep_sample_counts || !pt->deep_images) { rc = EXR_ERROR_OUT_OF_MEMORY; break; }
            for (i = 0; i < n; ++i) { pt->deep_sample_counts[i] = (int32_t)(i % 4); total += i % 4; }
            pt->deep_total_samples = total;
            for (c = 0; c < 3; ++c) {
                float *samples = (float *)malloc((size_t)total * sizeof(float));
                if (!samples) { rc = EXR_ERROR_OUT_OF_MEMORY; break; }
                pt->deep_images[c] = samples;
                for (i = 0; i < (size_t)total; ++i) samples[i] = (float)(i + c) * 0.25f;
            }
        }
    }
    free(rgb);
    return rc;
}

static void cold_job(void *u, int i) {
    const uint16_t *e, *l;
    uint32_t *hash = (uint32_t *)u, v = 2166136261u;
    size_t j;
    exr_b44_debug_tables(&e, &l);
    for (j = 0; j < 65536; ++j) v = (v ^ e[j] ^ l[j]) * 16777619u;
    hash[i] = v;
}
static void cold_b44(void) {
    uint32_t hashes[8] = {0};
    int i;
    exr_parallel_for(8, 8, cold_job, hashes);
    for (i = 0; i < 8; ++i) CHECK(hashes[i] && hashes[i] == hashes[0]);
}

static void block_source_parity(exr_reader *r, source *src, const uint8_t *data, size_t size) {
    exr_reader *memory = NULL;
    int part;
    REQUIRE(exr_reader_open_memory(data, size, NULL, &memory) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(memory) == EXR_SUCCESS);
    for (part = 0; part < exr_reader_num_parts(memory); ++part) {
        const exr_header *h = exr_reader_part_header(memory, part);
        uint32_t n, k;
        REQUIRE(exr_reader_num_blocks(memory, part, &n) == EXR_SUCCESS);
        for (k = n; k > 0; --k) {
            exr_block_info bi;
            exr_result rc;
            REQUIRE(exr_reader_block_info(memory, part, k - 1, &bi) == EXR_SUCCESS);
            if (!bi.is_deep) {
                void *a = malloc(bi.uncompressed_size ? bi.uncompressed_size : 1);
                void *b = malloc(bi.uncompressed_size ? bi.uncompressed_size : 1);
                REQUIRE(a && b);
                REQUIRE(exr_reader_decode_block(memory, part, k - 1, a, bi.uncompressed_size) == EXR_SUCCESS);
                do {
                    rc = exr_reader_decode_block(r, part, k - 1, b, bi.uncompressed_size);
                    if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, src, 7) == EXR_SUCCESS);
                } while (rc == EXR_WOULD_BLOCK);
                CHECK(rc == EXR_SUCCESS && memcmp(a, b, bi.uncompressed_size) == 0);
                free(a); free(b);
                if (bi.is_tiled) {
                    exr_part pa = {0}, pb = {0};
                    REQUIRE(exr_reader_read_tile(memory, part, bi.tile_x, bi.tile_y,
                                                 bi.level_x, bi.level_y, &pa) == EXR_SUCCESS);
                    do {
                        rc = exr_reader_read_tile(r, part, bi.tile_x, bi.tile_y,
                                                  bi.level_x, bi.level_y, &pb);
                        if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, src, 3) == EXR_SUCCESS);
                    } while (rc == EXR_WOULD_BLOCK);
                    CHECK(rc == EXR_SUCCESS && parts_equal(&pa, &pb));
                    CHECK(pb.header.data_window.min_x == bi.x0 && pb.header.data_window.min_y == bi.y0);
                    exr_part_free(NULL, &pa); exr_part_free(&r->alloc, &pb);
                }
            } else {
                size_t npix = (size_t)bi.width * bi.height;
                int32_t *a = (int32_t *)calloc(npix, sizeof(*a));
                int32_t *b = (int32_t *)calloc(npix, sizeof(*b));
                uint64_t ta = 0, tb = 0;
                exr_buffer *pa = (exr_buffer *)calloc(h->num_channels, sizeof(*pa));
                exr_buffer *pb = (exr_buffer *)calloc(h->num_channels, sizeof(*pb));
                int c;
                REQUIRE(a && b && pa && pb);
                REQUIRE(exr_reader_decode_deep_counts(memory, part, k - 1, a, npix, &ta) == EXR_SUCCESS);
                do {
                    rc = exr_reader_decode_deep_counts(r, part, k - 1, b, npix, &tb);
                    if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, src, 3) == EXR_SUCCESS);
                } while (rc == EXR_WOULD_BLOCK);
                CHECK(rc == EXR_SUCCESS && ta == tb && memcmp(a, b, npix * sizeof(*a)) == 0);
                for (c = 0; c < h->num_channels; ++c) {
                    pa[c].size = pb[c].size = (size_t)ta * exr_pixel_size(h->channels[c].pixel_type);
                    pa[c].data = malloc(pa[c].size ? pa[c].size : 1);
                    pb[c].data = malloc(pb[c].size ? pb[c].size : 1);
                    REQUIRE(pa[c].data && pb[c].data);
                }
                REQUIRE(exr_reader_decode_deep_samples(memory, part, k - 1, pa, h->num_channels) == EXR_SUCCESS);
                do {
                    rc = exr_reader_decode_deep_samples(r, part, k - 1, pb, h->num_channels);
                    if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, src, 11) == EXR_SUCCESS);
                } while (rc == EXR_WOULD_BLOCK);
                CHECK(rc == EXR_SUCCESS);
                for (c = 0; c < h->num_channels; ++c) {
                    CHECK(memcmp(pa[c].data, pb[c].data, pa[c].size) == 0);
                    free(pa[c].data); free(pb[c].data);
                }
                free(pa); free(pb); free(a); free(b);
            }
        }
    }
    exr_reader_close(memory);
}

static void source_matrix(void) {
    static const exr_compression codecs[] = {EXR_COMPRESSION_NONE, EXR_COMPRESSION_RLE,
        EXR_COMPRESSION_ZIPS, EXR_COMPRESSION_ZIP, EXR_COMPRESSION_PIZ,
        EXR_COMPRESSION_PXR24, EXR_COMPRESSION_B44, EXR_COMPRESSION_B44A, EXR_COMPRESSION_ZSTD};
    int shape, ci, block;
    for (shape = 0; shape < 8; ++shape) for (ci = 0; ci < (int)(sizeof(codecs)/sizeof(codecs[0])); ++ci) {
        int deep = shape >= 4;
        exr_image img = {0}, reference = {0};
        void *data = NULL;
        size_t size = 0;
        int tiled = shape & 1, levels = shape == 2 ? EXR_TILE_MIPMAP_LEVELS :
                                                  shape == 3 ? EXR_TILE_RIPMAP_LEVELS : EXR_TILE_ONE_LEVEL;
        if (shape == 2 || shape == 3) tiled = 1;
        if (deep && codecs[ci] != EXR_COMPRESSION_NONE && codecs[ci] != EXR_COMPRESSION_RLE &&
            codecs[ci] != EXR_COMPRESSION_ZIPS && codecs[ci] != EXR_COMPRESSION_ZIP &&
            codecs[ci] != EXR_COMPRESSION_ZSTD) continue;
        REQUIRE(fixture(&img, shape == 6 || shape == 7 ? 2 : 1, 7, 35, tiled, deep, levels) == EXR_SUCCESS);
        REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, codecs[ci]) == EXR_SUCCESS);
        REQUIRE(exr_load_from_memory(data, size, NULL, &reference) == EXR_SUCCESS);
        for (block = 0; block < 2; ++block) {
            stats st = {0};
            exr_allocator a = {&st, tracked_alloc, tracked_free};
            source src = {0};
            exr_data_source ds;
            exr_reader *r = NULL;
            int p;
            src.bytes = (const uint8_t *)data; src.size = size; src.total = size; src.blocking = block;
            ds.user = &src; ds.read = source_read; ds.total_size = size;
            REQUIRE(exr_reader_open_source(&ds, &a, &r) == EXR_SUCCESS);
            for (p = 0; p < reference.num_parts; ++p) {
                exr_part out = {0};
                REQUIRE(drive_part(r, &src, p, &out, 1) == EXR_SUCCESS);
                CHECK(parts_equal(&out, &reference.parts[p]));
                exr_part_free(&a, &out);
            }
            if (block) block_source_parity(r, &src, (const uint8_t *)data, size);
            CHECK(src.max_request <= 65536);
            exr_reader_close(r); CHECK(st.live == 0 && st.wrong == 0);
        }
        {
            exr_image file = {0};
            REQUIRE(exr_save_to_file("build/_range_source_test.exr", &img, codecs[ci]) == EXR_SUCCESS);
            REQUIRE(exr_load_from_file("build/_range_source_test.exr", NULL, &file) == EXR_SUCCESS);
            for (block = 0; block < reference.num_parts; ++block)
                CHECK(parts_equal(&file.parts[block], &reference.parts[block]));
            exr_image_free(&file);
        }
        exr_image_free(&img); exr_image_free(&reference); free(data);
    }
}

static void allocator_and_geometry(void) {
    stats ca = {0}, oa = {0};
    exr_allocator ac = {&ca, tracked_alloc, tracked_free}, ao = {&oa, tracked_alloc, tracked_free};
    exr_context *ctx = NULL;
    exr_image img = {0}, back = {0};
    void *data = NULL;
    size_t size = 0;
    int round, c;
    REQUIRE(fixture(&img, 1, 16, 35, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_PIZ) == EXR_SUCCESS);
    REQUIRE(exr_context_create(&ac, &ctx) == EXR_SUCCESS);
    exr_set_num_threads(1);
    for (round = 0; round < 2; ++round) {
        REQUIRE(exr_load_from_memory_ctx(ctx, data, size, &ao, &back) == EXR_SUCCESS);
        exr_image_free(&back);
    }
    CHECK(oa.live == 0 && ca.live > 0);
    exr_context_destroy(ctx); ctx = NULL;
    CHECK(ca.live == 0 && ca.wrong == 0 && oa.wrong == 0);
    free(data); data = NULL;
    for (round = 0; round < 2; ++round) {
        exr_part *p = &img.parts[0];
        p->header.data_window.min_x = round ? INT32_MIN : INT32_MAX - p->width + 1;
        p->header.data_window.max_x = p->header.data_window.min_x + (p->width - 1);
        p->header.data_window.min_y = round ? INT32_MIN : INT32_MAX - p->height + 1;
        p->header.data_window.max_y = p->header.data_window.min_y + (p->height - 1);
        p->header.display_window = p->header.data_window;
        for (c = 0; c < 8; ++c) {
            REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, (exr_compression)c) == EXR_SUCCESS);
            REQUIRE(exr_load_from_memory(data, size, NULL, &back) == EXR_SUCCESS);
            CHECK(back.parts[0].width == p->width && back.parts[0].height == p->height);
            exr_image_free(&back); free(data); data = NULL;
        }
    }
    exr_image_free(&img);
}

static void malformed_rows(void) {
    exr_image img = {0}, out = {0};
    void *data = NULL;
    size_t size = 0;
    exr_reader *r = NULL;
    uint64_t off;
    REQUIRE(fixture(&img, 1, 2, 2, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    off = r->parts[0].offsets[1]; exr_reader_close(r);
    exr_wr_i32((uint8_t *)data + (size_t)off, 0);
    CHECK(exr_load_from_memory(data, size, NULL, &out) == EXR_ERROR_CORRUPT);
    exr_set_num_threads(4);
    CHECK(exr_load_from_memory(data, size, NULL, &out) == EXR_ERROR_CORRUPT);
    exr_set_num_threads(1);
    CHECK(!out.parts);
    /* A forged payload size must fail before allocating its claimed bytes. */
    {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        source src = {0};
        exr_data_source ds;
        exr_part part = {0};
        exr_wr_i32((uint8_t *)data + (size_t)off, 1);
        exr_wr_i32((uint8_t *)data + (size_t)off + 4, INT32_MAX);
        src.bytes = data; src.size = size; src.total = size;
        ds.user = &src; ds.read = source_read; ds.total_size = size;
        REQUIRE(exr_reader_open_source(&ds, &a, &r) == EXR_SUCCESS);
        REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
        CHECK(exr_reader_read_part(r, 0, &part) == EXR_ERROR_CORRUPT);
        CHECK(!part.images && !part.header.channels);
        CHECK(st.peak < 65536);
        exr_reader_close(r);
        CHECK(st.live == 0);
    }
    free(data); exr_image_free(&img);
}

static void deep_spectral(void) {
    exr_image img = {0};
    exr_spectral_image cube = {0};
    void *data = NULL;
    size_t size = 0;
    REQUIRE(fixture(&img, 1, 2, 2, 0, 1, 0) == EXR_SUCCESS);
    memcpy(img.parts[0].header.channels[0].name, "S0.550,000000nm", 15);
    REQUIRE(exr_header_set_string_attribute(NULL, &img.parts[0].header, "spectralLayoutVersion", "1.0") == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_ZIPS) == EXR_SUCCESS);
    CHECK(exr_spectral_load_from_memory(data, size, NULL, &cube) == EXR_ERROR_UNSUPPORTED);
    CHECK(!cube.wavelengths && !cube.stokes[0]);
    free(data); exr_image_free(&img);
}

static void large_offsets_and_bounds(void) {
    exr_image img = {0};
    exr_reader *r = NULL;
    exr_context *ctx = NULL;
    uint8_t *data = NULL;
    size_t size = 0, table;
    uint64_t original;
    stats st = {0};
    exr_allocator a = {&st, tracked_alloc, tracked_free};
    source src = {0};
    exr_data_source ds;
    exr_block_info bi;
    float canonical[3] = {0};
    exr_result rc;
    REQUIRE(fixture(&img, 1, 1, 1, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory((void **)&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    original = r->parts[0].offsets[0]; table = r->header_end;
    exr_reader_close(r); r = NULL;
    src.bytes = data; src.size = size; src.chunk_offset = (size_t)original;
    src.tail = (UINT64_C(5) << 30) + 123;
    src.total = src.tail + size - src.chunk_offset; src.blocking = 1;
    exr_wr_u64(data + table, src.tail);
    ds.user = &src; ds.read = source_read; ds.total_size = src.total;
    REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
    REQUIRE(exr_context_set_max_file_bytes(ctx, 0) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_source_ctx(ctx, &ds, &a, &r) == EXR_SUCCESS);
    CHECK(st.peak < 32768);
    REQUIRE(drive_header(r, &src, 17) == EXR_SUCCESS);
    REQUIRE(exr_reader_block_info(r, 0, 0, &bi) == EXR_SUCCESS);
    do {
        rc = exr_reader_decode_block(r, 0, 0, canonical, sizeof(canonical));
        if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, &src, 3) == EXR_SUCCESS);
    } while (rc == EXR_WOULD_BLOCK);
    CHECK(rc == EXR_SUCCESS);
    CHECK(canonical[0] == 0.25f && canonical[1] == 0.125f && canonical[2] == 0.0f);
    CHECK(st.peak < 65536 && src.max_request <= 65536 && src.requests < 16);
    exr_reader_close(r); r = NULL;
    CHECK(st.live == 0);
    exr_context_destroy(ctx); exr_image_free(&img); free(data);

    REQUIRE(fixture(&img, 1, 128, 512, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory((void **)&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    memset(&src, 0, sizeof(src)); memset(&st, 0, sizeof(st));
    src.bytes = data; src.size = size; src.total = size;
    ds.user = &src; ds.total_size = size;
    REQUIRE(exr_reader_open_source(&ds, &a, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    {
        uint32_t n, i;
        REQUIRE(exr_reader_num_blocks(r, 0, &n) == EXR_SUCCESS);
        for (i = n; i > 0; --i) {
            uint8_t *pixels;
            REQUIRE(exr_reader_block_info(r, 0, i - 1, &bi) == EXR_SUCCESS);
            pixels = (uint8_t *)malloc(bi.uncompressed_size);
            REQUIRE(pixels != NULL);
            rc = exr_reader_decode_block(r, 0, i - 1, pixels, bi.uncompressed_size);
            free(pixels);
            REQUIRE(rc == EXR_SUCCESS);
        }
    }
    CHECK(st.peak < size / 4);
    printf("bounded source: %zu file bytes, %zu peak library bytes\n", size, st.peak);
    exr_reader_close(r); CHECK(st.live == 0);
    exr_image_free(&img); free(data);
}

static void source_failures(void) {
    exr_image img = {0};
    uint8_t *data = NULL;
    size_t size = 0, at;
    source src = {0};
    exr_data_source ds;
    REQUIRE(fixture(&img, 1, 7, 35, 1, 1, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory((void **)&data, &size, NULL, &img, EXR_COMPRESSION_ZIPS) == EXR_SUCCESS);
    src.bytes = data; src.size = size; src.total = size; src.blocking = 1;
    ds.user = &src; ds.read = source_read; ds.total_size = size;
    for (at = 1; at <= 140; ++at) {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        exr_reader *r = NULL;
        exr_part p = {0};
        exr_result rc;
        st.fail_at = at;
        rc = exr_reader_open_source(&ds, &a, &r);
        if (rc == EXR_SUCCESS) rc = drive_part(r, &src, 0, &p, 31);
        CHECK(rc == EXR_SUCCESS || rc == EXR_ERROR_OUT_OF_MEMORY);
        exr_part_free(&a, &p); exr_reader_close(r);
        CHECK(st.live == 0 && st.wrong == 0);
    }
    {
        exr_reader *r = NULL;
        exr_pending_read p;
        uint8_t byte = 0;
        REQUIRE(exr_reader_open_source(&ds, NULL, &r) == EXR_SUCCESS);
        REQUIRE(exr_reader_parse_header(r) == EXR_WOULD_BLOCK);
        REQUIRE(exr_reader_pending(r, &p) == EXR_SUCCESS);
        CHECK(exr_reader_supply(r, p.offset + 1, &byte, 1) == EXR_ERROR_INVALID_ARGUMENT);
        CHECK(exr_reader_supply(r, p.offset, &byte, 0) == EXR_ERROR_INVALID_ARGUMENT);
        CHECK(exr_reader_supply(r, p.offset, &byte, (size_t)p.size + 1) == EXR_ERROR_INVALID_ARGUMENT);
        exr_reader_close(r); /* Closing while a metadata supply is pending. */
    }
    {
        exr_reader *r = NULL;
        src.blocking = 0; src.error = 1;
        REQUIRE(exr_reader_open_source(&ds, NULL, &r) == EXR_SUCCESS);
        CHECK(exr_reader_parse_header(r) == EXR_ERROR_IO);
        src.error = 0;
        CHECK(exr_reader_parse_header(r) == EXR_ERROR_IO);
        exr_reader_close(r);
    }
    {
        int mode;
        for (mode = 0; mode < 2; ++mode) {
            stats st = {0};
            exr_allocator a = {&st, tracked_alloc, tracked_free};
            exr_reader *r = NULL;
            exr_part out = {0};
            exr_result rc;
            src.blocking = 0; src.error = 0; src.stop_after = 0;
            REQUIRE(exr_reader_open_source(&ds, &a, &r) == EXR_SUCCESS);
            REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
            src.stop_after = r->parts[0].offsets[1];
            src.blocking = !mode; src.error = mode;
            exr_set_num_threads(4);
            rc = exr_reader_read_part(r, 0, &out);
            CHECK(rc == (mode ? EXR_ERROR_IO : EXR_WOULD_BLOCK));
            CHECK(!out.header.channels && !out.deep_images && !out.deep_sample_counts);
            exr_reader_close(r); /* Includes prefetched chunk and private output. */
            CHECK(st.live == 0 && st.wrong == 0);
            exr_set_num_threads(1);
        }
    }
    exr_image_free(&img); free(data);
}

static void crop_conversion(void) {
    exr_image img = {0};
    void *data = NULL;
    size_t size = 0;
    exr_reader *r = NULL;
    exr_part crop = {0};
    float *rgba = NULL;
    int c;
    REQUIRE(fixture(&img, 1, 4, 4, 0, 0, 0) == EXR_SUCCESS);
    /* All three native planes have a 2x2 sampled grid, sorted BY, RY, Y. */
    memcpy(img.parts[0].header.channels[0].name, "BY", 3);
    memcpy(img.parts[0].header.channels[1].name, "RY", 3);
    memcpy(img.parts[0].header.channels[2].name, "Y", 2);
    for (c = 0; c < 3; ++c) {
        img.parts[0].header.channels[c].x_sampling = 2;
        img.parts[0].header.channels[c].y_sampling = 2;
    }
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_ZIP) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_read_scanlines(r, 0, 1, 1, &crop) == EXR_SUCCESS);
    CHECK(crop.header.data_window.min_y == 1 && crop.header.data_window.max_y == 1 && crop.height == 1);
    CHECK(exr_part_to_rgba_float(NULL, &crop, &rgba, NULL, NULL, NULL) == EXR_ERROR_UNSUPPORTED && !rgba);
    CHECK(exr_part_yc_to_rgba_float(NULL, &crop, &rgba, NULL, NULL) == EXR_ERROR_UNSUPPORTED && !rgba);
    exr_part_free(NULL, &crop);
    REQUIRE(exr_reader_read_scanlines(r, 0, 1, 3, &crop) == EXR_SUCCESS);
    REQUIRE(exr_part_to_rgba_float(NULL, &crop, &rgba, NULL, NULL, NULL) == EXR_SUCCESS);
    /* Row 2 is the only sampled row; its values extend to both crop edges. */
    CHECK(rgba[0] == ((float *)img.parts[0].images[0])[2]);
    CHECK(rgba[3 * 4 * 2] == rgba[0]);
    {
        exr_attribute at;
        CHECK(exr_header_find_attribute(&crop.header, "dataWindow", &at) == EXR_SUCCESS &&
              exr_rd_i32((const uint8_t *)at.data + 4) == 1);
    }
    free(rgba); rgba = NULL; exr_part_free(NULL, &crop); exr_reader_close(r); r = NULL;
    {
        source src = {0}; exr_data_source ds;
        exr_result rc;
        src.bytes = (const uint8_t *)data; src.size = size; src.total = size; src.blocking = 1;
        ds.user = &src; ds.read = source_read; ds.total_size = size;
        REQUIRE(exr_reader_open_source(&ds, NULL, &r) == EXR_SUCCESS);
        do {
            rc = exr_reader_read_scanlines(r, 0, 1, 1, &crop);
            if (rc == EXR_WOULD_BLOCK) REQUIRE(supply(r, &src, 1) == EXR_SUCCESS);
        } while (rc == EXR_WOULD_BLOCK);
        REQUIRE(rc == EXR_SUCCESS);
        CHECK(exr_part_to_rgba_float(NULL, &crop, &rgba, NULL, NULL, NULL) == EXR_ERROR_UNSUPPORTED && !rgba);
        exr_part_free(NULL, &crop); exr_reader_close(r);
    }
    exr_image_free(&img); free(data);
}

typedef struct sink_stat { uint64_t position, high; int writes, closes; } sink_stat;
static exr_result sink_write_test(void *u, const void *p, size_t n) {
    sink_stat *s = (sink_stat *)u; (void)p;
    s->position += n; if (s->position > s->high) s->high = s->position;
    ++s->writes; return EXR_SUCCESS;
}
static exr_result sink_seek_test(void *u, uint64_t off) { ((sink_stat *)u)->position = off; return EXR_SUCCESS; }
static exr_result sink_close_test(void *u) { ++((sink_stat *)u)->closes; return EXR_SUCCESS; }

static void writer_limits_and_names(void) {
    exr_image img = {0}, back = {0};
    exr_context *ctx = NULL;
    exr_writer *w = NULL;
    void *data = NULL;
    size_t size = 0, good_size;
    int i;
    REQUIRE(fixture(&img, 2, 2, 2, 0, 0, 0) == EXR_SUCCESS);
    memcpy(img.parts[0].header.name, "part0", 6); img.parts[1].header.name[0] = 0;
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    REQUIRE(exr_load_from_memory(data, size, NULL, &back) == EXR_SUCCESS);
    CHECK(strcmp(back.parts[0].header.name, "part0") == 0 && strcmp(back.parts[1].header.name, "part1") == 0);
    CHECK(img.parts[1].header.name[0] == 0);
    exr_image_free(&back); free(data); data = NULL;
    memcpy(img.parts[1].header.name, "part0", 6);
    CHECK(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_INVALID_ARGUMENT && !data && !size);
    img.parts[1].header.name[0] = 0;
    REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory_ctx(ctx, &data, &good_size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    free(data); data = NULL;
    REQUIRE(exr_context_set_max_file_bytes(ctx, good_size - 1) == EXR_SUCCESS);
    CHECK(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_LIMIT_EXCEEDED && !data && !size);
    REQUIRE(exr_context_set_max_file_bytes(ctx, good_size) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    CHECK(size == good_size); free(data); data = NULL;
    REQUIRE(exr_context_set_max_image_bytes(ctx, 95) == EXR_SUCCESS);
    CHECK(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_LIMIT_EXCEEDED);
    REQUIRE(exr_context_set_max_image_bytes(ctx, 96) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    free(data); data = NULL;
    REQUIRE(exr_context_set_max_header_bytes(ctx, 8) == EXR_SUCCESS);
    {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        st.fail_at = 1;
        CHECK(exr_save_to_memory_ctx(ctx, &data, &size, &a, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_LIMIT_EXCEEDED);
        CHECK(st.calls == 0 && !data && size == 0);
    }
    CHECK(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_LIMIT_EXCEEDED);
    {
        sink_stat ss = {0};
        exr_data_sink sink = {&ss, sink_write_test, sink_seek_test, sink_close_test};
        REQUIRE(exr_writer_create_ctx(ctx, NULL, &w) == EXR_SUCCESS);
        for (i = 0; i < img.num_parts; ++i) REQUIRE(exr_writer_add_part(w, &img.parts[i].header, NULL) == EXR_SUCCESS);
        CHECK(exr_writer_begin_stream(w, &sink, EXR_COMPRESSION_NONE) == EXR_ERROR_LIMIT_EXCEEDED);
        CHECK(ss.writes == 0 && ss.closes == 0);
        exr_writer_destroy(w); w = NULL;
    }
    exr_context_destroy(ctx); exr_image_free(&img);
}

static void metadata_and_large_chunk(void) {
    exr_image img = {0};
    void *data = NULL;
    size_t size = 0, metadata;
    exr_reader *r = NULL;
    exr_context *ctx = NULL;
    source src = {0};
    exr_data_source ds;
    REQUIRE(fixture(&img, 1, 1, 9000, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    metadata = r->metadata_end; exr_reader_close(r); r = NULL;
    src.bytes = (const uint8_t *)data; src.size = size; src.total = size; src.blocking = 1;
    ds.user = &src; ds.read = source_read; ds.total_size = size;
    REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
    REQUIRE(exr_context_set_max_header_bytes(ctx, metadata) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_source_ctx(ctx, &ds, NULL, &r) == EXR_SUCCESS);
    REQUIRE(drive_header(r, &src, 4093) == EXR_SUCCESS);
    CHECK(r->metadata_end == metadata && r->parts[0].num_chunks == 9000);
    CHECK(src.max_request <= 65536);
    exr_reader_close(r); r = NULL;
    REQUIRE(exr_context_set_max_header_bytes(ctx, metadata - 1) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_source_ctx(ctx, &ds, NULL, &r) == EXR_SUCCESS);
    CHECK(drive_header(r, &src, 4093) == EXR_ERROR_LIMIT_EXCEEDED);
    CHECK(exr_reader_parse_header(r) == EXR_ERROR_LIMIT_EXCEEDED);
    exr_reader_close(r); exr_context_destroy(ctx); ctx = NULL;
    free(data); data = NULL; exr_image_free(&img);

    REQUIRE(fixture(&img, 1, 256, 256, 1, 0, 0) == EXR_SUCCESS);
    img.parts[0].header.tile_x_size = img.parts[0].header.tile_y_size = 256;
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    memset(&src, 0, sizeof(src)); src.bytes = (const uint8_t *)data;
    src.size = size; src.total = size; src.blocking = 1;
    ds.total_size = size;
    REQUIRE(exr_reader_open_source(&ds, NULL, &r) == EXR_SUCCESS);
    {
        exr_part part = {0};
        exr_image reference = {0};
        REQUIRE(exr_load_from_memory(data, size, NULL, &reference) == EXR_SUCCESS);
        REQUIRE(drive_part(r, &src, 0, &part, 4093) == EXR_SUCCESS);
        CHECK(parts_equal(&part, &reference.parts[0]));
        exr_image_free(&reference);
        CHECK(src.max_request == 65536);
        exr_part_free(NULL, &part);
    }
    exr_reader_close(r); free(data); exr_image_free(&img);
}

static void context_failure_reuse(void) {
    exr_image img = {0};
    void *data = NULL;
    size_t size = 0, fail_at;
    REQUIRE(fixture(&img, 1, 16, 35, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_PIZ) == EXR_SUCCESS);
    for (fail_at = 1; fail_at <= 32; ++fail_at) {
        stats cs = {0}, os = {0};
        exr_allocator ca = {&cs, tracked_alloc, tracked_free}, oa = {&os, tracked_alloc, tracked_free};
        exr_context *ctx = NULL;
        exr_image back = {0};
        exr_result rc;
        cs.fail_at = fail_at;
        rc = exr_context_create(&ca, &ctx);
        if (rc == EXR_SUCCESS) {
            rc = exr_load_from_memory_ctx(ctx, data, size, &oa, &back);
            exr_image_free(&back);
            cs.fail_at = 0;
            CHECK(exr_load_from_memory_ctx(ctx, data, size, &oa, &back) == EXR_SUCCESS);
            exr_image_free(&back);
        }
        exr_context_destroy(ctx);
        CHECK(cs.live == 0 && os.live == 0 && cs.wrong == 0 && os.wrong == 0);
    }
    free(data); exr_image_free(&img);
}

static void encode_limit_matrix(void) {
    int shape, codec;
    for (shape = 0; shape < 6; ++shape) for (codec = 0; codec < 2; ++codec) {
        exr_image img = {0};
        exr_context *ctx = NULL;
        void *data = NULL;
        size_t size = 0, good_size;
        exr_compression comp = codec ? EXR_COMPRESSION_ZIPS : EXR_COMPRESSION_NONE;
        REQUIRE(fixture(&img, 1, 7, 35, shape != 0 && shape != 4,
                         shape >= 4, shape == 2 ? EXR_TILE_MIPMAP_LEVELS :
                                     shape == 3 ? EXR_TILE_RIPMAP_LEVELS : EXR_TILE_ONE_LEVEL) == EXR_SUCCESS);
        REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
        REQUIRE(exr_save_to_memory_ctx(ctx, &data, &good_size, NULL, &img, comp) == EXR_SUCCESS);
        free(data); data = NULL;
        REQUIRE(exr_context_set_max_file_bytes(ctx, good_size - 1) == EXR_SUCCESS);
        CHECK(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, comp) == EXR_ERROR_LIMIT_EXCEEDED);
        CHECK(!data && size == 0);
        REQUIRE(exr_context_set_max_file_bytes(ctx, good_size) == EXR_SUCCESS);
        CHECK(exr_save_to_memory_ctx(ctx, &data, &size, NULL, &img, comp) == EXR_SUCCESS && size == good_size);
        free(data); exr_context_destroy(ctx); exr_image_free(&img);
    }
    {
        exr_image img = {0};
        exr_writer *w = NULL;
        exr_context *ctx = NULL;
        sink_stat ss = {0};
        exr_data_sink sink = {&ss, sink_write_test, sink_seek_test, sink_close_test};
        exr_const_buffer planes[3];
        int c, y;
        REQUIRE(fixture(&img, 1, 2, 2, 0, 0, 0) == EXR_SUCCESS);
        REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
        REQUIRE(exr_writer_create_ctx(ctx, NULL, &w) == EXR_SUCCESS);
        REQUIRE(exr_writer_add_part(w, &img.parts[0].header, NULL) == EXR_SUCCESS);
        REQUIRE(exr_writer_begin_stream(w, &sink, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
        REQUIRE(exr_context_set_max_image_bytes(ctx, 23) == EXR_SUCCESS);
        for (c = 0; c < 3; ++c) { planes[c].data = img.parts[0].images[c]; planes[c].size = 8; }
        CHECK(exr_writer_write_scanline_block(w, 0, 0, planes, 3) == EXR_ERROR_LIMIT_EXCEEDED);
        REQUIRE(exr_context_set_max_image_bytes(ctx, 24) == EXR_SUCCESS);
        for (y = 0; y < 2; ++y) {
            for (c = 0; c < 3; ++c) planes[c].data = (float *)img.parts[0].images[c] + y * 2;
            REQUIRE(exr_writer_write_scanline_block(w, 0, y, planes, 3) == EXR_SUCCESS);
        }
        REQUIRE(exr_writer_end_stream(w) == EXR_SUCCESS);
        CHECK(ss.closes == 1);
        exr_writer_destroy(w); CHECK(ss.closes == 1);
        exr_context_destroy(ctx); exr_image_free(&img);
    }
}

static void tiled_sampling_rejected(void) {
    int mode, axis, origin, pt;
    for (mode = 0; mode < 3; ++mode)
        for (axis = 0; axis < 2; ++axis)
            for (origin = -3; origin <= 1; origin += 4)
                for (pt = EXR_PIXEL_UINT; pt <= EXR_PIXEL_FLOAT; ++pt) {
                    exr_image img = {0};
                    exr_part *p;
                    exr_writer *writer = NULL;
                    exr_mip_pyramid mip;
                    exr_ripmap_pyramid rip;
                    void *data = NULL;
                    size_t size = 0, n;
                    int c;
                    REQUIRE(fixture(&img, 1, 7, 7, 1, 0, mode) == EXR_SUCCESS);
                    p = &img.parts[0];
                    p->header.data_window.min_x = p->header.data_window.min_y = origin;
                    p->header.data_window.max_x = p->header.data_window.max_y = origin + 6;
                    n = (size_t)7 * exr_num_samples(origin, origin + 6, 2);
                    for (c = 0; c < 3; ++c) {
                        exr_channel *ch = &p->header.channels[c];
                        ch->pixel_type = (exr_pixel_type)pt;
                        if (axis) ch->y_sampling = 2; else ch->x_sampling = 2;
                        free(p->images[c]);
                        p->images[c] = calloc(n, exr_pixel_size(ch->pixel_type));
                        REQUIRE(p->images[c]);
                    }
                    CHECK(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_ERROR_INVALID_ARGUMENT);
                    CHECK(!data && !size);
                    REQUIRE(exr_writer_create(NULL, &writer) == EXR_SUCCESS);
                    CHECK(exr_writer_add_part(writer, &p->header, NULL) == EXR_ERROR_INVALID_ARGUMENT);
                    exr_writer_destroy(writer);
                    CHECK(exr_mip_generate(exr_default_allocator(), p, 0, &mip) == EXR_ERROR_UNSUPPORTED);
                    CHECK(!mip.img);
                    CHECK(exr_ripmap_generate(exr_default_allocator(), p, 0, &rip) == EXR_ERROR_UNSUPPORTED);
                    CHECK(!rip.img);
                    exr_image_free(&img);
                }
}

static void delayed_source(void) {
#if defined(EXR_USE_THREADS)
    exr_image img = {0}, reference = {0};
    exr_reader *r = NULL;
    exr_part part = {0};
    void *data = NULL;
    size_t size = 0;
    source src = {0};
    exr_data_source ds;
    struct timespec start, end;
    clock_t cpu;
    double wall, used;
    REQUIRE(fixture(&img, 1, 16, 12, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
    REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    src.delay_after = r->parts[0].offsets[4];
    exr_reader_close(r); r = NULL;
    src.bytes = data; src.size = size; src.total = size;
    src.delayed = 1; src.owner = thrd_current();
    REQUIRE(exr_load_from_memory(data, size, NULL, &reference) == EXR_SUCCESS);
    ds.user = &src; ds.read = source_read; ds.total_size = size;
    REQUIRE(exr_reader_open_source(&ds, NULL, &r) == EXR_SUCCESS);
    REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
    exr_set_num_threads(4);
    timespec_get(&start, TIME_UTC); cpu = clock();
    REQUIRE(exr_reader_read_part(r, 0, &part) == EXR_SUCCESS);
    used = (double)(clock() - cpu) / CLOCKS_PER_SEC;
    timespec_get(&end, TIME_UTC);
    wall = (double)(end.tv_sec - start.tv_sec) + (double)(end.tv_nsec - start.tv_nsec) * 1e-9;
    CHECK(parts_equal(&part, &reference.parts[0]));
    CHECK(!src.wrong_thread);
    CHECK(wall >= 0.25 && used < wall * 0.5 + 0.03);
    printf("delayed source: wall=%.3fs process_cpu=%.3fs\n", wall, used);
    exr_set_num_threads(1);
    exr_part_free(NULL, &part); exr_reader_close(r);
    exr_image_free(&img); exr_image_free(&reference); free(data);
#endif
}

#if defined(EXR_TEST_VIEWER)
int exrv_open(const uint8_t *, int);
void exrv_close(int);
int exrv_spectral_open_part(int, int);
int exrv_spectral_show(int, int);
float *exrv_rgba(int);
#endif

static void sparse_source_shapes(void) {
    int shape;
    for (shape = 0; shape < 3; ++shape) {
        exr_image img = {0};
        exr_part reference = {0}, out = {0};
        exr_reader *memory = NULL, *r = NULL;
        exr_context *ctx = NULL;
        uint8_t *data = NULL;
        size_t size = 0, table;
        uint32_t n, k;
        uint64_t first;
        source src = {0};
        exr_data_source ds;
        REQUIRE(fixture(&img, 1, 7, 35, shape == 1, shape == 2,
            shape == 1 ? EXR_TILE_RIPMAP_LEVELS : 0) == EXR_SUCCESS);
        REQUIRE(exr_save_to_memory((void **)&data, &size, NULL, &img, EXR_COMPRESSION_NONE) == EXR_SUCCESS);
        REQUIRE(exr_reader_open_memory(data, size, NULL, &memory) == EXR_SUCCESS);
        REQUIRE(exr_reader_parse_header(memory) == EXR_SUCCESS);
        REQUIRE(exr_reader_read_part(memory, 0, &reference) == EXR_SUCCESS);
        table = memory->header_end; n = memory->parts[0].num_chunks;
        first = memory->parts[0].offsets[0];
        for (k = 1; k < n; ++k) if (memory->parts[0].offsets[k] < first) first = memory->parts[0].offsets[k];
        src.bytes = data; src.size = size; src.chunk_offset = (size_t)first;
        src.tail = first + (UINT64_C(5) << 30);
        src.total = src.tail + size - (size_t)first; src.blocking = 1;
        for (k = 0; k < n; ++k)
            exr_wr_u64(data + table + (size_t)k * 8, memory->parts[0].offsets[k] + (UINT64_C(5) << 30));
        ds.user = &src; ds.read = source_read; ds.total_size = src.total;
        REQUIRE(exr_context_create(NULL, &ctx) == EXR_SUCCESS);
        REQUIRE(exr_context_set_max_file_bytes(ctx, 0) == EXR_SUCCESS);
        REQUIRE(exr_reader_open_source_ctx(ctx, &ds, NULL, &r) == EXR_SUCCESS);
        REQUIRE(drive_header(r, &src, 17) == EXR_SUCCESS);
        REQUIRE(drive_part(r, &src, 0, &out, 7) == EXR_SUCCESS);
        CHECK(parts_equal(&reference, &out));
        CHECK(src.max_request <= 65536);
        exr_part_free(NULL, &reference); exr_part_free(NULL, &out);
        exr_reader_close(memory); exr_reader_close(r); exr_context_destroy(ctx);
        free(data); exr_image_free(&img);
    }
}

static void piz_source_failures(void) {
    exr_image img = {0};
    void *data = NULL;
    size_t size = 0, at;
    source src = {0};
    exr_data_source ds;
    REQUIRE(fixture(&img, 1, 16, 70, 0, 0, 0) == EXR_SUCCESS);
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_PIZ) == EXR_SUCCESS);
    src.bytes = (const uint8_t *)data; src.size = size; src.total = size; src.blocking = 1;
    ds.user = &src; ds.read = source_read; ds.total_size = size;
    for (at = 1; at <= 120; ++at) {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        exr_reader *r = NULL;
        exr_part part = {0};
        exr_result rc;
        st.fail_at = at;
        rc = exr_reader_open_source(&ds, &a, &r);
        if (rc == EXR_SUCCESS) rc = drive_part(r, &src, 0, &part, 37);
        CHECK(rc == EXR_SUCCESS || rc == EXR_ERROR_OUT_OF_MEMORY);
        if (rc != EXR_SUCCESS) CHECK(!part.images && !part.header.channels);
        exr_part_free(&a, &part); exr_reader_close(r);
        CHECK(!st.live && !st.wrong);
    }
    {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        exr_reader *r = NULL;
        exr_part part = {0};
        src.blocking = 0;
        REQUIRE(exr_reader_open_source(&ds, &a, &r) == EXR_SUCCESS);
        REQUIRE(exr_reader_parse_header(r) == EXR_SUCCESS);
        src.blocking = 1; src.stop_after = r->parts[0].offsets[1];
        CHECK(exr_reader_read_part(r, 0, &part) == EXR_WOULD_BLOCK);
        CHECK(!part.images && !part.header.channels);
        exr_reader_close(r);
        CHECK(!st.live && !st.wrong);
    }
    free(data); exr_image_free(&img);
}

static void multipart_spectral(void) {
    exr_image img = {0};
    exr_spectral_image cube = {0};
    void *data = NULL;
    size_t size = 0;
    int p, c;
    REQUIRE(fixture(&img, 3, 3, 2, 0, 0, 0) == EXR_SUCCESS);
    for (p = 1; p < 3; ++p) {
        for (c = 0; c < 3; ++c) {
            size_t i;
            exr_spectral_channel_name(img.parts[p].header.channels[c].name, EXR_MAX_NAME,
                p == 1 ? EXR_SPECTRUM_EMISSIVE : EXR_SPECTRUM_REFLECTIVE, 0, 450.0f + c * 50);
            for (i = 0; i < 6; ++i) ((float *)img.parts[p].images[c])[i] = (float)(p * 10 + c);
        }
        REQUIRE(exr_spectral_set_attributes(NULL, &img.parts[p].header,
            p == 1 ? EXR_SPECTRUM_EMISSIVE : EXR_SPECTRUM_REFLECTIVE, "test-units") == EXR_SUCCESS);
    }
    REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_ZIP) == EXR_SUCCESS);
    CHECK(exr_spectral_load_from_memory(data, size, NULL, &cube) == EXR_SUCCESS);
    CHECK(cube.type == EXR_SPECTRUM_EMISSIVE && cube.num_wavelengths == 3 && cube.width == 3 && cube.height == 2);
    CHECK(exr_spectral_sample(&cube, 0, 2, 1, 1) == 12.0f);
    exr_spectral_image_free(&cube);
    CHECK(exr_spectral_load_part_from_memory(data, size, 2, NULL, &cube) == EXR_SUCCESS);
    CHECK(cube.type == EXR_SPECTRUM_REFLECTIVE && strcmp(cube.units, "test-units") == 0);
    CHECK(exr_spectral_sample(&cube, 0, 0, 0, 0) == 20.0f);
    exr_spectral_image_free(&cube);
    CHECK(exr_spectral_load_part_from_memory(data, size, 0, NULL, &cube) == EXR_ERROR_UNSUPPORTED);
    CHECK(!cube.stokes[0] && !cube.wavelengths);
    CHECK(exr_spectral_load_part_from_memory(data, size, 3, NULL, &cube) == EXR_ERROR_INVALID_ARGUMENT);
    CHECK(exr_spectral_load_part_from_memory(data, size, -2, NULL, &cube) == EXR_ERROR_INVALID_ARGUMENT);
    REQUIRE(exr_save_to_file("build/_spectral_parts.exr", &img, EXR_COMPRESSION_ZIP) == EXR_SUCCESS);
    CHECK(exr_spectral_load_part_from_file("build/_spectral_parts.exr", 2, NULL, &cube) == EXR_SUCCESS);
    CHECK(exr_spectral_sample(&cube, 0, 1, 2, 1) == 21.0f);
    exr_spectral_image_free(&cube);
#if defined(EXR_TEST_VIEWER)
    {
        int handle = exrv_open((const uint8_t *)data, (int)size);
        REQUIRE(handle > 0);
        CHECK(exrv_spectral_open_part(handle, 1) == 3);
        CHECK(exrv_spectral_show(handle, 0) == 1 && exrv_rgba(handle)[0] == 10.0f);
        CHECK(exrv_spectral_open_part(handle, 2) == 3);
        CHECK(exrv_spectral_show(handle, 2) == 1 && exrv_rgba(handle)[0] == 22.0f);
        CHECK(exrv_spectral_open_part(handle, 0) < 0);
        exrv_close(handle);
    }
#endif
    for (c = 1; c < 100; ++c) {
        stats st = {0};
        exr_allocator a = {&st, tracked_alloc, tracked_free};
        exr_result rc;
        st.fail_at = (size_t)c;
        rc = exr_spectral_load_part_from_memory(data, size, 2, &a, &cube);
        CHECK(rc == EXR_SUCCESS || rc == EXR_ERROR_OUT_OF_MEMORY);
        if (rc != EXR_SUCCESS) CHECK(!cube.stokes[0] && !cube.wavelengths);
        exr_spectral_image_free(&cube);
        CHECK(!st.live && !st.wrong);
    }
    free(data); exr_image_free(&img);
}

#if defined(EXR_TEST_VIEWER)
int exrv_open(const uint8_t *, int);
void exrv_close(int);
int exrv_select_ycc(int, int, int, int);
int exrv_level_width(int);
int exrv_level_height(int);
float *exrv_rgba(int);
int exrv_spectral_open_part(int, int);
float *exrv_spectral_wavelengths(int);
static void viewer_levels(void) {
    int mode, rounding;
    for (mode = EXR_TILE_ONE_LEVEL; mode <= EXR_TILE_RIPMAP_LEVELS; ++mode)
        for (rounding = 0; rounding < 2; ++rounding) {
            exr_image img = {0};
            exr_reader *r = NULL;
            void *data = NULL;
            size_t size = 0, i;
            uint32_t n, k;
            int h, c;
            const char *names[] = {"Y", "RY", "BY"};
            const float values[] = {2.0f, 0.5f, 0.25f};
            REQUIRE(fixture(&img, 1, 9, 7, 1, 0, mode) == EXR_SUCCESS);
            img.parts[0].header.rounding_mode = (exr_tile_rounding_mode)rounding;
            img.parts[0].header.data_window.min_x = -3; img.parts[0].header.data_window.max_x = 5;
            img.parts[0].header.data_window.min_y = 1; img.parts[0].header.data_window.max_y = 7;
            for (c = 0; c < 3; ++c) {
                strcpy(img.parts[0].header.channels[c].name, names[c]);
                for (i = 0; i < 63; ++i) ((float *)img.parts[0].images[c])[i] = values[c];
            }
            REQUIRE(exr_save_to_memory(&data, &size, NULL, &img, EXR_COMPRESSION_ZIP) == EXR_SUCCESS);
            REQUIRE(exr_reader_open_memory(data, size, NULL, &r) == EXR_SUCCESS);
            REQUIRE(exr_reader_num_blocks(r, 0, &n) == EXR_SUCCESS);
            h = exrv_open((const uint8_t *)data, (int)size); REQUIRE(h > 0);
            for (k = 0; k < n; ++k) {
                exr_block_info bi;
                float *rgba;
                int w, ht;
                REQUIRE(exr_reader_block_info(r, 0, k, &bi) == EXR_SUCCESS);
                if (bi.tile_x || bi.tile_y) continue;
                CHECK(exrv_select_ycc(h, 0, bi.level_x, bi.level_y) > 0);
                w = exrv_level_width(h); ht = exrv_level_height(h);
                CHECK(w > 0 && ht > 0);
                rgba = exrv_rgba(h); REQUIRE(rgba);
                for (i = 0; i < (size_t)w * ht; ++i) {
                    float expected_g = (2.0f - 3.0f * 0.2126f - 2.5f * 0.0722f) / 0.7152f;
                    float delta = rgba[i*4+1] - expected_g;
                    CHECK(rgba[i*4] == 3.0f && rgba[i*4+2] == 2.5f && rgba[i*4+3] == 1.0f && delta > -0.0001f && delta < 0.0001f);
                }
            }
            CHECK(exrv_select_ycc(h, 0, 99, 99) < 0);
            exrv_close(h); exr_reader_close(r); free(data); exr_image_free(&img);
        }
}
#endif

int main(void) {
#if defined(__EMSCRIPTEN__)
    CHECK(sizeof(void *) == 4 && sizeof(size_t) == 4);
    printf("WASM32: exercising sparse offsets above 4 GiB\n");
#endif
    cold_b44();
    multipart_spectral();
    sparse_source_shapes();
    piz_source_failures();
#if defined(EXR_TEST_VIEWER)
    viewer_levels();
#endif
    tiled_sampling_rejected();
    delayed_source();
    exr_set_num_threads(4);
    source_matrix();
    exr_set_num_threads(1);
    allocator_and_geometry();
    malformed_rows();
    deep_spectral();
    large_offsets_and_bounds();
    source_failures();
    crop_conversion();
    writer_limits_and_names();
    metadata_and_large_chunk();
    context_failure_reuse();
    encode_limit_matrix();
    printf("streaming/hardening: %d passed, %d failed\n", passed, failed);
    return failed ? 1 : 0;
}
