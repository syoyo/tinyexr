/*
 * TinyEXR v3 (pure-C11) fuzz harness.
 *
 * Exercises every decode entry point on the same bytes:
 *   1. high-level exr_load_from_memory()
 *   2. mid-level reader: parse_header + read every part
 *   3. streaming source path (full synchronous feed)
 *
 * Build (coverage-guided):  make fuzz       -> build/fuzz_v3
 * Build (corpus replay):    make fuzz-corpus -> build/fuzz_replay <files...>
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct mem_source {
    const uint8_t *data;
    size_t size;
    int always_block;
};

#define FUZZ_ALLOC_BUDGET (64u << 20)
typedef union fuzz_alloc_header {
    max_align_t align;
    size_t size;
} fuzz_alloc_header;
typedef struct fuzz_alloc_state {
    size_t live;
    size_t calls;
    size_t fail_at;
} fuzz_alloc_state;
static size_t g_fail_at_override;

static void *fuzz_alloc(void *user, size_t size) {
    fuzz_alloc_state *s = (fuzz_alloc_state *)user;
    fuzz_alloc_header *h;
    if (++s->calls == s->fail_at || size > FUZZ_ALLOC_BUDGET - s->live ||
        size > SIZE_MAX - sizeof(*h))
        return NULL;
    h = (fuzz_alloc_header *)malloc(sizeof(*h) + size);
    if (!h) return NULL;
    h->size = size;
    s->live += size;
    return h + 1;
}

static void fuzz_free(void *user, void *ptr) {
    fuzz_alloc_state *s = (fuzz_alloc_state *)user;
    fuzz_alloc_header *h;
    if (!ptr) return;
    h = ((fuzz_alloc_header *)ptr) - 1;
    s->live -= h->size;
    free(h);
}

static exr_result feed_read(void *user, uint64_t offset, uint64_t len,
                            void *dst) {
    struct mem_source *m = (struct mem_source *)user;
    if (m->always_block) return EXR_WOULD_BLOCK;
    if (offset > m->size || len > m->size - offset) return EXR_ERROR_CORRUPT;
    if (len) memcpy(dst, m->data + (size_t)offset, (size_t)len);
    return EXR_SUCCESS;
}

/* Retry the same operation after supplying only its requested range. */
static int fuzz_supply(exr_reader *r, const uint8_t *file, size_t file_size) {
    exr_pending_read pr;
    size_t step;
    if (exr_reader_pending(r, &pr) != EXR_SUCCESS || pr.offset > file_size ||
        pr.size > file_size - (size_t)pr.offset || !pr.size) return 0;
    step = pr.size > 4096 ? 4096 : (size_t)pr.size;
    return exr_reader_supply(r, pr.offset, file + (size_t)pr.offset, step) == EXR_SUCCESS;
}
#define RETRY_READ(expr) do { \
    do { \
        rc = (expr); \
        if (rc == EXR_WOULD_BLOCK && !fuzz_supply(r, file, file_size)) { \
            rc = EXR_ERROR_CORRUPT; break; \
        } \
    } while (rc == EXR_WOULD_BLOCK); \
} while (0)

/* Block-iterate one part: geometry + per-block decode into a bounded buffer. */
static void drain_blocks(exr_reader *r, int part, const uint8_t *file, size_t file_size) {
    exr_result rc;
    const exr_header *h = exr_reader_part_header(r, part);
    uint32_t n = 0, i;
    if (!EXR_OK(exr_reader_num_blocks(r, part, &n))) return;
    for (i = 0; i < n; ++i) {
        exr_block_info bi;
        if (!EXR_OK(exr_reader_block_info(r, part, i, &bi))) continue;
        if (bi.is_deep) {
            size_t npix;
            int32_t *counts;
            exr_buffer *planes;
            uint64_t total = 0;
            int c;
            if (!h || bi.width <= 0 || bi.height <= 0 ||
                (size_t)bi.width > (1u << 20) / (size_t)bi.height)
                continue;
            npix = (size_t)bi.width * (size_t)bi.height;
            counts = (int32_t *)calloc(npix, sizeof(*counts));
            if (!counts) continue;
            RETRY_READ(exr_reader_decode_deep_counts(r, part, i, counts, npix, &total));
            if (rc != EXR_SUCCESS) {
                free(counts); continue;
            }
            planes = (exr_buffer *)calloc((size_t)h->num_channels, sizeof(*planes));
            if (planes && total < FUZZ_ALLOC_BUDGET) {
                for (c = 0; c < h->num_channels; ++c) {
                    size_t ps = h->channels[c].pixel_type == EXR_PIXEL_HALF ? 2u : 4u;
                    if (total > FUZZ_ALLOC_BUDGET / ps) break;
                    planes[c].size = (size_t)total * ps;
                    planes[c].data = malloc(planes[c].size ? planes[c].size : 1);
                    if (!planes[c].data) break;
                }
                if (c == h->num_channels) {
                    RETRY_READ(exr_reader_decode_deep_samples(
                        r, part, i, planes, (size_t)h->num_channels));
                }
                for (c = 0; c < h->num_channels; ++c) free(planes[c].data);
            }
            free(planes);
            free(counts);
            continue;
        }
        if (bi.uncompressed_size == 0 || bi.uncompressed_size > (64u << 20))
            continue;
        {
            uint8_t *blk = (uint8_t *)malloc((size_t)bi.uncompressed_size);
            if (!blk) return;
            RETRY_READ(exr_reader_decode_block(r, part, i, blk, bi.uncompressed_size));
            if (rc == EXR_SUCCESS && h && h->num_channels > 0) {
                void *plane = malloc(bi.uncompressed_size);
                if (plane) {
                    (void)exr_block_extract_channel(
                        h, &bi, blk, bi.uncompressed_size,
                        (int32_t)(i % (uint32_t)h->num_channels), plane,
                        bi.uncompressed_size);
                    free(plane);
                }
            }
            free(blk);
        }
    }
}

static void drain_reader(exr_reader *r, const exr_allocator *a,
                           const uint8_t *file, size_t file_size) {
    int np, p;
    exr_result rc;
    RETRY_READ(exr_reader_parse_header(r));
    if (rc != EXR_SUCCESS) {
        (void)exr_reader_parse_header(r); /* terminal parse must be idempotent */
        return;
    }
    (void)exr_reader_parse_header(r);
    np = exr_reader_num_parts(r);
    for (p = 0; p < np; ++p) {
        exr_part out;
        memset(&out, 0, sizeof(out));
        RETRY_READ(exr_reader_read_part(r, p, &out));
        if (rc == EXR_SUCCESS) {
            if (!out.is_deep && (uint64_t)out.width * (uint64_t)out.height *
                (uint32_t)out.header.num_channels < (1u << 20)) {
                float *pixels = NULL;
                (void)exr_part_to_rgba_float(a, &out, &pixels, NULL, NULL, NULL);
                if (pixels) a->free(a->user, pixels);
            }
            exr_part_free(a, &out);
        }
        {
            const exr_header *h = exr_reader_part_header(r, p);
            if (h && h->part_type == EXR_PART_SCANLINE) {
                memset(&out, 0, sizeof(out));
                RETRY_READ(exr_reader_read_scanlines(r, p, h->data_window.min_y, 1, &out));
                if (rc == EXR_SUCCESS) exr_part_free(a, &out);
            } else if (h && h->part_type == EXR_PART_TILED) {
                exr_block_info bi;
                if (EXR_OK(exr_reader_block_info(r, p, 0, &bi))) {
                    memset(&out, 0, sizeof(out));
                    RETRY_READ(exr_reader_read_tile(r, p, bi.tile_x, bi.tile_y,
                                                    bi.level_x, bi.level_y, &out));
                    if (rc == EXR_SUCCESS) exr_part_free(a, &out);
                }
            }
        }
        drain_blocks(r, p, file, file_size);
    }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    fuzz_alloc_state state;
    exr_allocator alloc;
    memset(&state, 0, sizeof(state));
    state.fail_at = g_fail_at_override ? g_fail_at_override
                                       : (size ? (size_t)(data[0] & 63u) : 0);
    alloc.user = &state;
    alloc.alloc = fuzz_alloc;
    alloc.free = fuzz_free;
    /* 1. high-level load (all parts, all channels). */
    {
        exr_image img;
        memset(&img, 0, sizeof(img));
        if (EXR_OK(exr_load_from_memory(data, size, &alloc, &img)))
            exr_image_free(&img);
    }

    /* 2. mid-level reader over the same bytes (zero-copy memory path). */
    {
        exr_reader *r = NULL;
        if (EXR_OK(exr_reader_open_memory(data, size, &alloc, &r)) && r) {
            drain_reader(r, &alloc, data, size);
            exr_reader_close(r);
        }
    }

    /* 3. streaming source path (synchronous range reads). */
    if (size > 0) {
        struct mem_source m;
        exr_data_source ds;
        exr_reader *r = NULL;
        m.data = data;
        m.size = size;
        m.always_block = 0;
        ds.user = &m;
        ds.read = feed_read;
        ds.total_size = (uint64_t)size;
        if (EXR_OK(exr_reader_open_source(&ds, &alloc, &r)) && r) {
            drain_reader(r, &alloc, data, size);
            exr_reader_close(r);
        }
    }
    /* 4. Suspend/resume source. Supply the requested range in short prefixes
     * so pending offset/size updates and repeated WOULD_BLOCK are exercised. */
    if (size > 0) {
        struct mem_source m;
        exr_data_source ds;
        exr_reader *r = NULL;
        m.data = data; m.size = size; m.always_block = 1;
        ds.user = &m; ds.read = feed_read; ds.total_size = (uint64_t)size;
        if (EXR_OK(exr_reader_open_source(&ds, &alloc, &r)) && r) {
            drain_reader(r, &alloc, data, size);
            exr_reader_close(r);
        }
    }
    return 0;
}

#ifdef EXR_FUZZ_STANDALONE
#include <stdio.h>
#include <stdlib.h>

/* Deterministic replay over a list of files (CI corpus check). */
int main(int argc, char **argv) {
    int i, failed = 0, ran = 0;
    for (i = 1; i < argc; ++i) {
        FILE *fp = fopen(argv[i], "rb");
        long n;
        uint8_t *buf;
        if (!fp) { fprintf(stderr, "  FAIL (open): %s\n", argv[i]); failed = 1; continue; }
        if (fseek(fp, 0, SEEK_END) != 0) { fclose(fp); failed = 1; continue; }
        n = ftell(fp);
        if (n < 0 || fseek(fp, 0, SEEK_SET) != 0) { fclose(fp); failed = 1; continue; }
        buf = (uint8_t *)malloc((size_t)n ? (size_t)n : 1);
        if (!buf || (n && fread(buf, 1, (size_t)n, fp) != (size_t)n)) {
            free(buf); fclose(fp); failed = 1; continue;
        }
        fclose(fp);
        g_fail_at_override = 0;
        LLVMFuzzerTestOneInput(buf, (size_t)n);
        for (size_t fail_at = 1; fail_at <= 8; ++fail_at) {
            g_fail_at_override = fail_at;
            LLVMFuzzerTestOneInput(buf, (size_t)n);
        }
        g_fail_at_override = 0;
        free(buf);
        ran++;
        printf("  ok (no crash): %s\n", argv[i]);
    }
    printf("fuzz corpus replay: %d file(s), no crash / no sanitizer error\n",
           ran);
    return failed ? 1 : 0;
}
#endif
