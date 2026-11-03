/*
 * TinyEXR - resumable materialization over bounded source batches.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr_internal.h"

#define SOURCE_BATCH_CAP 64

typedef struct source_job {
    uint8_t *data;
    size_t size;
    uint8_t *scratch;
    size_t scratch_size;
    uint32_t index;
    exr_block_info bi;
    exr_result rc;
    uint64_t total;
} source_job;

typedef struct source_operation {
    exr_part output;
    int32_t part, x, y, lx, ly;
    int kind, pass, width, height;
    int batch_width, batch_count;
    uint32_t next, end;
    size_t owned;
    uint64_t total, *prefix;
    source_job jobs[SOURCE_BATCH_CAP];
    exr_reader *reader;
    exr_context *codec_context;
    exr_wait_queue *queue;
    int queue_open, queue_next, queue_left, stop, warmed;
    exr_result result;
} source_operation;

void exr_source_operation_free(exr_reader *r) {
    source_operation *op = (source_operation *)r->read_operation;
    int i;
    if (!op) return;
    for (i = 0; i < SOURCE_BATCH_CAP; ++i) {
        exr_free(&r->alloc, op->jobs[i].data);
        exr_free(&r->alloc, op->jobs[i].scratch);
    }
    exr_part_free(&r->alloc, &op->output);
    exr_free(&r->alloc, op->prefix);
    exr_wait_queue_free(&r->alloc, op->queue);
    exr_context_destroy(op->codec_context);
    exr_free(&r->alloc, op); r->read_operation = NULL;
}

static exr_result source_owned(source_operation *op, size_t bytes) {
    size_t next;
    uint64_t limit = exr_reader_image_limit(op->reader);
    if (exr_add_ovf(op->owned, bytes, &next) || (limit && (uint64_t)next > limit))
        return EXR_ERROR_LIMIT_EXCEEDED;
    op->owned = next; return EXR_SUCCESS;
}

static exr_result source_init(exr_reader *r, int32_t part, int kind,
                              int32_t x, int32_t y, int32_t lx, int32_t ly) {
    source_operation *op;
    exr_int_part *p = &r->parts[part];
    exr_header *h = &p->header;
    exr_result rc;
    size_t npix, ptrbytes;
    int deep = h->part_type == EXR_PART_DEEP_SCANLINE || h->part_type == EXR_PART_DEEP_TILED;
    exr_box2i crop = h->data_window;
    uint32_t first = 0, end = p->num_chunks;
    if (kind == 1) {
        int lpb = exr_lines_per_block(h->compression);
        if (y <= 0 || x < crop.min_y || (int64_t)x + y - 1 > crop.max_y)
            return EXR_ERROR_INVALID_ARGUMENT;
        crop.min_y = x; crop.max_y = x + (y - 1);
        first = (uint32_t)((x - h->data_window.min_y) / lpb);
        end = (uint32_t)((crop.max_y - h->data_window.min_y) / lpb) + 1;
    } else if (kind == 2) {
        exr_block_info bi;
        uint32_t k;
        rc = exr_reader_tile_index(p, x, y, lx, ly, &k);
        if (rc != EXR_SUCCESS) return rc;
        rc = exr_reader_block_info(r, part, k, &bi);
        if (rc != EXR_SUCCESS) return rc;
        crop.min_x = bi.x0; crop.min_y = bi.y0;
        crop.max_x = bi.x0 + (bi.width - 1); crop.max_y = bi.y0 + (bi.height - 1);
        first = k; end = k + 1;
    }
    op = (source_operation *)exr_calloc(&r->alloc, 1, sizeof(*op));
    if (!op) return EXR_ERROR_OUT_OF_MEMORY;
    r->read_operation = op;
    op->reader = r; op->part = part; op->kind = kind;
    op->x = x; op->y = y; op->lx = lx; op->ly = ly;
    op->next = first; op->end = end;
    op->width = crop.max_x - crop.min_x + 1;
    op->height = crop.max_y - crop.min_y + 1;
    op->batch_width = exr_get_num_threads();
    if (op->batch_width < 1) op->batch_width = 1;
    if (op->batch_width > SOURCE_BATCH_CAP) op->batch_width = SOURCE_BATCH_CAP;
    if ((uint32_t)op->batch_width > end - first) op->batch_width = (int)(end - first);
    if (op->batch_width < 1) op->batch_width = 1;
    if (op->batch_width > 1) op->queue = exr_wait_queue_create(&r->alloc);
    if (!op->queue) op->batch_width = 1;
    /* Serial file/source reads otherwise rebuild PIZ's large Huffman tables
     * for every chunk. A private context reuses bounded codec scratch for this
     * operation without changing ownership of a caller-supplied context. */
    if (!r->context && h->compression == EXR_COMPRESSION_PIZ &&
        exr_get_num_threads() <= 1) {
        rc = exr_context_create(&r->alloc, &op->codec_context);
        if (rc != EXR_SUCCESS) return rc;
    }
    rc = exr_header_copy(&r->alloc, &op->output.header, h);
    if (rc != EXR_SUCCESS) return rc;
    rc = exr_header_crop(&r->alloc, &op->output.header, crop);
    if (rc != EXR_SUCCESS) return rc;
    op->output.width = op->width; op->output.height = op->height;
    op->output.is_deep = (uint8_t)deep;
    if (exr_mul_ovf((size_t)op->width, (size_t)op->height, &npix) ||
        exr_mul_ovf((size_t)h->num_channels, sizeof(void *), &ptrbytes))
        return EXR_ERROR_LIMIT_EXCEEDED;
    rc = source_owned(op, ptrbytes);
    if (rc != EXR_SUCCESS) return rc;
    if (deep) {
        size_t bytes;
        if (exr_mul_ovf(npix, sizeof(int32_t), &bytes)) return EXR_ERROR_LIMIT_EXCEEDED;
        rc = source_owned(op, bytes);
        if (rc != EXR_SUCCESS) return rc;
        op->output.deep_sample_counts = (int32_t *)exr_calloc(&r->alloc, npix, sizeof(int32_t));
        op->output.deep_images = (void **)exr_calloc(&r->alloc, h->num_channels, sizeof(void *));
        if (!op->output.deep_sample_counts || !op->output.deep_images)
            return EXR_ERROR_OUT_OF_MEMORY;
    } else {
        /* Planes share one block when small enough (see exr_flat_planes_alloc).
         * The pointer array was charged above; charge the padded planes. */
        size_t total;
        rc = exr_flat_planes_size(h, crop.min_x, crop.min_y, op->width,
                                  op->height, &total);
        if (rc != EXR_SUCCESS) return EXR_ERROR_LIMIT_EXCEEDED;
        rc = source_owned(op, total - ptrbytes);
        if (rc != EXR_SUCCESS) return rc;
        rc = exr_flat_planes_alloc(&r->alloc, h, crop.min_x, crop.min_y,
                                   op->width, op->height, &op->output);
        if (rc != EXR_SUCCESS) return rc;
    }
    return EXR_SUCCESS;
}

static exr_result scatter_flat(source_operation *op, const source_job *j,
                                const uint8_t *data) {
    const exr_header *h = &op->output.header;
    const exr_block_info *bi = &j->bi;
    size_t off = 0;
    int line, c;
    for (line = 0; line < bi->height; ++line) {
        int yy = bi->y0 + line;
        for (c = 0; c < h->num_channels; ++c) {
            const exr_channel *v = &h->channels[c];
            int nx, cw, row, col;
            size_t bytes;
            if (yy % v->y_sampling) continue;
            nx = exr_num_samples(bi->x0, (int64_t)bi->x0 + bi->width - 1, v->x_sampling);
            if (exr_mul_ovf((size_t)nx, exr_pixel_size(v->pixel_type), &bytes) ||
                off > bi->uncompressed_size || bytes > bi->uncompressed_size - off)
                return EXR_ERROR_CORRUPT;
            if (bytes && yy >= h->data_window.min_y && yy <= h->data_window.max_y) {
                cw = exr_num_samples(h->data_window.min_x, h->data_window.max_x, v->x_sampling);
                row = exr_num_samples(h->data_window.min_y, yy, v->y_sampling) - 1;
                col = exr_num_samples(h->data_window.min_x, (int64_t)bi->x0 - 1, v->x_sampling);
                if (row < 0 || col < 0 || col > cw || nx > cw - col) return EXR_ERROR_CORRUPT;
                memcpy((uint8_t *)op->output.images[c] + ((size_t)row * cw + col) * exr_pixel_size(v->pixel_type),
                       data + off, bytes);
            }
            off += bytes;
        }
    }
    return off == bi->uncompressed_size ? EXR_SUCCESS : EXR_ERROR_CORRUPT;
}

static void source_job_run(void *user, int index) {
    source_operation *op = (source_operation *)user;
    source_job *j = &op->jobs[index];
    exr_reader shadow = *op->reader;
    const exr_header *h = &op->output.header;
    const exr_allocator *a = &shadow.alloc;
    int c, yy, xx;
    size_t npix, k = 0;
    shadow.kind = EXR_SRC_CHUNK;
    if (op->codec_context) shadow.context = op->codec_context;
    shadow.mem = j->data; shadow.mem_size = j->size;
    shadow.source_base = shadow.parts[op->part].offsets[j->index];
    shadow.have_pending = 0; shadow.pending_buffer = NULL;
    if (!op->output.is_deep) {
        if (!j->scratch || j->scratch_size < j->bi.uncompressed_size) {
            exr_free(a, j->scratch);
            j->scratch_size = j->bi.uncompressed_size;
            j->scratch = (uint8_t *)exr_malloc(a, j->scratch_size ? j->scratch_size : 1);
            if (!j->scratch) { j->rc = EXR_ERROR_OUT_OF_MEMORY; return; }
        }
        j->rc = exr_reader_decode_block(&shadow, op->part, j->index, j->scratch, j->bi.uncompressed_size);
        if (j->rc == EXR_SUCCESS) j->rc = scatter_flat(op, j, j->scratch);
        return;
    }
    if (exr_mul_ovf((size_t)j->bi.width, (size_t)j->bi.height, &npix)) {
        j->rc = EXR_ERROR_LIMIT_EXCEEDED; return;
    }
    if (op->pass == 0) {
        int32_t *counts = (int32_t *)exr_calloc(a, npix, sizeof(int32_t));
        if (!counts) { j->rc = EXR_ERROR_OUT_OF_MEMORY; return; }
        j->rc = exr_reader_decode_deep_counts(&shadow, op->part, j->index, counts, npix, &j->total);
        if (j->rc == EXR_SUCCESS) {
            for (yy = 0; yy < j->bi.height; ++yy)
                for (xx = 0; xx < j->bi.width; ++xx) {
                    size_t pixel = (size_t)(j->bi.y0 - h->data_window.min_y + yy) * op->width +
                                   (j->bi.x0 - h->data_window.min_x + xx);
                    op->output.deep_sample_counts[pixel] = counts[k++];
                }
        }
        exr_free(a, counts);
    } else {
        exr_buffer *planes = (exr_buffer *)exr_calloc(a, h->num_channels, sizeof(exr_buffer));
        uint64_t total = 0, local = 0;
        if (!planes) { j->rc = EXR_ERROR_OUT_OF_MEMORY; return; }
        for (yy = 0; yy < j->bi.height; ++yy)
            for (xx = 0; xx < j->bi.width; ++xx) {
                size_t pixel = (size_t)(j->bi.y0 - h->data_window.min_y + yy) * op->width +
                               (j->bi.x0 - h->data_window.min_x + xx);
                total += (uint32_t)op->output.deep_sample_counts[pixel];
            }
        j->rc = EXR_SUCCESS;
        for (c = 0; c < h->num_channels; ++c) {
            if (total > SIZE_MAX || exr_mul_ovf((size_t)total, exr_pixel_size(h->channels[c].pixel_type), &planes[c].size)) {
                j->rc = EXR_ERROR_LIMIT_EXCEEDED; break;
            }
            planes[c].data = exr_malloc(a, planes[c].size ? planes[c].size : 1);
            if (!planes[c].data) { j->rc = EXR_ERROR_OUT_OF_MEMORY; break; }
        }
        if (j->rc == EXR_SUCCESS)
            j->rc = exr_reader_decode_deep_samples(&shadow, op->part, j->index, planes, h->num_channels);
        if (j->rc == EXR_SUCCESS) {
            for (yy = 0; yy < j->bi.height; ++yy)
                for (xx = 0; xx < j->bi.width; ++xx) {
                    size_t pixel = (size_t)(j->bi.y0 - h->data_window.min_y + yy) * op->width +
                                   (j->bi.x0 - h->data_window.min_x + xx);
                    size_t count = (size_t)op->output.deep_sample_counts[pixel];
                    for (c = 0; c < h->num_channels; ++c) {
                        size_t ps = exr_pixel_size(h->channels[c].pixel_type);
                        if (count) memcpy((uint8_t *)op->output.deep_images[c] + (size_t)op->prefix[pixel] * ps,
                                          (uint8_t *)planes[c].data + (size_t)local * ps, count * ps);
                    }
                    local += count;
                }
        }
        for (c = 0; c < h->num_channels; ++c) exr_free(a, planes[c].data);
        exr_free(a, planes);
    }
}

/* Claims and completion counters also publish the ordinary job/output fields. */
static int source_work_one(source_operation *op) {
    int index = -1;
    exr_wait_queue_lock(op->queue);
    if (op->queue_open && op->queue_next < op->batch_count)
        index = op->queue_next++;
    exr_wait_queue_unlock(op->queue);
    if (index < 0) return 0;
    source_job_run(op, index);
    exr_wait_queue_lock(op->queue);
    --op->queue_left;
    exr_wait_queue_notify(op->queue);
    exr_wait_queue_unlock(op->queue);
    return 1;
}

static void source_background(void *user, int unused) {
    source_operation *op = (source_operation *)user;
    (void)unused;
    for (;;) {
        int stop;
        exr_wait_queue_lock(op->queue);
        while (!op->stop && (!op->queue_open || op->queue_next >= op->batch_count))
            exr_wait_queue_wait(op->queue);
        stop = op->stop;
        exr_wait_queue_unlock(op->queue);
        if (stop) return;
        (void)source_work_one(op);
    }
}

static exr_result source_samples_init(source_operation *op) {
    exr_reader *r = op->reader;
    const exr_header *h = &op->output.header;
    size_t n, bytes, i;
    int c;
    exr_result rc;
    if (op->total > SIZE_MAX || exr_mul_ovf((size_t)op->width, (size_t)op->height, &n) ||
        exr_mul_ovf(n, sizeof(uint64_t), &bytes)) return EXR_ERROR_LIMIT_EXCEEDED;
    op->prefix = (uint64_t *)exr_malloc(&r->alloc, bytes);
    if (!op->prefix) return EXR_ERROR_OUT_OF_MEMORY;
    {
        uint64_t acc = 0;
        for (i = 0; i < n; ++i) {
            op->prefix[i] = acc; acc += (uint32_t)op->output.deep_sample_counts[i];
        }
        if (acc != op->total) return EXR_ERROR_CORRUPT;
    }
    for (c = 0; c < h->num_channels; ++c) {
        if (exr_mul_ovf((size_t)op->total, exr_pixel_size(h->channels[c].pixel_type), &bytes))
            return EXR_ERROR_LIMIT_EXCEEDED;
        rc = source_owned(op, bytes);
        if (rc != EXR_SUCCESS) return rc;
        op->output.deep_images[c] = exr_calloc(&r->alloc, bytes ? bytes : 1, 1);
        if (!op->output.deep_images[c]) return EXR_ERROR_OUT_OF_MEMORY;
    }
    op->output.deep_total_samples = op->total;
    op->next = 0; op->pass = 1;
    return EXR_SUCCESS;
}

static exr_result source_prefetch(source_operation *op) {
    exr_result rc;
    while (op->next < op->end && op->batch_count < op->batch_width) {
        source_job *j = &op->jobs[op->batch_count];
        rc = exr_reader_block_info(op->reader, op->part, op->next, &j->bi);
        if (rc != EXR_SUCCESS) return rc;
        if (op->kind == 0 && (j->bi.level_x || j->bi.level_y)) { ++op->next; continue; }
        j->index = op->next;
        rc = exr_source_chunk(op->reader, op->part, j->index, op->output.is_deep && op->pass == 0, &j->data, &j->size);
        if (rc == EXR_WOULD_BLOCK) return rc;
        if (rc != EXR_SUCCESS) return rc;
        ++op->batch_count; ++op->next;
    }
    return EXR_SUCCESS;
}

static exr_result source_drive(source_operation *op) {
    exr_result rc = EXR_SUCCESS;
    int i;
    for (;;) {
        rc = source_prefetch(op);
        if (rc != EXR_SUCCESS) return rc;
        if (op->batch_count) {
            exr_simd_init();
            {
                int first = 0;
                if (!op->warmed) {
                    source_job_run(op, 0); op->warmed = 1; first = 1;
                    if (op->jobs[0].rc != EXR_SUCCESS) return op->jobs[0].rc;
                }
                exr_wait_queue_lock(op->queue);
                op->queue_next = first; op->queue_left = op->batch_count - first;
                op->queue_open = 1;
                exr_wait_queue_notify(op->queue);
                exr_wait_queue_unlock(op->queue);
                for (;;) {
                    int left;
                    exr_wait_queue_lock(op->queue); left = op->queue_left; exr_wait_queue_unlock(op->queue);
                    if (!left) break;
                    if (!source_work_one(op)) {
                        exr_wait_queue_lock(op->queue);
                        while (op->queue_left && op->queue_next >= op->batch_count)
                            exr_wait_queue_wait(op->queue);
                        exr_wait_queue_unlock(op->queue);
                    }
                }
                exr_wait_queue_lock(op->queue); op->queue_open = 0; exr_wait_queue_unlock(op->queue);
            }
            for (i = 0; i < op->batch_count; ++i) {
                source_job *j = &op->jobs[i];
                if (j->rc != EXR_SUCCESS) { rc = j->rc; goto fail; }
                if (op->output.is_deep && op->pass == 0) {
                    if (j->total > UINT64_MAX - op->total) { rc = EXR_ERROR_CORRUPT; goto fail; }
                    op->total += j->total;
                }
                exr_source_recycle(op->reader, j->data, j->size);
                j->data = NULL; j->size = 0; j->rc = EXR_SUCCESS; j->total = 0;
            }
            op->batch_count = 0;
        }
        if (op->next < op->end) continue;
        if (op->output.is_deep && op->pass == 0) {
            rc = source_samples_init(op);
            if (rc != EXR_SUCCESS) goto fail;
            continue;
        }
        return EXR_SUCCESS;
    }
fail:
    return rc;
}

static void source_producer(void *user) {
    source_operation *op = (source_operation *)user;
    op->result = source_drive(op);
    exr_wait_queue_lock(op->queue); op->stop = 1; exr_wait_queue_notify(op->queue); exr_wait_queue_unlock(op->queue);
}

exr_result exr_source_read_part(exr_reader *r, int32_t part, int kind,
                                int32_t x, int32_t y, int32_t lx, int32_t ly,
                                exr_part *out) {
    source_operation *op = (source_operation *)r->read_operation;
    exr_result rc;
    if (op && (op->part != part || op->kind != kind || op->x != x || op->y != y ||
               op->lx != lx || op->ly != ly)) return EXR_ERROR_INVALID_ARGUMENT;
    memset(out, 0, sizeof(*out));
    if (!op) {
        rc = source_init(r, part, kind, x, y, lx, ly);
        if (rc != EXR_SUCCESS) { exr_source_operation_free(r); return rc; }
        op = (source_operation *)r->read_operation;
    }
    rc = source_prefetch(op);
    if (rc != EXR_SUCCESS) {
        if (rc != EXR_WOULD_BLOCK) exr_source_operation_free(r);
        return rc;
    }
    op->stop = 0;
    exr_parallel_caller(op->batch_width, source_background, source_producer, op);
    rc = op->result;
    if (rc == EXR_SUCCESS) {
        *out = op->output; memset(&op->output, 0, sizeof(op->output));
    }
    if (rc != EXR_WOULD_BLOCK) exr_source_operation_free(r);
    return rc;
}
