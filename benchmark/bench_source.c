/*
 * TinyEXR - file/input memory and high-channel-count throughput benchmark.
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr_internal.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct meter { size_t live, peak; volatile long lock; } meter;
typedef union record { max_align_t align; size_t size; } record;
static void *meter_alloc(void *u, size_t size) {
    meter *m = (meter *)u;
    record *p;
    if (size > SIZE_MAX - sizeof(*p)) return NULL;
    p = (record *)malloc(sizeof(*p) + size);
    if (!p) return NULL;
    p->size = size;
    exr_input_lock(&m->lock); m->live += size;
    if (m->live > m->peak) m->peak = m->live;
    exr_input_unlock(&m->lock);
    return p + 1;
}
static void meter_free(void *u, void *ptr) {
    meter *m = (meter *)u;
    record *p;
    if (!ptr) return;
    p = (record *)ptr - 1;
    exr_input_lock(&m->lock); m->live -= p->size; exr_input_unlock(&m->lock);
    free(p);
}
static double seconds(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}
static exr_result read_path(int mode, const char *path, const void *data, size_t size,
                             const exr_allocator *a) {
    exr_result rc;
    if (mode < 2) {
        exr_image image = {0};
        rc = mode == 0 ? exr_load_from_memory(data, size, a, &image)
                       : exr_load_from_file(path, a, &image);
        exr_image_free(&image);
    } else {
        exr_reader *r = NULL;
        void *scratch = NULL;
        size_t capacity = 0;
        uint32_t n = 0, k;
        rc = exr_reader_open_file(path, a, &r);
        if (rc == EXR_SUCCESS) rc = exr_reader_num_blocks(r, 0, &n);
        for (k = 0; rc == EXR_SUCCESS && k < n; ++k) {
            exr_block_info bi;
            rc = exr_reader_block_info(r, 0, k, &bi);
            if (rc != EXR_SUCCESS) break;
            if (bi.uncompressed_size > capacity) {
                exr_free(a, scratch); capacity = bi.uncompressed_size;
                scratch = exr_malloc(a, capacity ? capacity : 1);
                if (!scratch) { rc = EXR_ERROR_OUT_OF_MEMORY; break; }
            }
            rc = exr_reader_decode_block(r, 0, k, scratch, capacity);
        }
        exr_free(a, scratch); exr_reader_close(r);
    }
    return rc;
}
int main(int argc, char **argv) {
    int w = argc > 1 ? atoi(argv[1]) : 1024;
    int h = argc > 2 ? atoi(argv[2]) : 1024;
    int nc = argc > 3 ? atoi(argv[3]) : 4;
    int repeats = argc > 4 ? atoi(argv[4]) : 3;
    const exr_compression codecs[] = {EXR_COMPRESSION_NONE, EXR_COMPRESSION_ZIP, EXR_COMPRESSION_PIZ};
    const char *codec_names[] = {"none", "zip", "piz"};
    const char *paths[] = {"memory", "file", "blocks"};
    exr_image input = {0};
    exr_part *p;
    float pixel[3] = {0};
    size_t n, bytes, i;
    int c, codec, threads, mode, repeat;
    if (w < 1 || h < 1 || nc < 1 || nc > EXR_MAX_CHANNELS || repeats < 1 ||
        exr_mul_ovf((size_t)w, (size_t)h, &n) || exr_mul_ovf(n, sizeof(uint16_t), &bytes)) return 2;
    input.alloc = *exr_default_allocator(); input.num_parts = 1;
    input.parts = (exr_part *)calloc(1, sizeof(exr_part));
    if (!input.parts) return 2;
    p = input.parts;
    if (exr_rgba_float_to_part(NULL, pixel, 1, 1, 3, EXR_PIXEL_HALF, p)) return 2;
    for (c = 0; c < 3; ++c) free(p->images[c]);
    free(p->images); free(p->header.channels);
    p->width = w; p->height = h;
    p->header.data_window.max_x = p->header.display_window.max_x = w - 1;
    p->header.data_window.max_y = p->header.display_window.max_y = h - 1;
    p->header.num_channels = nc;
    p->header.channels = (exr_channel *)calloc((size_t)nc, sizeof(exr_channel));
    p->images = (void **)calloc((size_t)nc, sizeof(void *));
    if (!p->header.channels || !p->images) return 2;
    for (c = 0; c < nc; ++c) {
        uint16_t *plane = (uint16_t *)malloc(bytes);
        if (!plane) return 2;
        p->images[c] = plane;
        snprintf(p->header.channels[c].name, EXR_MAX_NAME, "C%04d", c);
        p->header.channels[c].pixel_type = EXR_PIXEL_HALF;
        p->header.channels[c].x_sampling = p->header.channels[c].y_sampling = 1;
        for (i = 0; i < n; ++i) plane[i] = (uint16_t)(0x3000 + (i + c * 71) % 1024);
    }
    puts("width,height,channels,codec,threads,path,ms,encoded_bytes,peak_tracked_bytes");
    for (codec = 0; codec < 3; ++codec) {
        void *encoded = NULL;
        size_t size = 0;
        char path[160];
        FILE *f;
        if (exr_save_to_memory(&encoded, &size, NULL, &input, codecs[codec])) return 3;
        snprintf(path, sizeof(path), "build/_bench_source_%dx%dx%d_%s.exr", w, h, nc, codec_names[codec]);
        f = fopen(path, "wb");
        if (!f) return 3;
        if (fwrite(encoded, 1, size, f) != size || fclose(f)) return 3;
        for (threads = 1; threads <= 4; threads *= 4) {
            exr_set_num_threads(threads);
            for (mode = 0; mode < 3; ++mode) {
                meter m = {0};
                exr_allocator a = {&m, meter_alloc, meter_free};
                double start, elapsed;
                /* Allocation metering is a separate warm-up, outside timing. */
                if (read_path(mode, path, encoded, size, &a) || m.live) return 4;
                start = seconds();
                for (repeat = 0; repeat < repeats; ++repeat)
                    if (read_path(mode, path, encoded, size, exr_default_allocator())) return 4;
                elapsed = (seconds() - start) * 1000 / repeats;
                printf("%d,%d,%d,%s,%d,%s,%.3f,%zu,%zu\n", w, h, nc, codec_names[codec], threads, paths[mode], elapsed, size, m.peak);
                fflush(stdout);
            }
        }
        free(encoded); remove(path);
    }
    exr_image_free(&input);
    return 0;
}
