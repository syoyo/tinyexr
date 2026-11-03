/*
 * TinyEXR - repeated whole-image load benchmark.
 *
 * Times N warm-cache loads of one file through the public load APIs and reports
 * per-load elapsed time plus per-load minor page faults. This isolates the
 * allocation-lifetime/paging cost of repeated loads, which the general
 * throughput sweep in bench_source.c averages away.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

typedef struct meter {
    size_t live, peak;
} meter;

static void *meter_alloc(void *user, size_t size) {
    meter *m = (meter *)user;
    size_t *p;
    if (size > SIZE_MAX - sizeof(size_t)) return NULL;
    p = (size_t *)malloc(sizeof(size_t) + size);
    if (!p) return NULL;
    *p = size;
    m->live += size;
    if (m->live > m->peak) m->peak = m->live;
    return p + 1;
}

static void meter_free(void *user, void *ptr) {
    meter *m = (meter *)user;
    size_t *p;
    if (!ptr) return;
    p = (size_t *)ptr - 1;
    m->live -= *p;
    free(p);
}

static double seconds(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

static long minor_faults(void) {
    struct rusage u;
    if (getrusage(RUSAGE_SELF, &u) != 0) return 0;
    return u.ru_minflt;
}

typedef enum load_mode {
    LOAD_FILE = 0, /* exr_load_from_file: library-private codec context */
    LOAD_CTX = 1   /* exr_load_from_file_ctx with one caller-reused context */
} load_mode;

static const char *mode_names[] = {"file", "file+ctx"};

static exr_result do_load(load_mode mode, exr_context *ctx, const char *path,
                          const exr_allocator *alloc) {
    exr_image image = {0};
    exr_result rc = mode == LOAD_CTX
                        ? exr_load_from_file_ctx(ctx, path, alloc, &image)
                        : exr_load_from_file(path, alloc, &image);
    if (rc == EXR_SUCCESS) exr_image_free(&image);
    return rc;
}

static uint64_t file_size(const char *path) {
    FILE *f = fopen(path, "rb");
    long size;
    if (!f) return 0;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return 0; }
    size = ftell(f);
    fclose(f);
    return size > 0 ? (uint64_t)size : 0;
}

int main(int argc, char **argv) {
    const char *path;
    int loads, warmups, mode;
    int threads = 1;
    uint64_t bytes;

    if (argc < 2) {
        fprintf(stderr,
                "usage: %s FILE [LOADS] [WARMUPS] [THREADS]\n"
                "  default: LOADS=300 WARMUPS=6 THREADS=1\n",
                argv[0]);
        return 2;
    }
    path = argv[1];
    loads = argc > 2 ? atoi(argv[2]) : 300;
    warmups = argc > 3 ? atoi(argv[3]) : 6;
    threads = argc > 4 ? atoi(argv[4]) : 1;
    if (loads < 1 || warmups < 0 || threads < 1) return 2;
    bytes = file_size(path);
    if (!bytes) {
        fprintf(stderr, "bench_reload: cannot read %s\n", path);
        return 2;
    }
    exr_set_num_threads(threads);

    puts("file_bytes,mode,threads,ms_per_load,minflt_per_load,peak_tracked_bytes");
    for (mode = 0; mode < 2; ++mode) {
        exr_context *ctx = NULL;
        long fault0;
        double start;
        size_t peak;
        int i;

        if (mode == LOAD_CTX && exr_context_create(NULL, &ctx) != EXR_SUCCESS) {
            fprintf(stderr, "bench_reload: context creation failed\n");
            return 4;
        }

        for (i = 0; i < warmups; ++i)
            if (do_load((load_mode)mode, ctx, path, NULL) !=
                EXR_SUCCESS) {
                fprintf(stderr, "bench_reload: warm-up load failed\n");
                return 4;
            }

        fault0 = minor_faults();
        start = seconds();
        for (i = 0; i < loads; ++i)
            if (do_load((load_mode)mode, ctx, path, NULL) !=
                EXR_SUCCESS) {
                fprintf(stderr, "bench_reload: timed load failed\n");
                return 4;
            }
        {
            double ms = (seconds() - start) * 1000.0 / loads;
            double flt = (double)(minor_faults() - fault0) / loads;
            if (ctx) { exr_context_destroy(ctx); ctx = NULL; }

            /* Peak tracked bytes are measured after timing: a metered pass
             * first would perturb the heap state the timing run sees. */
            {
                meter m = {0};
                exr_allocator metered = {&m, meter_alloc, meter_free};
                exr_context *mctx = NULL;
                if (mode == LOAD_CTX) {
                    if (exr_context_create(&metered, &mctx) != EXR_SUCCESS) {
                        fprintf(stderr,
                                "bench_reload: metered context creation failed\n");
                        return 4;
                    }
                }
                if (do_load((load_mode)mode, mctx, path, &metered) !=
                    EXR_SUCCESS) {
                    fprintf(stderr, "bench_reload: metered %s load failed\n",
                            mode_names[mode]);
                    return 4;
                }
                peak = m.peak;
                if (mctx) exr_context_destroy(mctx);
            }
            printf("%llu,%s,%d,%.3f,%.1f,%zu\n",
                   (unsigned long long)bytes, mode_names[mode], threads, ms,
                   flt, peak);
            fflush(stdout);
        }

        if (ctx) exr_context_destroy(ctx);
    }
    return 0;
}
