/*
 * tir - streaming trace vectors for the Lean state-machine model.
 * Format:
 *   cfg <sh> <dh> <cap> <fastLo> <fastHi>
 *   start <y> <count0> <count1> ...   (per destination row: needed source rows)
 *   trace <op> <arg> <rc> <ring[0..cap-1]> <curDst>
 *   parity <equal 0|1> <rows>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "tir_internal.h"

static void dump_ring(const tir_sampler *s) {
    for (int i = 0; i < s->ring_cap; ++i) printf(" %d", s->ring_srcy[i]);
}

static void trace(const char *op, int arg, tir_result rc, const tir_sampler *s) {
    printf("trace %s %d %d", op, arg, (int)rc);
    dump_ring(s);
    printf(" %d\n", s->cur_dst);
}

static tir_result push_draining(tir_sampler *s, int y, const void *src,
                                uint8_t *out, int *total, int dh, int pattern) {
    int tries = 0;
    tir_result rc;
    do {
        rc = tir__push_row(s, y, src);
        if (pattern) trace("P", y, rc, s);
        if (rc == TIR_WOULD_BLOCK) {
            int oy = -1;
            tir_result pr = tir__pull_row(s, &oy,
                out + (size_t)(*total) * 4u * 4u);
            if (pattern) trace("Y", oy, pr, s);
            if (pr != TIR_SUCCESS) return pr;
            if (oy >= 0) (*total)++;
        }
    } while (rc == TIR_WOULD_BLOCK && ++tries < dh + 64);
    return rc;
}

static void emit_case(int sh, int dh, int pattern) {
    tir_options opt;
    tir_sampler *s = NULL;
    uint8_t *src = NULL, *out1 = NULL, *out2 = NULL;
    size_t rowbytes = 4u * 4u;  /* dst_w=4, ch=1, f32 */
    int y, rc, total = 0;
    tir_options_init(&opt);
    opt.deterministic = 1;
    opt.filter_x = TIR_FILTER_TRIANGLE;
    opt.filter_y = TIR_FILTER_TRIANGLE;
    if (tir_sampler_create(NULL, 4, sh, 4, dh, 1, TIR_F32, TIR_F32, &opt, &s) != TIR_SUCCESS)
        return;
    src = (uint8_t *)malloc(rowbytes);
    out1 = (uint8_t *)calloc((size_t)dh, rowbytes);
    out2 = (uint8_t *)calloc((size_t)dh, rowbytes);
    if (!src || !out1 || !out2) goto done;
    for (int i = 0; i < 4; ++i) ((float *)src)[i] = (float)((i * 7 + sh) % 11) * 0.125f;

    printf("cfg %d %d %d %d %d\n", sh, dh, s->ring_cap, s->fy.fast_lo, s->fy.fast_hi);
    for (int d = 0; d < dh; ++d) {
        printf("start %d", s->fy.start[d]);
        printf(" %d", s->fy.count[d]);
        putchar('\n');
    }

    /* Run 1: serial (all pushes, then all pulls). */
    for (y = 0; y < sh; ++y) {
        rc = push_draining(s, y, src, out1, &total, dh, 0);
        if (rc != TIR_SUCCESS) goto done;
    }
    while (total < dh) {
        int oy = -1;
        rc = tir__pull_row(s, &oy, out1 + (size_t)total * rowbytes);
        if (rc != TIR_SUCCESS) break;
        if (oy >= 0) total++;
    }

    /* Reset and run 2: interleaved, emitting the trace. */
    tir__reset(s);
    total = 0;
    for (y = 0; y < sh; ++y) {
        rc = push_draining(s, y, src, out2, &total, dh, pattern);
        if (rc != TIR_SUCCESS) goto done;
    }
    while (total < dh) {
        int oy = -1;
        rc = tir__pull_row(s, &oy, out2 + (size_t)total * rowbytes);
        if (pattern) trace("Y", oy, rc, s);
        if (rc != TIR_SUCCESS) break;
        if (oy >= 0) total++;
    }
    printf("parity %d %d\n", (total == dh && memcmp(out1, out2, (size_t)dh * rowbytes) == 0) ? 1 : 0, total);
done:
    free(src); free(out1); free(out2);
    tir_sampler_destroy(s);
}

int main(void) {
    emit_case(8, 4, 1);
    emit_case(8, 8, 1);
    emit_case(16, 4, 1);
    emit_case(12, 12, 1);
    emit_case(9, 5, 1);
    emit_case(5, 9, 1);
    return 0;
}
