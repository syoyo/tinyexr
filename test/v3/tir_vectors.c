/*
 * tir - emit axis-classification vectors for the Lean differential gate.
 *
 * For each parameter combination we ask the C table builder for the
 * fast/exception classification of every destination index and for the
 * resulting measure dims. The Lean model recomputes the classification scan
 * and the exception count from those bits.
 *
 * Output line format:
 *   d fastLo fastHi nExc bits
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdlib.h>

#include "tir_internal.h"

int main(void) {
    static const int dims[] = {1, 2, 3, 4, 5, 7, 8, 16, 17, 33};
    static const tir_filter filters[] = {
        TIR_FILTER_BOX, TIR_FILTER_TRIANGLE, TIR_FILTER_BSPLINE,
        TIR_FILTER_GAUSSIAN, TIR_FILTER_MITCHELL, TIR_FILTER_CATMULL_ROM,
        TIR_FILTER_LANCZOS2, TIR_FILTER_LANCZOS3, TIR_FILTER_KAISER};
    static const tir_edge_mode edges[] = {
        TIR_EDGE_CLAMP, TIR_EDGE_REFLECT, TIR_EDGE_WRAP};
    static const tir_registration regs[] = {
        TIR_REG_CELL_CENTERED, TIR_REG_GRID_VERTEX};
    static const float scales[] = {1.0f, 2.0f, 0.5f};
    static const float sigmas[] = {0.5f, 1.0f};
    size_t di, fi, ei, ri, si, gi;

    for (di = 0; di < sizeof(dims) / sizeof(dims[0]); ++di) {
        const int d = dims[di];
        for (fi = 0; fi < sizeof(filters) / sizeof(filters[0]); ++fi) {
            for (ei = 0; ei < sizeof(edges) / sizeof(edges[0]); ++ei) {
                for (ri = 0; ri < sizeof(regs) / sizeof(regs[0]); ++ri) {
                    for (si = 0; si < sizeof(scales) / sizeof(scales[0]); ++si) {
                        for (gi = 0; gi < sizeof(sigmas) / sizeof(sigmas[0]); ++gi) {
                            tir__axis_params p;
                            tir__axis_dims out;
                            unsigned char *bits;
                            int i;
                            tir_result rc;
                            p.s = d;
                            p.d = d;
                            p.filter = filters[fi];
                            p.edge = edges[ei];
                            p.reg = regs[ri];
                            p.filter_scale = scales[si];
                            p.gaussian_sigma = sigmas[gi];
                            bits = (unsigned char *)malloc((size_t)d);
                            if (!bits) return 1;
                            rc = tir__axis_classify(&p, bits, &out);
                            if (rc != TIR_SUCCESS) {
                                free(bits);
                                continue; /* size overflow / OOM: not a model case */
                            }
                            printf("%d %d %d %d ", d, out.fast_lo, out.fast_hi, out.n_exc);
                            for (i = 0; i < d; ++i) putchar(bits[i] ? '1' : '0');
                            putchar('\n');
                            free(bits);
                        }
                    }
                }
            }
        }
    }
    return 0;
}
