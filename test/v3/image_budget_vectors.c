/* image-budget vectors: flat-plane byte sizes vs the Lean model.
 * Format: <w> <h> <nc> <xs,ys,pt>... <size>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "exr_internal.h"

static uint64_t st = 0x243f6a8885a308d3ULL;
static uint32_t rnd(void) {
    uint64_t z = (st += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return (uint32_t)(z ^ (z >> 31));
}

int main(void) {
    for (int it = 0; it < 240; ++it) {
        exr_header h;
        exr_channel ch[4];
        char names[4][EXR_MAX_NAME];
        int nc = 1 + (int)(rnd() % 4);
        int w = 1 + (int)(rnd() % 300), ht = 1 + (int)(rnd() % 300);
        size_t bytes = 0;
        exr_result rc;
        memset(&h, 0, sizeof(h));
        memset(ch, 0, sizeof(ch));
        for (int c = 0; c < nc; ++c) {
            memset(names[c], 'c', 2); names[c][2] = 0;
            strcpy(ch[c].name, names[c]);
            ch[c].x_sampling = (int32_t)(1 + rnd() % 4);
            ch[c].y_sampling = (int32_t)(1 + rnd() % 4);
            ch[c].pixel_type = (exr_pixel_type)(rnd() % 3);
        }
        h.num_channels = nc;
        h.channels = ch;
        rc = exr_flat_planes_size(&h, 0, 0, w, ht, &bytes);
        if (rc != EXR_SUCCESS) continue;
        printf("%d %d %d", w, ht, nc);
        for (int c = 0; c < nc; ++c)
            printf(" %d %d %d", ch[c].x_sampling, ch[c].y_sampling,
                   (int)ch[c].pixel_type);
        printf(" %zu\n", bytes);
    }
    return 0;
}
