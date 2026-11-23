/*
 * texcomp - emit shared header-validation vectors for the Lean gate.
 * Format: <fields...> <verdict 0|1> <channel-tuples...>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "exr_internal.h"

static uint64_t st = 0x2545f4914f6cdd1dULL;
static uint32_t rnd(void) {
    uint64_t z = (st += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return (uint32_t)(z ^ (z >> 31));
}

int main(void) {
    for (int iter = 0; iter < 240; ++iter) {
        exr_header h;
        exr_channel chans[4];
        char names[4][EXR_MAX_NAME];
        char partname[EXR_MAX_NAME];
        int nc = 1 + (int)(rnd() % 4);
        int valid = iter % 2;
        int tiled = (int)(rnd() % 2);
        int pt = rnd() % 4;
        int comp = rnd() % 9;
        int lo = rnd() % 2;
        int32_t w = 1 + (int)(rnd() % 64), ht = 1 + (int)(rnd() % 64);
        int nl = 1 + (int)(rnd() % 40);
        int rc;
        memset(&h, 0, sizeof(h));
        memset(chans, 0, sizeof(chans));
        h.num_channels = nc;
        h.channels = chans;
        h.part_type = (exr_part_type)pt;
        h.compression = (exr_compression)comp;
        h.line_order = (exr_line_order)lo;
        h.data_window.min_x = 0; h.data_window.min_y = 0;
        h.data_window.max_x = w - 1; h.data_window.max_y = ht - 1;
        h.display_window = h.data_window;
        h.pixel_aspect_ratio = 1.0f;
        h.screen_window_center_x = 0.0f;
        h.screen_window_center_y = 0.0f;
        h.screen_window_width = 1.0f;
        h.tiled = (uint8_t)tiled;
        h.tile_x_size = 16; h.tile_y_size = 16;
        h.level_mode = EXR_TILE_ONE_LEVEL;
        h.rounding_mode = EXR_TILE_ROUND_DOWN;
        memset(partname, 'p', (size_t)nl); partname[nl] = 0;
        strcpy(h.name, partname);
        for (int c = 0; c < nc; ++c) {
            int n = 1 + (int)(rnd() % 40);
            memset(names[c], 'c', (size_t)n); names[c][n] = 0;
            strcpy(chans[c].name, names[c]);
            chans[c].pixel_type = (exr_pixel_type)(rnd() % 3);
            chans[c].x_sampling = 1;
            chans[c].y_sampling = 1;
            chans[c].p_linear = 0;
        }
        if (valid) {
            /* keep the randomized-but-legal values; force tiled consistency */
            h.tiled = (uint8_t)(pt == EXR_PART_TILED || pt == EXR_PART_DEEP_TILED);
        } else {
            /* inject one violation */
            switch (rnd() % 8) {
            case 0: h.num_channels = 0; break;
            case 1: h.data_window.max_x = h.data_window.min_x - 1; break;
            case 2: chans[0].y_sampling = 0; break;
            case 3: chans[0].pixel_type = (exr_pixel_type)99; break;
            case 4: h.pixel_aspect_ratio = 0.0f; break;
            case 5: h.tiled = (uint8_t)!h.tiled; break;
            case 6: h.tile_x_size = 0; break;
            case 7: h.num_channels = 2000; break; /* above maxChannels */
            }
        }
        rc = (int)exr_header_validate(&h, 0, NULL, NULL, NULL);
        {
            int vals[24] = {
                h.num_channels, 1, pt, comp, lo,
                h.data_window.min_x, h.data_window.max_x,
                h.data_window.min_y, h.data_window.max_y,
                h.display_window.min_x, h.display_window.max_x,
                h.display_window.min_y, h.display_window.max_y,
                1, h.pixel_aspect_ratio > 0.0f ? 1 : 0,
                h.screen_window_width >= 0.0f ? 1 : 0, 1, (int)h.tiled, (int)h.tile_x_size, (int)h.tile_y_size,
                (int)h.level_mode, (int)h.rounding_mode, nl,
                rc == EXR_SUCCESS ? 1 : 0
            };
            for (int i = 0; i < 24; ++i) printf("%d ", vals[i]);
        }
        for (int c = 0; c < nc; ++c) {
            int n = (int)strlen(chans[c].name);
            printf(" %d %d %d %d %d", n, (int)chans[c].pixel_type,
                   chans[c].x_sampling, chans[c].y_sampling,
                   (int)chans[c].p_linear);
        }
        putchar('\n');
    }
    return 0;
}
