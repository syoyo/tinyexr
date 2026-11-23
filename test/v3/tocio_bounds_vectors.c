/* tocio values-fit guard vectors for the Lean loader-bounds model.
 * Format: <count> <avail> <verdict 0|1>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause */
#include <stdio.h>
#include <stdint.h>
#include "toc_internal.h"

int main(void) {
    static const size_t counts[] = {0, 1, 2, 3, 7, 16, 255, 256, 1024, 65536};
    static const size_t avails[] = {0, 1, 2, 3, 4, 7, 15, 16, 31, 64, 511, 1024};
    char buf[1024];
    for (unsigned a = 0; a < sizeof(avails) / sizeof(avails[0]); ++a) {
        size_t avail = avails[a];
        for (unsigned c = 0; c < sizeof(counts) / sizeof(counts[0]); ++c)
            printf("%zu %zu %d\n", counts[c], avail,
                   toc_values_fit(counts[c], buf, buf + avail) ? 1 : 0);
    }
    return 0;
}
