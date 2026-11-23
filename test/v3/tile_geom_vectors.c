/* tile-geometry vectors: 64-bit ceil-div vs the Lean model (task.md S4).
 * Format: <value> <divisor> <result>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause */
#include <stdio.h>
#include <stdint.h>
#include "exr_internal.h"

int main(void) {
    static const int vals[] = {1, 2, 3, 7, 16, 64, 255, 4096, 65535,
        1 << 20, 0x3fffffff, 0x7ffffffe, 0x7fffffff};
    static const int divs[] = {1, 2, 3, 4, 16, 256, 0x7fefffff, 0x7fffffff};
    for (unsigned i = 0; i < sizeof(vals) / sizeof(vals[0]); ++i)
        for (unsigned j = 0; j < sizeof(divs) / sizeof(divs[0]); ++j)
            printf("%d %d %d\n", vals[i], divs[j],
                   exr_ceil_div_pos(vals[i], divs[j]));
    return 0;
}
