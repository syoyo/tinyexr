/*
 * B44 perceptual table boundary vectors: C table vs Lean closed-form model.
 * Format: <index-hex> <exp-entry-hex> <log-entry-hex>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include "exr_internal.h"

int main(void) {
    const uint16_t *exp_tbl = NULL, *log_tbl = NULL;
    exr_b44_debug_tables(&exp_tbl, &log_tbl);
    for (int i = 0x558c; i <= 0x7bff; i += 37)
        printf("%04x %04x -\n", i, exp_tbl[i]);
    for (int i = 0x7c00; i < 0x8000; i += 11)
        printf("%04x %04x %04x\n", i, exp_tbl[i], log_tbl[i]);
    for (int i = 0x8001; i <= 0xffff; i += 11)
        printf("%04x - %04x\n", i, log_tbl[i]);
    return 0;
}
