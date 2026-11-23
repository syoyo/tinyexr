/*
 * reader-state vectors: error latching and ownership on failed parses.
 * Format: <kind> <rc1> <rc2> <num_parts> <parts_cap> <parts_nonnull>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "exr_internal.h"

static const uint8_t bad_magic[8] = {0, 0, 0, 0, 0, 0, 0, 0};
static const uint8_t truncated[12] = {0x76, 0x2f, 0x31, 0x01, 2, 0, 0, 0, 'a', 0, 0};
static const uint8_t bad_version[8] = {0x76, 0x2f, 0x31, 0x01, 0xff, 0, 0, 0};

static void emit(const char *kind, const uint8_t *buf, size_t n, int via_read) {
    exr_reader *r = NULL;
    exr_part p;
    exr_result r1, r2;
    if (exr_reader_open_memory(buf, n, NULL, &r) != EXR_SUCCESS) return;
    memset(&p, 0, sizeof(p));
    if (via_read)
        r1 = exr_reader_read_part(r, 0, &p);
    else
        r1 = exr_reader_parse_header(r);
    r2 = exr_reader_parse_header(r);
    printf("%s %d %d %d %d %d\n", kind, (int)r1, (int)r2,
           r->num_parts, r->parts_cap, r->parts ? 1 : 0);
    exr_part_free(NULL, &p);
    exr_reader_close(r);
}

int main(void) {
    emit("magic", bad_magic, sizeof(bad_magic), 0);
    emit("trunc", truncated, sizeof(truncated), 0);
    emit("version", bad_version, sizeof(bad_version), 0);
    emit("magic_read", bad_magic, sizeof(bad_magic), 1);
    emit("trunc_read", truncated, sizeof(truncated), 1);
    emit("version_read", bad_version, sizeof(bad_version), 1);
    return 0;
}
