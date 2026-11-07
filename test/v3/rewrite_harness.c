/*
 * Rewrite a fixture through the v3 public API for an independent reader.
 * Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr.h"
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
    exr_compression compression;
    exr_image image;
    exr_result rc;
    if (argc != 4) {
        fprintf(stderr, "usage: rewrite_harness <input.exr> <output.exr> <NONE|RLE|ZIPS>\n");
        return 2;
    }
    if (strcmp(argv[3], "NONE") == 0) compression = EXR_COMPRESSION_NONE;
    else if (strcmp(argv[3], "RLE") == 0) compression = EXR_COMPRESSION_RLE;
    else if (strcmp(argv[3], "ZIPS") == 0) compression = EXR_COMPRESSION_ZIPS;
    else return 2;
    memset(&image, 0, sizeof(image));
    rc = exr_load_from_file(argv[1], NULL, &image);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "load: %s\n", exr_result_string(rc));
        return 1;
    }
    rc = exr_save_to_file(argv[2], &image, compression);
    exr_image_free(&image);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "save: %s\n", exr_result_string(rc));
        return 1;
    }
    return 0;
}
