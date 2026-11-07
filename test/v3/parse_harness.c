/*
 * parse_harness - minimal TinyEXR v3 parse/load probe for the parse tester.
 *
 * Usage: parse_harness <file.exr>
 *
 * Emits machine-readable key/value lines on stdout:
 *
 *   FILE <path>
 *   HEADER_RESULT <code> <string>
 *   PARTS <n>
 *   PART <i> type=<t> compression=<NAME> channels=<n> size=<w>x<h>
 *   LOAD_RESULT <code> <string>
 *
 * It first parses the headers/offset tables (no pixel I/O) so the per-part
 * compression is reported even when the subsequent full load fails (e.g. an
 * unsupported DWA codec). Then it attempts a full high-level load.
 *
 * Exit status: 0 if the full load succeeded, 1 otherwise. The tester relies on
 * the printed compression names + result strings, not just the exit code.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdio.h>
#include <stdlib.h>

#include "exr.h"

static const char *compression_name(exr_compression c) {
    switch (c) {
        case EXR_COMPRESSION_NONE: return "NONE";
        case EXR_COMPRESSION_RLE: return "RLE";
        case EXR_COMPRESSION_ZIPS: return "ZIPS";
        case EXR_COMPRESSION_ZIP: return "ZIP";
        case EXR_COMPRESSION_PIZ: return "PIZ";
        case EXR_COMPRESSION_PXR24: return "PXR24";
        case EXR_COMPRESSION_B44: return "B44";
        case EXR_COMPRESSION_B44A: return "B44A";
        case EXR_COMPRESSION_DWAA: return "DWAA";
        case EXR_COMPRESSION_DWAB: return "DWAB";
        case EXR_COMPRESSION_HTJ2K256: return "HTJ2K256";
        case EXR_COMPRESSION_HTJ2K32: return "HTJ2K32";
        case EXR_COMPRESSION_ZSTD: return "ZSTD";
        default: return "UNKNOWN";
    }
}

static const char *part_type_name(exr_part_type t) {
    switch (t) {
        case EXR_PART_SCANLINE: return "scanline";
        case EXR_PART_TILED: return "tiled";
        case EXR_PART_DEEP_SCANLINE: return "deep_scanline";
        case EXR_PART_DEEP_TILED: return "deep_tiled";
        default: return "unknown";
    }
}

static void emit_fatal(exr_result code) {
    printf("HEADER_RESULT %d %s\n", (int)code, exr_result_string(code));
    printf("LOAD_RESULT %d %s\n", (int)code, exr_result_string(code));
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <file.exr>\n", argv[0]);
        return 2;
    }
    const char *path = argv[1];
    printf("FILE %s\n", path);

    /* Read the whole file into memory so both passes use the zero-copy path. */
    FILE *fp = fopen(path, "rb");
    if (!fp) {
        emit_fatal(EXR_ERROR_IO);
        return 1;
    }
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    if (sz <= 0) {
        fclose(fp);
        emit_fatal(EXR_ERROR_INVALID_FILE);
        return 1;
    }
    unsigned char *buf = (unsigned char *)malloc((size_t)sz);
    if (!buf) {
        fclose(fp);
        emit_fatal(EXR_ERROR_OUT_OF_MEMORY);
        return 1;
    }
    size_t got = fread(buf, 1, (size_t)sz, fp);
    fclose(fp);
    if (got != (size_t)sz) {
        free(buf);
        emit_fatal(EXR_ERROR_IO);
        return 1;
    }

    /* --- Header pass: report structure + compression without pixel I/O. --- */
    exr_reader *r = NULL;
    exr_result hres = exr_reader_open_memory(buf, (size_t)sz, NULL, &r);
    if (EXR_OK(hres)) hres = exr_reader_parse_header(r);
    printf("HEADER_RESULT %d %s\n", (int)hres, exr_result_string(hres));
    if (EXR_OK(hres) && r) {
        int32_t n = exr_reader_num_parts(r);
        printf("PARTS %d\n", (int)n);
        for (int32_t i = 0; i < n; i++) {
            const exr_header *h = exr_reader_part_header(r, i);
            if (!h) continue;
            int32_t w = h->data_window.max_x - h->data_window.min_x + 1;
            int32_t hh = h->data_window.max_y - h->data_window.min_y + 1;
            printf("COMPRESSION %d %d\n", (int)i, (int)h->compression);
            if (h->tiled)
                printf("TILE %d %u %u %d %d\n", (int)i,
                       h->tile_x_size, h->tile_y_size,
                       (int)h->level_mode, (int)h->rounding_mode);
            else printf("TILE %d none\n", (int)i);
            for (int32_t ci = 0; ci < h->num_channels; ++ci) {
                const exr_channel *ch = &h->channels[ci];
                printf("CHANNEL %d %d ", (int)i, (int)ci);
                for (size_t ni = 0; ch->name[ni]; ++ni)
                    printf("%s%u", ni ? "." : "", (unsigned)(unsigned char)ch->name[ni]);
                printf(" %d %d %d %d\n", (int)ch->pixel_type, (int)ch->p_linear,
                       (int)ch->x_sampling, (int)ch->y_sampling);
            }
            printf("WINDOW %d %d %d %d %d\n", (int)i,
                   (int)h->data_window.min_x, (int)h->data_window.min_y,
                   (int)h->data_window.max_x, (int)h->data_window.max_y);
            {
                uint32_t blocks = 0;
                exr_reader_num_blocks(r, i, &blocks);
                printf("PART %d type=%s compression=%s channels=%d size=%dx%d "
                       "chunks=%u tiled=%d deep=%d\n",
                       (int)i, part_type_name(h->part_type),
                       compression_name(h->compression), (int)h->num_channels,
                       (int)w, (int)hh, blocks,
                       h->tiled ? 1 : 0,
                       (h->part_type == EXR_PART_DEEP_SCANLINE ||
                        h->part_type == EXR_PART_DEEP_TILED) ? 1 : 0);
            }
        }
    }
    if (r) exr_reader_close(r);

    /* --- Full load pass (decodes all pixels). --- */
    exr_image img;
    exr_result lres = exr_load_from_memory(buf, (size_t)sz, NULL, &img);
    printf("LOAD_RESULT %d %s\n", (int)lres, exr_result_string(lres));
    if (EXR_OK(lres)) exr_image_free(&img);
    free(buf);

    return EXR_OK(lres) ? 0 : 1;
}
