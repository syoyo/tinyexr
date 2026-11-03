/*
 * TinyEXR v3 - WebAssembly binding for the browser viewer (web/viewer/).
 *
 * A small stateful session layer over the v3 streaming block API
 * (include/exr.h). It lets JavaScript:
 *   - open an EXR held in WASM memory and parse all part headers,
 *   - read the full structured header as JSON (for the info panel + selectors),
 *   - select one (part, mip level) and decode it block-by-block so the UI can
 *     show load progress, accumulating the result into an RGBA float buffer,
 *   - hand that buffer to JS as a HEAPF32 view (for WebGL upload + the pixel
 *     picker).
 *
 * No filesystem, no stdio. Pixel data crosses the JS boundary through
 * emscripten's _malloc/_free and the HEAPF32/HEAPU8 views. The in-memory reader
 * never returns EXR_WOULD_BLOCK, so no suspend/resume loop is needed; the
 * progress reporting comes from driving the per-block decode loop from JS.
 *
 * Custom/standard attributes (exr_header.attrs) are opaque in the public v3 API
 * with no iteration entry point, so the JSON exposes the structured header
 * fields and the channel list only.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#define EXRV_EXPORT EMSCRIPTEN_KEEPALIVE
#else
#define EXRV_EXPORT
#endif

/* ------------------------------------------------------------------ session */

typedef struct exrv_session {
    uint8_t *data; /* owned copy of the file bytes (reader is zero-copy) */
    size_t size;
    exr_reader *r;
    int num_parts;

    /* current selection (set by exrv_select) */
    int sel_part;
    int lw, lh;             /* selected level pixel dimensions */
    int dw_min_x, dw_min_y; /* selected part data-window origin */
    uint32_t *blocks;       /* global block indices belonging to part+level */
    int nblocks;
    int rmap[4]; /* header channel index for R,G,B,A or -1 */
    float *rgba; /* lw*lh*4 accumulation buffer (RGBA float) */
    int ycc_filled; /* 1 if rgba already holds whole-part luminance-chroma color */

    /* deep point cloud: 6 floats per sample (x, y, z, r, g, b) */
    float *deep_pts;
    int deep_n;

    /* spectral image (loaded lazily for the spectral viewer mode) */
    exr_spectral_image spec;
    int spec_loaded;
    float *spec_pixel; /* num_wavelengths scratch for the per-pixel spectrum */
} exrv_session;

#define EXRV_MAX_SESSIONS 16
static exrv_session *g_sessions[EXRV_MAX_SESSIONS];

static exrv_session *session_from_handle(int h) {
    if (h < 1 || h > EXRV_MAX_SESSIONS) return NULL;
    return g_sessions[h - 1];
}

static void session_reset_selection(exrv_session *s) {
    free(s->blocks);
    s->blocks = NULL;
    s->nblocks = 0;
    free(s->rgba);
    s->rgba = NULL;
    s->lw = s->lh = 0;
    s->ycc_filled = 0;
    s->sel_part = -1;
}

/* ------------------------------------------------------------------ helpers */

static int find_channel(const exr_header *h, const char *name) {
    int c;
    for (c = 0; c < h->num_channels; ++c)
        if (strcmp(h->channels[c].name, name) == 0) return c;
    return -1;
}

/* ------------------------------------------------------------- string builder
 * Minimal growable buffer for assembling the header JSON. */

typedef struct {
    char *buf;
    size_t len, cap;
    int oom;
} strbuf;

static void sb_ensure(strbuf *b, size_t extra) {
    if (b->oom) return;
    if (b->len + extra + 1 > b->cap) {
        size_t ncap = b->cap ? b->cap * 2 : 1024;
        char *nb;
        while (ncap < b->len + extra + 1) ncap *= 2;
        nb = (char *)realloc(b->buf, ncap);
        if (!nb) {
            b->oom = 1;
            return;
        }
        b->buf = nb;
        b->cap = ncap;
    }
}

static void sb_puts(strbuf *b, const char *s) {
    size_t n = strlen(s);
    sb_ensure(b, n);
    if (b->oom) return;
    memcpy(b->buf + b->len, s, n);
    b->len += n;
    b->buf[b->len] = '\0';
}

/* Append a JSON string value with the few escapes that matter here. */
static void sb_json_str(strbuf *b, const char *s) {
    sb_puts(b, "\"");
    for (; *s; ++s) {
        char c = *s;
        if (c == '"' || c == '\\') {
            char esc[3];
            esc[0] = '\\';
            esc[1] = c;
            esc[2] = '\0';
            sb_puts(b, esc);
        } else if ((unsigned char)c < 0x20) {
            char u[8];
            snprintf(u, sizeof(u), "\\u%04x", (unsigned)(unsigned char)c);
            sb_puts(b, u);
        } else {
            char one[2];
            one[0] = c;
            one[1] = '\0';
            sb_puts(b, one);
        }
    }
    sb_puts(b, "\"");
}

static void sb_kv_int(strbuf *b, const char *key, long v) {
    char tmp[64];
    snprintf(tmp, sizeof(tmp), "\"%s\":%ld", key, v);
    sb_puts(b, tmp);
}

static const char *comp_name(exr_compression c) {
    switch (c) {
    case EXR_COMPRESSION_NONE:
        return "none";
    case EXR_COMPRESSION_RLE:
        return "rle";
    case EXR_COMPRESSION_ZIPS:
        return "zips";
    case EXR_COMPRESSION_ZIP:
        return "zip";
    case EXR_COMPRESSION_PIZ:
        return "piz";
    case EXR_COMPRESSION_PXR24:
        return "pxr24";
    case EXR_COMPRESSION_B44:
        return "b44";
    case EXR_COMPRESSION_B44A:
        return "b44a";
    case EXR_COMPRESSION_DWAA:
        return "dwaa";
    case EXR_COMPRESSION_DWAB:
        return "dwab";
    case EXR_COMPRESSION_HTJ2K256:
        return "htj2k256";
    case EXR_COMPRESSION_HTJ2K32:
        return "htj2k32";
    case EXR_COMPRESSION_ZSTD:
        return "zstd";
    }
    return "unknown";
}

static const char *parttype_name(exr_part_type t) {
    switch (t) {
    case EXR_PART_SCANLINE:
        return "scanline";
    case EXR_PART_TILED:
        return "tiled";
    case EXR_PART_DEEP_SCANLINE:
        return "deepscanline";
    case EXR_PART_DEEP_TILED:
        return "deeptiled";
    }
    return "unknown";
}

static const char *lineorder_name(exr_line_order o) {
    switch (o) {
    case EXR_LINEORDER_INCREASING_Y:
        return "increasingY";
    case EXR_LINEORDER_DECREASING_Y:
        return "decreasingY";
    case EXR_LINEORDER_RANDOM_Y:
        return "randomY";
    }
    return "unknown";
}

static const char *pixeltype_name(exr_pixel_type t) {
    switch (t) {
    case EXR_PIXEL_UINT:
        return "uint";
    case EXR_PIXEL_HALF:
        return "half";
    case EXR_PIXEL_FLOAT:
        return "float";
    }
    return "unknown";
}

static const char *levelmode_name(exr_tile_level_mode m) {
    switch (m) {
    case EXR_TILE_ONE_LEVEL:
        return "one";
    case EXR_TILE_MIPMAP_LEVELS:
        return "mipmap";
    case EXR_TILE_RIPMAP_LEVELS:
        return "ripmap";
    }
    return "unknown";
}

static const char *spectrum_type_name(exr_spectrum_type t) {
    switch (t) {
    case EXR_SPECTRUM_NONE:
        return "none";
    case EXR_SPECTRUM_REFLECTIVE:
        return "reflective";
    case EXR_SPECTRUM_EMISSIVE:
        return "emissive";
    case EXR_SPECTRUM_POLARISED:
        return "polarised";
    }
    return "unknown";
}

/* ------------------------------------------------------------------- exports */

EXRV_EXPORT int exrv_open(const uint8_t *data, int size) {
    int slot;
    exrv_session *s;
    if (!data || size <= 0) return 0;

    for (slot = 0; slot < EXRV_MAX_SESSIONS; ++slot)
        if (!g_sessions[slot]) break;
    if (slot == EXRV_MAX_SESSIONS) return 0;

    s = (exrv_session *)calloc(1, sizeof(*s));
    if (!s) return 0;
    s->sel_part = -1;

    /* The reader is zero-copy and requires the bytes to outlive it, so keep an
     * owned copy independent of whatever JS does with its input buffer. */
    s->data = (uint8_t *)malloc((size_t)size);
    if (!s->data) {
        free(s);
        return 0;
    }
    memcpy(s->data, data, (size_t)size);
    s->size = (size_t)size;

    if (!EXR_OK(exr_reader_open_memory(s->data, s->size, NULL, &s->r))) {
        free(s->data);
        free(s);
        return 0;
    }
    if (exr_reader_parse_header(s->r) != EXR_SUCCESS) {
        exr_reader_close(s->r);
        free(s->data);
        free(s);
        return 0;
    }
    s->num_parts = exr_reader_num_parts(s->r);

    g_sessions[slot] = s;
    return slot + 1;
}

EXRV_EXPORT void exrv_close(int h) {
    exrv_session *s = session_from_handle(h);
    if (!s) return;
    session_reset_selection(s);
    free(s->deep_pts);
    free(s->spec_pixel);
    if (s->spec_loaded) exr_spectral_image_free(&s->spec);
    if (s->r) exr_reader_close(s->r);
    free(s->data);
    free(s);
    g_sessions[h - 1] = NULL;
}

EXRV_EXPORT int exrv_num_parts(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->num_parts : 0;
}

/* Build the structured-header JSON. Caller frees the returned string with
 * exrv_free. Returns NULL on error. */
EXRV_EXPORT char *exrv_header_json(int h) {
    exrv_session *s = session_from_handle(h);
    strbuf b;
    int part;
    if (!s) return NULL;

    memset(&b, 0, sizeof(b));
    sb_puts(&b, "{");
    sb_kv_int(&b, "numParts", s->num_parts);
    sb_puts(&b, ",\"parts\":[");

    for (part = 0; part < s->num_parts; ++part) {
        const exr_header *hd = exr_reader_part_header(s->r, part);
        int width, height, c;
        int is_deep;
        if (!hd) continue;
        width = hd->data_window.max_x - hd->data_window.min_x + 1;
        height = hd->data_window.max_y - hd->data_window.min_y + 1;
        is_deep = (hd->part_type == EXR_PART_DEEP_SCANLINE ||
                   hd->part_type == EXR_PART_DEEP_TILED);

        if (part) sb_puts(&b, ",");
        sb_puts(&b, "{");
        sb_puts(&b, "\"name\":");
        sb_json_str(&b, hd->name);
        sb_puts(&b, ",\"type\":");
        sb_json_str(&b, parttype_name(hd->part_type));
        sb_puts(&b, ",\"compression\":");
        sb_json_str(&b, comp_name(hd->compression));
        sb_puts(&b, ",\"lineOrder\":");
        sb_json_str(&b, lineorder_name(hd->line_order));
        sb_puts(&b, ",");
        sb_kv_int(&b, "width", width);
        sb_puts(&b, ",");
        sb_kv_int(&b, "height", height);
        sb_puts(&b, ",");
        sb_kv_int(&b, "deep", is_deep);

        sb_puts(&b, ",\"dataWindow\":{");
        sb_kv_int(&b, "minX", hd->data_window.min_x);
        sb_puts(&b, ",");
        sb_kv_int(&b, "minY", hd->data_window.min_y);
        sb_puts(&b, ",");
        sb_kv_int(&b, "maxX", hd->data_window.max_x);
        sb_puts(&b, ",");
        sb_kv_int(&b, "maxY", hd->data_window.max_y);
        sb_puts(&b, "}");

        sb_puts(&b, ",\"displayWindow\":{");
        sb_kv_int(&b, "minX", hd->display_window.min_x);
        sb_puts(&b, ",");
        sb_kv_int(&b, "minY", hd->display_window.min_y);
        sb_puts(&b, ",");
        sb_kv_int(&b, "maxX", hd->display_window.max_x);
        sb_puts(&b, ",");
        sb_kv_int(&b, "maxY", hd->display_window.max_y);
        sb_puts(&b, "}");

        {
            char tmp[64];
            snprintf(tmp, sizeof(tmp), ",\"pixelAspect\":%g",
                     (double)hd->pixel_aspect_ratio);
            sb_puts(&b, tmp);
        }

        sb_puts(&b, ",");
        sb_kv_int(&b, "tiled", hd->tiled);
        if (hd->tiled) {
            sb_puts(&b, ",");
            sb_kv_int(&b, "tileXSize", (long)hd->tile_x_size);
            sb_puts(&b, ",");
            sb_kv_int(&b, "tileYSize", (long)hd->tile_y_size);
            sb_puts(&b, ",\"levelMode\":");
            sb_json_str(&b, levelmode_name(hd->level_mode));
        }

        /* Available (level_x, level_y) pairs, gathered from the block geometry
         * so the UI mip selector matches exactly what we can decode. */
        sb_puts(&b, ",\"levels\":[");
        if (hd->tiled && hd->level_mode != EXR_TILE_ONE_LEVEL) {
            uint32_t nb = 0, i;
            int first = 1;
            /* dedupe small level sets with an O(n^2) scan; level counts are tiny */
            int seen_lx[256], seen_ly[256], nseen = 0;
            if (EXR_OK(exr_reader_num_blocks(s->r, part, &nb))) {
                for (i = 0; i < nb; ++i) {
                    exr_block_info bi;
                    int k, dup = 0;
                    if (!EXR_OK(exr_reader_block_info(s->r, part, i, &bi)))
                        continue;
                    for (k = 0; k < nseen; ++k)
                        if (seen_lx[k] == bi.level_x && seen_ly[k] == bi.level_y) {
                            dup = 1;
                            break;
                        }
                    if (dup || nseen >= 256) continue;
                    seen_lx[nseen] = bi.level_x;
                    seen_ly[nseen] = bi.level_y;
                    nseen++;
                    if (!first) sb_puts(&b, ",");
                    first = 0;
                    {
                        char tmp[64];
                        snprintf(tmp, sizeof(tmp), "[%d,%d]", bi.level_x,
                                 bi.level_y);
                        sb_puts(&b, tmp);
                    }
                }
            }
            if (first) sb_puts(&b, "[0,0]");
        } else {
            sb_puts(&b, "[0,0]");
        }
        sb_puts(&b, "]");

        sb_puts(&b, ",\"channels\":[");
        for (c = 0; c < hd->num_channels; ++c) {
            const exr_channel *ch = &hd->channels[c];
            if (c) sb_puts(&b, ",");
            sb_puts(&b, "{\"name\":");
            sb_json_str(&b, ch->name);
            sb_puts(&b, ",\"type\":");
            sb_json_str(&b, pixeltype_name(ch->pixel_type));
            sb_puts(&b, ",");
            sb_kv_int(&b, "xSampling", ch->x_sampling);
            sb_puts(&b, ",");
            sb_kv_int(&b, "ySampling", ch->y_sampling);
            sb_puts(&b, "}");
        }
        sb_puts(&b, "]");

        /* Spectral metadata (JCGT layout) so the UI can offer spectral mode. */
        sb_puts(&b, ",");
        sb_kv_int(&b, "spectral", exr_is_spectral(hd) ? 1 : 0);
        if (exr_is_spectral(hd)) {
            sb_puts(&b, ",\"spectrumType\":");
            sb_json_str(&b, spectrum_type_name(exr_spectrum_type_of(hd)));
            sb_puts(&b, ",");
            sb_kv_int(&b, "numWavelengths",
                      exr_spectral_wavelengths(hd, NULL, 0));
        }

        sb_puts(&b, "}");
    }
    sb_puts(&b, "]}");

    if (b.oom) {
        free(b.buf);
        return NULL;
    }
    return b.buf;
}

/*
 * Select one (part, level) for decoding. Builds the list of global block
 * indices that belong to it, computes the level's pixel dimensions, maps the
 * R/G/B/A channels, and allocates a cleared RGBA accumulation buffer.
 * Returns the number of blocks to decode (>= 0), or -1 on error / unsupported
 * (e.g. a deep part).
 */
/* Common tail of the select* entry points: validate the part, enumerate the
 * blocks of (part, level), compute the level dimensions, and allocate a cleared
 * RGBA buffer. Caller has already filled s->rmap / s->ycc. Returns block count
 * (>= 0) or -1. */
static int finish_selection(exrv_session *s, int part, int level_x, int level_y) {
    const exr_header *hd;
    uint32_t nb = 0, i;
    int lw = 0, lh = 0, count = 0;

    hd = exr_reader_part_header(s->r, part);
    if (!hd) return -1;
    s->sel_part = part;
    s->dw_min_x = hd->data_window.min_x;
    s->dw_min_y = hd->data_window.min_y;

    if (!EXR_OK(exr_reader_num_blocks(s->r, part, &nb))) return -1;
    s->blocks = (uint32_t *)malloc((nb ? nb : 1) * sizeof(uint32_t));
    if (!s->blocks) return -1;

    for (i = 0; i < nb; ++i) {
        exr_block_info bi;
        int dx, dy;
        if (!EXR_OK(exr_reader_block_info(s->r, part, i, &bi))) continue;
        if (bi.level_x != level_x || bi.level_y != level_y) continue;
        s->blocks[count++] = i;
        dx = bi.x0 - s->dw_min_x;
        dy = bi.y0 - s->dw_min_y;
        if (dx + bi.width > lw) lw = dx + bi.width;
        if (dy + bi.height > lh) lh = dy + bi.height;
    }
    s->nblocks = count;
    s->lw = lw;
    s->lh = lh;
    if (lw <= 0 || lh <= 0) { session_reset_selection(s); s->sel_part = part; return -1; }

    s->rgba = (float *)malloc((size_t)lw * (size_t)lh * 4 * sizeof(float));
    if (!s->rgba) { session_reset_selection(s); return -1; }
    /* default RGB = 0, A = 1 (so images lacking an alpha channel are opaque) */
    {
        size_t n = (size_t)lw * (size_t)lh, p;
        for (p = 0; p < n; ++p) {
            s->rgba[p * 4 + 0] = 0.0f;
            s->rgba[p * 4 + 1] = 0.0f;
            s->rgba[p * 4 + 2] = 0.0f;
            s->rgba[p * 4 + 3] = 1.0f;
        }
    }
    return count;
}

/* Reconstruct the selected level. Tiled EXR channels have unit sampling, so
 * tiles can be converted independently without fetching chroma neighbours. */
static int select_luminance_chroma(exrv_session *s, int part, int lx, int ly) {
    const exr_header *hd = exr_reader_part_header(s->r, part);
    int count, i;
    if (!hd || find_channel(hd, "Y") < 0 || find_channel(hd, "RY") < 0 ||
        find_channel(hd, "BY") < 0 || find_channel(hd, "R") >= 0 ||
        find_channel(hd, "G") >= 0 || find_channel(hd, "B") >= 0)
        return -1;
    count = finish_selection(s, part, lx, ly);
    if (count < 0) return -1;
    for (i = 0; i < (hd->tiled ? count : 1); ++i) {
        exr_part native = {0};
        exr_block_info bi;
        exr_result rc;
        float *rgba = NULL;
        int w = 0, h = 0, x0 = 0, y0 = 0, row;
        if (hd->tiled) {
            rc = exr_reader_block_info(s->r, part, s->blocks[i], &bi);
            if (rc != EXR_SUCCESS) return -1;
            rc = exr_reader_read_tile(s->r, part, bi.tile_x, bi.tile_y, lx, ly, &native);
            x0 = bi.x0 - s->dw_min_x; y0 = bi.y0 - s->dw_min_y;
        } else rc = exr_reader_read_part(s->r, part, &native);
        if (rc == EXR_SUCCESS)
            rc = exr_part_yc_to_rgba_float(NULL, &native, &rgba, &w, &h);
        exr_part_free(NULL, &native);
        if (rc != EXR_SUCCESS || !rgba || x0 < 0 || y0 < 0 ||
            w > s->lw - x0 || h > s->lh - y0) { free(rgba); return -1; }
        for (row = 0; row < h; ++row)
            memcpy(s->rgba + ((size_t)(row + y0) * s->lw + x0) * 4,
                   rgba + (size_t)row * w * 4, (size_t)w * 4 * sizeof(float));
        free(rgba);
    }
    s->ycc_filled = 1;
    return count;
}

/* Auto-detect a sensible channel mapping for a part (conventional R/G/B/A,
 * luminance-chroma Y/RY/BY, or a generic fallback) and select it. */
EXRV_EXPORT int exrv_select(int h, int part, int level_x, int level_y) {
    exrv_session *s = session_from_handle(h);
    const exr_header *hd;
    static const char *names[4] = {"R", "G", "B", "A"};
    int k;
    if (!s) return -1;
    if (part < 0 || part >= s->num_parts) return -1;
    hd = exr_reader_part_header(s->r, part);
    if (!hd) return -1;
    if (hd->part_type == EXR_PART_DEEP_SCANLINE ||
        hd->part_type == EXR_PART_DEEP_TILED)
        return -1; /* deep not supported by this viewer */

    session_reset_selection(s);
    for (k = 0; k < 4; ++k) s->rmap[k] = find_channel(hd, names[k]);

    /* Fallbacks for parts without conventional R/G/B so they render instead of
     * showing black — luminance, multiview, depth, motion vectors, etc. */
    if (s->rmap[0] < 0 && s->rmap[1] < 0 && s->rmap[2] < 0) {
        int y;
        /* Luminance-chroma (Y + subsampled RY/BY, e.g. CrissyField.exr): decode
         * the whole part and reconstruct true color. Falls through to grayscale
         * Y if reconstruction isn't applicable (other level, decode failure). */
        int yc = select_luminance_chroma(s, part, level_x, level_y);
        if (yc >= 0) return yc;
        session_reset_selection(s);
        for (k = 0; k < 4; ++k) s->rmap[k] = find_channel(hd, names[k]);

        y = find_channel(hd, "Y");
        if (y >= 0) {
            s->rmap[0] = s->rmap[1] = s->rmap[2] = y; /* luminance -> grayscale */
        } else if (hd->num_channels == 1) {
            s->rmap[0] = s->rmap[1] = s->rmap[2] = 0; /* single data channel */
        } else if (hd->num_channels >= 2) {
            /* Multi-channel data (motion vectors, disparity): leading -> R,G,B. */
            s->rmap[0] = 0;
            s->rmap[1] = 1;
            s->rmap[2] = (hd->num_channels >= 3) ? 2 : -1;
        }
    }
    return finish_selection(s, part, level_x, level_y);
}

/* Explicit channel selection from the UI's channel-view combo: (c0,c1,c2,c3)
 * map directly to (R,G,B,A); -1 leaves the default (RGB 0 / A 1). Use the same
 * index for c0/c1/c2 to display one channel as grayscale. */
EXRV_EXPORT int exrv_select_channels(int h, int part, int level_x, int level_y,
                                     int c0, int c1, int c2, int c3) {
    exrv_session *s = session_from_handle(h);
    const exr_header *hd;
    if (!s) return -1;
    if (part < 0 || part >= s->num_parts) return -1;
    hd = exr_reader_part_header(s->r, part);
    if (!hd) return -1;
    if (hd->part_type == EXR_PART_DEEP_SCANLINE ||
        hd->part_type == EXR_PART_DEEP_TILED)
        return -1;

    session_reset_selection(s);
    s->rmap[0] = c0; s->rmap[1] = c1; s->rmap[2] = c2; s->rmap[3] = c3;
    return finish_selection(s, part, level_x, level_y);
}

/* Select the luminance-chroma "Color" view: reconstruct full color from a
 * Y/RY/BY part. Returns the block count (>= 0) or -1 if the part is not
 * luminance-chroma / not at level 0 / could not be decoded (the UI then falls
 * back to the grayscale-Y channel view). */
EXRV_EXPORT int exrv_select_ycc(int h, int part, int level_x, int level_y) {
    exrv_session *s = session_from_handle(h);
    const exr_header *hd;
    int yc;
    if (!s) return -1;
    if (part < 0 || part >= s->num_parts) return -1;
    hd = exr_reader_part_header(s->r, part);
    if (!hd) return -1;
    if (hd->part_type == EXR_PART_DEEP_SCANLINE ||
        hd->part_type == EXR_PART_DEEP_TILED)
        return -1;

    session_reset_selection(s);
    yc = select_luminance_chroma(s, part, level_x, level_y);
    if (yc >= 0) return yc;
    session_reset_selection(s);
    return -1;
}

EXRV_EXPORT int exrv_level_width(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->lw : 0;
}

EXRV_EXPORT int exrv_level_height(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->lh : 0;
}

/* Scatter one channel's planar samples (native pixel type) into the RGBA
 * accumulation buffer at the block's offset. Only full-resolution channels
 * (x/y sampling == 1) are mapped; subsampled channels are skipped (rare for
 * R/G/B/A and not needed for a viewer). */
static void scatter_channel(exrv_session *s, const exr_block_info *bi,
                            int comp, const void *planar, exr_pixel_type type) {
    int row, col, bw = bi->width, bh = bi->height;
    int dx = bi->x0 - s->dw_min_x;
    int dy = bi->y0 - s->dw_min_y;
    const uint16_t *ph = (const uint16_t *)planar;
    const float *pf = (const float *)planar;
    const uint32_t *pu = (const uint32_t *)planar;

    for (row = 0; row < bh; ++row) {
        int yy = dy + row;
        if (yy < 0 || yy >= s->lh) continue;
        for (col = 0; col < bw; ++col) {
            int xx = dx + col;
            size_t si = (size_t)row * (size_t)bw + (size_t)col;
            size_t di;
            float v;
            if (xx < 0 || xx >= s->lw) continue;
            switch (type) {
            case EXR_PIXEL_HALF: {
                float f;
                exr_half_to_float(ph + si, &f, 1);
                v = f;
                break;
            }
            case EXR_PIXEL_FLOAT:
                v = pf[si];
                break;
            case EXR_PIXEL_UINT:
                v = (float)pu[si];
                break;
            default:
                v = 0.0f;
                break;
            }
            di = ((size_t)yy * (size_t)s->lw + (size_t)xx) * 4 + (size_t)comp;
            s->rgba[di] = v;
        }
    }
}

/*
 * Decode the i-th block of the current selection into the RGBA accumulation
 * buffer. Returns 1 on success, 0 if i is out of range, -1 on decode error.
 */
EXRV_EXPORT int exrv_decode_block(int h, int i) {
    exrv_session *s = session_from_handle(h);
    const exr_header *hd;
    exr_block_info bi;
    uint8_t *block = NULL;
    uint8_t *chan = NULL;
    size_t chan_cap;
    int k, rc_ret = -1;

    if (!s || !s->rgba || !s->blocks) return -1;
    if (i < 0 || i >= s->nblocks) return 0;
    /* Luminance-chroma color was reconstructed whole-part at select time; the
     * per-block scatter would overwrite it, so the loop is a no-op here. */
    if (s->ycc_filled) return 1;
    hd = exr_reader_part_header(s->r, s->sel_part);
    if (!hd) return -1;

    if (!EXR_OK(exr_reader_block_info(s->r, s->sel_part, s->blocks[i], &bi)))
        return -1;

    block = (uint8_t *)malloc(bi.uncompressed_size ? bi.uncompressed_size : 1);
    if (!block) return -1;
    if (!EXR_OK(exr_reader_decode_block(s->r, s->sel_part, s->blocks[i], block,
                                        bi.uncompressed_size)))
        goto done;

    /* scratch for one extracted channel (full-res block: width*height elems) */
    chan_cap = (size_t)bi.width * (size_t)bi.height * 4; /* worst-case 4 bytes */
    chan = (uint8_t *)malloc(chan_cap ? chan_cap : 1);
    if (!chan) goto done;

    for (k = 0; k < 4; ++k) {
        int ci = s->rmap[k];
        exr_pixel_type type;
        if (ci < 0) continue;
        if (hd->channels[ci].x_sampling != 1 || hd->channels[ci].y_sampling != 1)
            continue; /* skip subsampled channels */
        type = hd->channels[ci].pixel_type;
        if (!EXR_OK(exr_block_extract_channel(hd, &bi, block,
                                              bi.uncompressed_size, ci, chan,
                                              chan_cap)))
            goto done;
        scatter_channel(s, &bi, k, chan, type);
    }
    rc_ret = 1;

done:
    free(block);
    free(chan);
    return rc_ret;
}

EXRV_EXPORT float *exrv_rgba(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->rgba : NULL;
}

/* ------------------------------------------------------------ deep (3D) ---- */

/* Read deep sample `idx` of channel `c` as float (0 if c < 0). */
static float deep_sample_f(const exr_part *p, int c, uint64_t idx) {
    const void *buf;
    if (c < 0) return 0.0f;
    buf = p->deep_images[c];
    switch (p->header.channels[c].pixel_type) {
    case EXR_PIXEL_HALF: { float f; exr_half_to_float((const uint16_t *)buf + idx, &f, 1); return f; }
    case EXR_PIXEL_FLOAT: return ((const float *)buf)[idx];
    case EXR_PIXEL_UINT:  return (float)((const uint32_t *)buf)[idx];
    default: return 0.0f;
    }
}

/* Decode a deep part into a point cloud: 6 floats per sample (x, y, z, r, g, b),
 * x/y in data-window pixel coords, z = the Z (depth) channel. Returns the sample
 * count (>= 0) or -1 (not deep / no Z / error). Buffer via exrv_deep_points. */
EXRV_EXPORT int exrv_deep_load(int h, int part) {
    exrv_session *s = session_from_handle(h);
    exr_image img;
    exr_part *p;
    int zc = -1, rc = -1, gc = -1, bc = -1, c, x, y, w;
    uint64_t N, off, o;
    if (!s) return -1;
    if (part < 0 || part >= s->num_parts) return -1;

    free(s->deep_pts);
    s->deep_pts = NULL;
    s->deep_n = 0;

    memset(&img, 0, sizeof img);
    if (!EXR_OK(exr_load_from_memory(s->data, s->size, NULL, &img))) return -1;
    if (part >= img.num_parts) { exr_image_free(&img); return -1; }
    p = &img.parts[part];
    if (!p->is_deep || !p->deep_sample_counts || !p->deep_images) {
        exr_image_free(&img);
        return -1;
    }
    for (c = 0; c < p->header.num_channels; ++c) {
        const char *nm = p->header.channels[c].name;
        if (!strcmp(nm, "Z")) zc = c;
        else if (!strcmp(nm, "R")) rc = c;
        else if (!strcmp(nm, "G")) gc = c;
        else if (!strcmp(nm, "B")) bc = c;
    }
    N = p->deep_total_samples;
    if (N == 0 || zc < 0) { exr_image_free(&img); return -1; } /* need depth */

    s->deep_pts = (float *)malloc((size_t)N * 6 * sizeof(float));
    if (!s->deep_pts) { exr_image_free(&img); return -1; }

    w = p->width;
    off = 0; o = 0;
    for (y = 0; y < p->height; ++y) {
        for (x = 0; x < w; ++x) {
            int cnt = p->deep_sample_counts[(size_t)y * w + x], sps;
            for (sps = 0; sps < cnt; ++sps) {
                uint64_t i = off + (uint64_t)sps;
                s->deep_pts[o++] = (float)x;
                s->deep_pts[o++] = (float)y;
                s->deep_pts[o++] = deep_sample_f(p, zc, i);
                s->deep_pts[o++] = deep_sample_f(p, rc, i);
                s->deep_pts[o++] = deep_sample_f(p, gc, i);
                s->deep_pts[o++] = deep_sample_f(p, bc, i);
            }
            off += (uint64_t)cnt;
        }
    }
    s->deep_n = (int)N;
    exr_image_free(&img);
    return s->deep_n;
}

EXRV_EXPORT float *exrv_deep_points(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->deep_pts : NULL;
}

EXRV_EXPORT int exrv_deep_count(int h) {
    exrv_session *s = session_from_handle(h);
    return s ? s->deep_n : 0;
}

/* ----------------------------------------------------- spectral viewer ---- */

EXRV_EXPORT int exrv_is_spectral(int h, int part) {
    exrv_session *s = session_from_handle(h);
    const exr_header *hd;
    if (!s) return 0;
    if (part < 0 || part >= s->num_parts) return 0;
    hd = exr_reader_part_header(s->r, part);
    return (hd && exr_is_spectral(hd)) ? 1 : 0;
}

/* Load all wavelength planes of the (single) spectral part into a float cube,
 * (re)allocate the shared RGBA buffer sized to the image, and a per-pixel
 * spectrum scratch. Returns the number of wavelengths (> 0) or -1. The cube
 * keeps the spectral channels in memory so wavelength scrubbing and per-pixel
 * spectra are allocation-free afterwards. */
EXRV_EXPORT int exrv_spectral_open_part(int h, int part) {
    exrv_session *s = session_from_handle(h);
    size_t npix;
    if (!s) return -1;

    session_reset_selection(s); /* frees any 2D rgba buffer + selection */
    if (s->spec_loaded) {
        exr_spectral_image_free(&s->spec);
        s->spec_loaded = 0;
    }
    free(s->spec_pixel);
    s->spec_pixel = NULL;

    if (!EXR_OK(exr_spectral_load_part_from_memory(s->data, s->size, part, NULL, &s->spec)))
        return -1;
    s->spec_loaded = 1;
    s->lw = s->spec.width;
    s->lh = s->spec.height;
    s->dw_min_x = 0;
    s->dw_min_y = 0;

    npix = (size_t)s->lw * (size_t)s->lh;
    s->rgba = (float *)malloc((npix ? npix : 1) * 4 * sizeof(float));
    s->spec_pixel = (float *)malloc(
        (s->spec.num_wavelengths ? (size_t)s->spec.num_wavelengths : 1) *
        sizeof(float));
    if (!s->rgba || !s->spec_pixel) return -1;
    return s->spec.num_wavelengths;
}

/* Retain the existing entry point for consumers selecting the first part. */
EXRV_EXPORT int exrv_spectral_open(int h) { return exrv_spectral_open_part(h, -1); }

EXRV_EXPORT int exrv_spectral_width(int h) {
    exrv_session *s = session_from_handle(h);
    return (s && s->spec_loaded) ? s->spec.width : 0;
}
EXRV_EXPORT int exrv_spectral_height(int h) {
    exrv_session *s = session_from_handle(h);
    return (s && s->spec_loaded) ? s->spec.height : 0;
}

/* Pointer to the sorted wavelength array (num_wavelengths floats) for JS. */
EXRV_EXPORT float *exrv_spectral_wavelengths(int h) {
    exrv_session *s = session_from_handle(h);
    return (s && s->spec_loaded) ? s->spec.wavelengths : NULL;
}

/* Fill the shared RGBA buffer with the grayscale plane for wavelength `wi`
 * (R=G=B=value, A=1), reusing the existing 2D upload + tone-map path. Returns
 * 1 on success, -1 otherwise. */
EXRV_EXPORT int exrv_spectral_show(int h, int wi) {
    exrv_session *s = session_from_handle(h);
    size_t npix, p;
    const float *plane;
    if (!s || !s->spec_loaded || !s->rgba) return -1;
    if (wi < 0 || wi >= s->spec.num_wavelengths || !s->spec.stokes[0]) return -1;
    npix = (size_t)s->spec.width * (size_t)s->spec.height;
    plane = s->spec.stokes[0] + (size_t)wi * npix;
    for (p = 0; p < npix; ++p) {
        float v = plane[p];
        s->rgba[p * 4 + 0] = v;
        s->rgba[p * 4 + 1] = v;
        s->rgba[p * 4 + 2] = v;
        s->rgba[p * 4 + 3] = 1.0f;
    }
    return 1;
}

/* CIE 1931 2-deg color-matching functions via the multi-lobe Gaussian fit of
 * Wyman, Sloan & Shirley, "Simple Analytic Approximations to the CIE XYZ Color
 * Matching Functions" (JCGT 2013) — compact and accurate enough for a preview. */
static float cie_lobe(float x, float mu, float s1, float s2) {
    float t = (x - mu) * (x < mu ? 1.0f / s1 : 1.0f / s2);
    return expf(-0.5f * t * t);
}
static void cie_xyz_bar(float wl, float *X, float *Y, float *Z) {
    *X = 1.056f * cie_lobe(wl, 599.8f, 37.9f, 31.0f) +
         0.362f * cie_lobe(wl, 442.0f, 16.0f, 26.7f) -
         0.065f * cie_lobe(wl, 501.1f, 20.4f, 26.2f);
    *Y = 0.821f * cie_lobe(wl, 568.8f, 46.9f, 40.5f) +
         0.286f * cie_lobe(wl, 530.9f, 16.3f, 31.1f);
    *Z = 1.217f * cie_lobe(wl, 437.0f, 11.8f, 36.0f) +
         0.681f * cie_lobe(wl, 459.0f, 26.0f, 13.8f);
}

/* Composite the spectral cube to a linear-sRGB preview in the shared RGBA buffer
 * (the shader then applies exposure + the sRGB curve). For each pixel we
 * integrate S(lambda) against the CMFs (trapezoidal dlambda from the wavelength
 * spacing), normalize so an equal-energy spectrum has luminance 1, convert XYZ
 * to linear sRGB (D65 matrix), and white-balance so a flat spectrum maps to
 * neutral (1,1,1). Returns 1 on success, -1 otherwise. */
EXRV_EXPORT int exrv_spectral_composite(int h) {
    exrv_session *s = session_from_handle(h);
    int nwl, k;
    size_t npix, p;
    const float *wl;
    float *Xw, *Yw, *Zw;
    float sumX = 0.0f, sumY = 0.0f, sumZ = 0.0f, inv, wr, wg, wb;
    /* XYZ (D65) -> linear sRGB */
    static const float M[9] = {
        3.2406255f, -1.5372080f, -0.4986286f,
        -0.9689307f, 1.8757561f, 0.0415175f,
        0.0557101f, -0.2040211f, 1.0569959f};

    if (!s || !s->spec_loaded || !s->rgba || !s->spec.stokes[0]) return -1;
    nwl = s->spec.num_wavelengths;
    wl = s->spec.wavelengths;
    if (nwl <= 0) return -1;
    npix = (size_t)s->spec.width * (size_t)s->spec.height;

    Xw = (float *)malloc((size_t)nwl * sizeof(float));
    Yw = (float *)malloc((size_t)nwl * sizeof(float));
    Zw = (float *)malloc((size_t)nwl * sizeof(float));
    if (!Xw || !Yw || !Zw) { free(Xw); free(Yw); free(Zw); return -1; }

    for (k = 0; k < nwl; ++k) {
        float x, y, z, dl;
        float lo = (k > 0) ? wl[k - 1] : wl[k];
        float hi = (k + 1 < nwl) ? wl[k + 1] : wl[k];
        dl = 0.5f * (hi - lo);
        if (dl <= 0.0f) dl = 1.0f;
        cie_xyz_bar(wl[k], &x, &y, &z);
        Xw[k] = x * dl;
        Yw[k] = y * dl;
        Zw[k] = z * dl;
        sumX += Xw[k];
        sumY += Yw[k];
        sumZ += Zw[k];
    }
    if (sumY <= 0.0f) sumY = 1.0f;
    inv = 1.0f / sumY;
    for (k = 0; k < nwl; ++k) { Xw[k] *= inv; Yw[k] *= inv; Zw[k] *= inv; }
    sumX *= inv; sumZ *= inv; sumY = 1.0f;

    /* equal-energy white in linear sRGB, used for per-channel white balance */
    wr = M[0] * sumX + M[1] * sumY + M[2] * sumZ;
    wg = M[3] * sumX + M[4] * sumY + M[5] * sumZ;
    wb = M[6] * sumX + M[7] * sumY + M[8] * sumZ;
    if (wr <= 0.0f) wr = 1.0f;
    if (wg <= 0.0f) wg = 1.0f;
    if (wb <= 0.0f) wb = 1.0f;

    for (p = 0; p < npix; ++p) {
        float X = 0.0f, Y = 0.0f, Z = 0.0f, r, g, b;
        const float *plane = s->spec.stokes[0] + p;
        for (k = 0; k < nwl; ++k) {
            float v = plane[(size_t)k * npix];
            X += v * Xw[k];
            Y += v * Yw[k];
            Z += v * Zw[k];
        }
        r = (M[0] * X + M[1] * Y + M[2] * Z) / wr;
        g = (M[3] * X + M[4] * Y + M[5] * Z) / wg;
        b = (M[6] * X + M[7] * Y + M[8] * Z) / wb;
        s->rgba[p * 4 + 0] = r > 0.0f ? r : 0.0f;
        s->rgba[p * 4 + 1] = g > 0.0f ? g : 0.0f;
        s->rgba[p * 4 + 2] = b > 0.0f ? b : 0.0f;
        s->rgba[p * 4 + 3] = 1.0f;
    }
    free(Xw); free(Yw); free(Zw);
    return 1;
}

/* Fill the per-pixel spectrum scratch (num_wavelengths floats) for (x,y) of the
 * primary Stokes plane and return it (zeros on out-of-range). */
EXRV_EXPORT float *exrv_spectral_pixel(int h, int x, int y) {
    exrv_session *s = session_from_handle(h);
    if (!s || !s->spec_loaded || !s->spec_pixel) return NULL;
    if (exr_spectral_pixel(&s->spec, 0, x, y, s->spec_pixel) <= 0) {
        int i;
        for (i = 0; i < s->spec.num_wavelengths; ++i) s->spec_pixel[i] = 0.0f;
    }
    return s->spec_pixel;
}

EXRV_EXPORT void exrv_free(void *p) { free(p); }
