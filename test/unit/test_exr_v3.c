/*
 * TinyEXR v3 (pure C11) reader unit test.
 *
 * Run from the repository root (paths are relative to it):
 *     make test-c
 *
 * Validates the public load API against the bundled corpus and confirms that
 * malformed / fuzzer files fail cleanly without crashing (run under ASan).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr.h"
#include "exr_internal.h" /* exr_fpnge_deflate / exr_inflate_zlib (internal) */

#include <math.h> /* libm reference for the B44 table-correctness test */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_pass = 0, g_fail = 0;

#define CHECK(cond, msg)                                                       \
    do {                                                                       \
        if (cond) {                                                            \
            g_pass++;                                                          \
        } else {                                                               \
            g_fail++;                                                          \
            printf("  FAIL: %s (%s:%d)\n", msg, __FILE__, __LINE__);           \
        }                                                                      \
    } while (0)

typedef struct test_alloc_stats {
    int allocs;
    int frees;
} test_alloc_stats;

static void *test_counting_alloc(void *user, size_t size) {
    test_alloc_stats *stats = (test_alloc_stats *)user;
    if (stats) stats->allocs++;
    return malloc(size ? size : 1);
}

static void test_counting_free(void *user, void *ptr) {
    test_alloc_stats *stats = (test_alloc_stats *)user;
    if (stats && ptr) stats->frees++;
    free(ptr);
}

/* Load a file expected to succeed; check dims + channel count of part 0. */
static void expect_load(const char *path, int parts, int w, int h, int nch) {
    exr_image img;
    exr_result rc;
    memset(&img, 0, sizeof(img));
    rc = exr_load_from_file(path, NULL, &img);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: %s did not load: %s\n", path, exr_result_string(rc));
        return;
    }
    CHECK(img.num_parts == parts, path);
    if (img.num_parts > 0) {
        CHECK(img.parts[0].width == w, path);
        CHECK(img.parts[0].height == h, path);
        CHECK(img.parts[0].header.num_channels == nch, path);
        CHECK(img.parts[0].images != NULL, path);
    }
    exr_image_free(&img);
    printf("  ok: %s (%dx%d, %d ch)\n", path, w, h, nch);
}

/* Load a file expected to fail; the subsequent free must be safe. */
static void expect_fail(const char *path) {
    exr_image img;
    exr_result rc;
    memset(&img, 0, sizeof(img));
    rc = exr_load_from_file(path, NULL, &img);
    CHECK(!EXR_OK(rc) || rc == EXR_WOULD_BLOCK ? !EXR_OK(rc) : 0, path);
    exr_image_free(&img); /* must not crash / double-free */
    if (!EXR_OK(rc)) printf("  ok (rejected): %s -> %s\n", path,
                            exr_result_string(rc));
}

/* Run a file purely for crash-safety (any result accepted). */
static void run_safe(const char *path) {
    exr_image img;
    memset(&img, 0, sizeof(img));
    (void)exr_load_from_file(path, NULL, &img);
    exr_image_free(&img);
    g_pass++;
}

static int images_equal(const exr_image *a, const exr_image *b) {
    int p, c;
    if (a->num_parts != b->num_parts) return 0;
    for (p = 0; p < a->num_parts; ++p) {
        const exr_part *pa = &a->parts[p], *pb = &b->parts[p];
        if (pa->width != pb->width || pa->height != pb->height) return 0;
        if (pa->header.num_channels != pb->header.num_channels) return 0;
        for (c = 0; c < pa->header.num_channels; ++c) {
            size_t ps =
                pa->header.channels[c].pixel_type == EXR_PIXEL_HALF ? 2 : 4;
            if (memcmp(pa->images[c], pb->images[c],
                       (size_t)pa->width * pa->height * ps) != 0)
                return 0;
        }
    }
    return 1;
}

/* Decode an HTJ2K regression fixture and assert each channel's pixels match a
 * pre-captured expected byte sequence. The expected arrays below were produced
 * by loading each fixture once via v3 and dumping the raw channel bytes; the
 * goal is byte-equal regression coverage independent of the openexr-images
 * corpus (which the v3 test suite intentionally does not depend on). */
static void jph_decode_known_pixels(const char *path, const char *name,
                                    const int *expected_w, const int *expected_h,
                                    const char *const *channel_names,
                                    const unsigned char *const *expected_bytes,
                                    const size_t *expected_sizes,
                                    int n_channels) {
    exr_image img;
    exr_result rc;
    int c;
    memset(&img, 0, sizeof(img));
    rc = exr_load_from_file(path, NULL, &img);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: HTJ2K decode %s load: %s\n", name,
               exr_result_string(rc));
        exr_image_free(&img);
        return;
    }
    CHECK(img.num_parts == 1, "HTJ2K decode: one part");
    CHECK(img.parts[0].width == *expected_w, "HTJ2K decode: width");
    CHECK(img.parts[0].height == *expected_h, "HTJ2K decode: height");
    CHECK(img.parts[0].header.num_channels == n_channels,
          "HTJ2K decode: channel count");
    for (c = 0; c < n_channels; ++c) {
        const exr_channel *ch = &img.parts[0].header.channels[c];
        const unsigned char *got =
            (const unsigned char *)img.parts[0].images[c];
        size_t expected_size = expected_sizes[c];
        if (strcmp(ch->name, channel_names[c]) != 0) {
            g_fail++;
            printf("  FAIL: HTJ2K decode %s channel %d name: got %s want %s\n",
                   name, c, ch->name, channel_names[c]);
            continue;
        }
        if (memcmp(got, expected_bytes[c], expected_size) != 0) {
            g_fail++;
            printf("  FAIL: HTJ2K decode %s channel %s pixel mismatch\n", name,
                   ch->name);
            printf("    first diff at byte: ");
            for (size_t b = 0; b < expected_size; ++b) {
                if (got[b] != expected_bytes[c][b]) {
                    printf("%zu (got %02x want %02x)\n", b, got[b],
                           expected_bytes[c][b]);
                    break;
                }
            }
        }
    }
    if (g_fail == 0)
        printf("  ok: HTJ2K decode known pixels %s\n", name);
    exr_image_free(&img);
}

static void jph_decode_matches(const char *ref_path, const char *ht_path,
                               const char *name) {
    exr_image ref, ht;
    exr_result rc_ref, rc_ht;
    memset(&ref, 0, sizeof(ref));
    memset(&ht, 0, sizeof(ht));
    rc_ref = exr_load_from_file(ref_path, NULL, &ref);
    rc_ht = exr_load_from_file(ht_path, NULL, &ht);
    if (!EXR_OK(rc_ref) || !EXR_OK(rc_ht)) {
        g_fail++;
        printf("  FAIL: HTJ2K decode compare %s load ref=%s ht=%s\n", name,
               exr_result_string(rc_ref), exr_result_string(rc_ht));
    } else {
        if (!images_equal(&ref, &ht)) {
            int p, c;
            CHECK(0, name);
            for (p = 0; p < ref.num_parts && p < ht.num_parts; ++p) {
                for (c = 0; c < ref.parts[p].header.num_channels &&
                            c < ht.parts[p].header.num_channels; ++c) {
                    const exr_part *rp = &ref.parts[p];
                    const exr_part *hp = &ht.parts[p];
                    size_t ps = rp->header.channels[c].pixel_type ==
                                        EXR_PIXEL_HALF
                                    ? 2
                                    : 4;
                    size_t n = (size_t)rp->width * rp->height * ps;
                    size_t k;
                    for (k = 0; k < n; ++k) {
                        if (((const unsigned char *)rp->images[c])[k] !=
                            ((const unsigned char *)hp->images[c])[k]) {
                            printf("  first diff %s part %d channel %d %s byte %zu: %02x != %02x\n",
                                   name, p, c, rp->header.channels[c].name, k,
                                   ((const unsigned char *)rp->images[c])[k],
                                   ((const unsigned char *)hp->images[c])[k]);
                            goto diff_done;
                        }
                    }
                }
            }
diff_done:
            ;
        } else {
            CHECK(1, name);
            printf("  ok: HTJ2K decode matches %s\n", name);
        }
    }
    exr_image_free(&ref);
    exr_image_free(&ht);
}

/* Encode with non-1 subsampling and verify the resulting file decodes and has
 * the expected (sampled-down) dimensions. */
static void jph_encode_subsampling_roundtrip(void) {
    exr_image img, dec;
    exr_part part;
    exr_channel channels[2];
    void *images[2];
    /* 4x2 file: channel A (subsampled 2x1) and channel B (full-res). */
    uint16_t a_pixels[4] = {0x3c00, 0x4000, 0xbc00, 0x0001};
    uint16_t b_pixels[8] = {0x0000, 0x3c00, 0x4000, 0xffff,
                            0xbc00, 0x8000, 0x0001, 0x7bff};
    size_t i;
    exr_result rc;
    memset(&img, 0, sizeof(img));
    img.num_parts = 1;
    img.parts = &part;
    memset(&part, 0, sizeof(part));
    part.header.num_channels = 2;
    part.header.channels = channels;
    memset(channels, 0, sizeof(channels));
    channels[0] = (exr_channel){"A", EXR_PIXEL_HALF, 2, 1, 0};
    channels[1] = (exr_channel){"B", EXR_PIXEL_HALF, 1, 1, 0};
    part.header.data_window.min_x = 0;
    part.header.data_window.min_y = 0;
    part.header.data_window.max_x = 3;
    part.header.data_window.max_y = 1;
    part.header.display_window = part.header.data_window;
    part.width = 4;
    part.height = 2;
    part.images = images;
    images[0] = a_pixels;
    images[1] = b_pixels;
    part.header.compression = EXR_COMPRESSION_HTJ2K32;
    {
        void *buf = NULL;
        size_t sz = 0;
        rc = exr_save_to_memory(&buf, &sz, NULL, &img, EXR_COMPRESSION_HTJ2K32);
        if (rc != EXR_SUCCESS) {
            g_fail++;
            printf("  FAIL: HTJ2K subsampling encode: %s\n",
                   exr_result_string(rc));
            return;
        }
        memset(&dec, 0, sizeof(dec));
        rc = exr_load_from_memory(buf, sz, NULL, &dec);
        free(buf);
        if (!EXR_OK(rc)) {
            g_fail++;
            printf("  FAIL: HTJ2K subsampling decode: %s\n",
                   exr_result_string(rc));
            return;
        }
    }
    /* Channel A should be 2x2 (sampled 2x1 from 4x2). Channel B 4x2. */
    if (dec.num_parts != 1) {
        g_fail++;
        printf("  FAIL: HTJ2K subsampling wrong part count\n");
        return;
    }
    if (dec.parts[0].header.num_channels != 2) {
        g_fail++;
        printf("  FAIL: HTJ2K subsampling wrong channel count\n");
        return;
    }
    for (i = 0; i < 2; ++i) {
        const exr_channel *ch = &dec.parts[0].header.channels[i];
        const unsigned char *got =
            (const unsigned char *)dec.parts[0].images[i];
        size_t expected_size;
        if (strcmp(ch->name, "A") == 0) {
            expected_size = 4 * 2; /* 2x2 half */
            if (memcmp(got, a_pixels, expected_size) != 0) {
                g_fail++;
                printf("  FAIL: HTJ2K subsampling channel A mismatch\n");
            }
        } else {
            expected_size = 8 * 2; /* 4x2 half */
            if (memcmp(got, b_pixels, expected_size) != 0) {
                g_fail++;
                printf("  FAIL: HTJ2K subsampling channel B mismatch\n");
            }
        }
    }
    if (g_fail == 0) {
        g_pass++;
        printf("  ok: HTJ2K subsampling encode round-trips losslessly\n");
    }
    exr_image_free(&dec);
}

/* Encode a 3-channel RGB file (HALF + FLOAT) and decode it losslessly. Exactly
 * 3 same-type channels triggers the multicomponent RCT (mc_trans=1) on encode;
 * a bit-exact round-trip proves the forward RCT + inverse RCT agree. */
static void jph_encode_rct_roundtrip(void) {
    const int W = 5, H = 4, N = 20;
    int i, ok = 1;
    float Rf[20], Gf[20], Bf[20];
    uint16_t Rh[20], Gh[20], Bh[20];
    for (i = 0; i < N; ++i) {
        Rf[i] = (float)i * 0.1f - 0.5f;       /* incl. negatives */
        Gf[i] = (float)((i * 7) % 13) * 0.3f;
        Bf[i] = (float)(N - i) * 0.07f;
    }
    exr_float_to_half(Rf, Rh, N);
    exr_float_to_half(Gf, Gh, N);
    exr_float_to_half(Bf, Bh, N);
    {
        struct { exr_pixel_type pt; void *r, *g, *b; size_t bytes; const char *nm; }
        cases[2] = {
            {EXR_PIXEL_HALF, Rh, Gh, Bh, (size_t)N * 2, "HALF"},
            {EXR_PIXEL_FLOAT, Rf, Gf, Bf, (size_t)N * 4, "FLOAT"}};
        int k;
        for (k = 0; k < 2; ++k) {
            exr_image img, dec;
            exr_part part;
            exr_channel ch[3];
            void *images[3], *buf = NULL;
            size_t sz = 0;
            exr_result rc;
            memset(&img, 0, sizeof(img));
            img.num_parts = 1; img.parts = &part;
            memset(&part, 0, sizeof(part));
            part.header.num_channels = 3;
            part.header.channels = ch;
            memset(ch, 0, sizeof(ch));
            ch[0] = (exr_channel){"B", cases[k].pt, 1, 1, 0}; /* sorted B,G,R */
            ch[1] = (exr_channel){"G", cases[k].pt, 1, 1, 0};
            ch[2] = (exr_channel){"R", cases[k].pt, 1, 1, 0};
            part.header.data_window.min_x = 0;
            part.header.data_window.min_y = 0;
            part.header.data_window.max_x = W - 1;
            part.header.data_window.max_y = H - 1;
            part.header.display_window = part.header.data_window;
            part.width = W; part.height = H;
            part.images = images;
            images[0] = cases[k].b; images[1] = cases[k].g; images[2] = cases[k].r;
            part.header.compression = EXR_COMPRESSION_HTJ2K32;
            rc = exr_save_to_memory(&buf, &sz, NULL, &img, EXR_COMPRESSION_HTJ2K32);
            if (!EXR_OK(rc)) { ok = 0; continue; }
            memset(&dec, 0, sizeof(dec));
            rc = exr_load_from_memory(buf, sz, NULL, &dec);
            free(buf);
            if (!EXR_OK(rc) || dec.parts[0].header.num_channels != 3) {
                ok = 0;
            } else {
                if (memcmp(dec.parts[0].images[0], cases[k].b, cases[k].bytes) ||
                    memcmp(dec.parts[0].images[1], cases[k].g, cases[k].bytes) ||
                    memcmp(dec.parts[0].images[2], cases[k].r, cases[k].bytes))
                    ok = 0;
                exr_image_free(&dec);
            }
        }
    }
    CHECK(ok, "3-channel RGB HTJ2K (RCT) round-trips losslessly (HALF+FLOAT)");
    if (ok) printf("  ok: 3-channel HTJ2K RCT round-trips (mc_trans=1)\n");
}

/* Encode a UINT-only file and decode it losslessly. */
static void jph_encode_uint_roundtrip(void) {
    exr_image img, dec;
    exr_part part;
    exr_channel channels[1];
    void *images[1];
    /* 3x2 UINT "Z" with a range covering the full 32-bit width including
     * the high bit, plus zero, to exercise the zero-extension path. */
    uint32_t pixels[6] = {0u, 1u, 0x7fffffffu, 0x80000000u, 0xffffffffu,
                          0xdeadbeefu};
    exr_result rc;
    memset(&img, 0, sizeof(img));
    img.num_parts = 1;
    img.parts = &part;
    memset(&part, 0, sizeof(part));
    part.header.num_channels = 1;
    part.header.channels = channels;
    memset(channels, 0, sizeof(channels));
    channels[0] = (exr_channel){"Z", EXR_PIXEL_UINT, 1, 1, 0};
    part.header.data_window.min_x = 0;
    part.header.data_window.min_y = 0;
    part.header.data_window.max_x = 2;
    part.header.data_window.max_y = 1;
    part.header.display_window = part.header.data_window;
    part.width = 3;
    part.height = 2;
    part.images = images;
    images[0] = pixels;
    part.header.compression = EXR_COMPRESSION_HTJ2K32;
    {
        void *buf = NULL;
        size_t sz = 0;
        rc = exr_save_to_memory(&buf, &sz, NULL, &img, EXR_COMPRESSION_HTJ2K32);
        if (rc != EXR_SUCCESS) {
            g_fail++;
            printf("  FAIL: HTJ2K UINT encode: %s\n", exr_result_string(rc));
            return;
        }
        memset(&dec, 0, sizeof(dec));
        rc = exr_load_from_memory(buf, sz, NULL, &dec);
        free(buf);
        if (!EXR_OK(rc)) {
            g_fail++;
            printf("  FAIL: HTJ2K UINT decode: %s\n", exr_result_string(rc));
            return;
        }
    }
    if (dec.num_parts != 1 || dec.parts[0].header.num_channels != 1) {
        g_fail++;
        printf("  FAIL: HTJ2K UINT roundtrip part/channel count\n");
    } else {
        const unsigned char *got =
            (const unsigned char *)dec.parts[0].images[0];
        if (memcmp(got, pixels, sizeof(pixels)) != 0) {
            g_fail++;
            printf("  FAIL: HTJ2K UINT pixel mismatch\n");
        }
    }
    if (g_fail == 0) {
        g_pass++;
        printf("  ok: HTJ2K UINT encode round-trips losslessly\n");
    }
    exr_image_free(&dec);
}

/* Mixed half + float channels in one HTJ2K codestream must encode and then
 * decode back losslessly (reversible 5/3 + per-component bit depth). */
static void jph_encode_mixed_precision_roundtrip(void) {
    exr_image img, dec;
    exr_part part;
    exr_channel channels[2];
    void *images[2];
    /* 2x2 half "A" and 2x2 float "Z" with non-trivial values. */
    uint16_t half_pixels[4] = {0x3c00, 0x4000, 0xbc00, 0x0001};
    float float_pixels[4] = {0.0f, 1.5f, -2.5f, 12345.678f};
    void *buf = NULL;
    size_t sz = 0;
    exr_result rc;
    int ok = 0;

    memset(&img, 0, sizeof(img));
    memset(&dec, 0, sizeof(dec));
    memset(&part, 0, sizeof(part));
    memset(channels, 0, sizeof(channels));
    memset(images, 0, sizeof(images));

    strcpy(channels[0].name, "A");
    channels[0].pixel_type = EXR_PIXEL_HALF;
    channels[0].x_sampling = 1;
    channels[0].y_sampling = 1;
    strcpy(channels[1].name, "Z");
    channels[1].pixel_type = EXR_PIXEL_FLOAT;
    channels[1].x_sampling = 1;
    channels[1].y_sampling = 1;
    images[0] = half_pixels;
    images[1] = float_pixels;

    part.header.part_type = EXR_PART_SCANLINE;
    part.header.compression = EXR_COMPRESSION_HTJ2K32;
    part.header.line_order = EXR_LINEORDER_INCREASING_Y;
    part.header.data_window.min_x = 0;
    part.header.data_window.min_y = 0;
    part.header.data_window.max_x = 1;
    part.header.data_window.max_y = 1;
    part.header.display_window = part.header.data_window;
    part.header.pixel_aspect_ratio = 1.0f;
    part.header.screen_window_width = 1.0f;
    part.header.num_channels = 2;
    part.header.channels = channels;
    part.width = 2;
    part.height = 2;
    part.images = images;

    img.num_parts = 1;
    img.parts = &part;

    rc = exr_save_to_memory(&buf, &sz, NULL, &img, EXR_COMPRESSION_HTJ2K32);
    if (rc == EXR_SUCCESS && buf && sz) {
        rc = exr_load_from_memory(buf, sz, NULL, &dec);
        if (rc == EXR_SUCCESS && dec.num_parts == 1 &&
            dec.parts[0].header.num_channels == 2) {
            /* channels come back sorted by name: A (half), Z (float) */
            const exr_part *dp = &dec.parts[0];
            ok = memcmp(dp->images[0], half_pixels, sizeof(half_pixels)) == 0 &&
                 memcmp(dp->images[1], float_pixels, sizeof(float_pixels)) == 0;
        }
    }
    CHECK(ok, "HTJ2K mixed HALF/FLOAT encode round-trips losslessly");
    if (ok)
        printf("  ok: HTJ2K mixed HALF/FLOAT encode round-trips losslessly\n");
    else
        printf("  FAIL: HTJ2K mixed precision round-trip rc=%s size=%zu\n",
               exr_result_string(rc), sz);
    if (EXR_OK(rc)) exr_image_free(&dec);
    free(buf);
}

static unsigned rd_u32le(const unsigned char *p) {
    return (unsigned)p[0] | ((unsigned)p[1] << 8) | ((unsigned)p[2] << 16) |
           ((unsigned)p[3] << 24);
}

static unsigned long long rd_u64le(const unsigned char *p) {
    return (unsigned long long)rd_u32le(p) |
           ((unsigned long long)rd_u32le(p + 4) << 32);
}

static int first_scanline_payload(void *buf, size_t sz, size_t *payload,
                                  unsigned *payload_size) {
    unsigned char *p = (unsigned char *)buf;
    size_t pos = 8;
    unsigned long long chunk_off;

    while (pos < sz && p[pos] != 0) {
        int32_t attr_size;
        while (pos < sz && p[pos] != 0) pos++;
        if (pos >= sz) return 0;
        pos++;
        while (pos < sz && p[pos] != 0) pos++;
        if (pos >= sz || pos + 5 > sz) return 0;
        pos++;
        attr_size = (int32_t)rd_u32le(p + pos);
        pos += 4;
        if (attr_size < 0 || pos + (size_t)attr_size > sz) return 0;
        pos += (size_t)attr_size;
    }
    if (pos >= sz || pos + 9 > sz) return 0;
    pos++;
    chunk_off = rd_u64le(p + pos);
    if (chunk_off > sz || (size_t)chunk_off + 8 > sz) return 0;
    *payload_size = rd_u32le(p + (size_t)chunk_off + 4);
    *payload = (size_t)chunk_off + 8;
    return *payload + *payload_size <= sz;
}

static void zero_image(exr_image *img) {
    int p, c;
    for (p = 0; p < img->num_parts; ++p) {
        exr_part *part = &img->parts[p];
        for (c = 0; c < part->header.num_channels; ++c) {
            size_t ps =
                part->header.channels[c].pixel_type == EXR_PIXEL_HALF ? 2 : 4;
            memset(part->images[c], 0, (size_t)part->width * part->height * ps);
        }
    }
}

/* Load -> save (codec) -> reload -> must equal the original. */
static void roundtrip(const char *path, exr_compression comp, const char *name) {
    exr_image src, back;
    void *buf = NULL;
    size_t sz = 0;
    exr_result rc;
    memset(&src, 0, sizeof(src));
    memset(&back, 0, sizeof(back));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (roundtrip %s)\n", path, name);
        return;
    }
    rc = exr_save_to_memory(&buf, &sz, NULL, &src, comp);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: save %s: %s\n", name, exr_result_string(rc));
        exr_image_free(&src);
        return;
    }
    rc = exr_load_from_memory(buf, sz, NULL, &back);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: reload %s: %s\n", name, exr_result_string(rc));
    } else {
        CHECK(back.parts[0].header.compression == comp, name);
        CHECK(images_equal(&src, &back), name);
        printf("  ok: roundtrip %s (%s, %zu bytes)\n", name, path, sz);
    }
    free(buf);
    exr_image_free(&src);
    exr_image_free(&back);
}

/* Build a tiled image from a scanline source in-memory, save tiled, reload. */
static void tiled_roundtrip(const char *path, exr_compression comp,
                            const char *name) {
    exr_image src, back;
    void *buf = NULL;
    size_t sz = 0;
    exr_result rc;
    memset(&src, 0, sizeof(src));
    memset(&back, 0, sizeof(back));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (tiled rt)\n", path);
        return;
    }
    src.parts[0].header.tiled = 1;
    src.parts[0].header.part_type = EXR_PART_TILED;
    src.parts[0].header.tile_x_size = 64;
    src.parts[0].header.tile_y_size = 64;
    src.parts[0].header.level_mode = EXR_TILE_ONE_LEVEL;
    src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    rc = exr_save_to_memory(&buf, &sz, NULL, &src, comp);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: tiled save: %s\n", exr_result_string(rc));
        exr_image_free(&src);
        return;
    }
    rc = exr_load_from_memory(buf, sz, NULL, &back);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: tiled reload: %s\n", exr_result_string(rc));
    } else {
        CHECK(back.parts[0].header.tiled, "tiled flag preserved");
        CHECK(back.parts[0].header.compression == comp, name);
        CHECK(images_equal(&src, &back), "tiled roundtrip pixels");
        printf("  ok: tiled roundtrip (%s, %s, %zu bytes)\n", path, name, sz);
    }
    free(buf);
    exr_image_free(&src);
    exr_image_free(&back);
}

static void zstd_corruption_rejects(const char *path) {
    exr_image src, back;
    void *buf = NULL;
    size_t sz = 0, payload = 0;
    unsigned payload_size = 0;
    exr_result rc;
    memset(&src, 0, sizeof(src));
    memset(&back, 0, sizeof(back));

    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (zstd corrupt test)\n", path);
        return;
    }
    zero_image(&src);
    rc = exr_save_to_memory(&buf, &sz, NULL, &src, EXR_COMPRESSION_ZSTD);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: zstd save for corruption test: %s\n",
               exr_result_string(rc));
        exr_image_free(&src);
        return;
    }
    if (!first_scanline_payload(buf, sz, &payload, &payload_size) ||
        payload_size == 0) {
        g_fail++;
        printf("  FAIL: could not locate zstd payload\n");
        free(buf);
        exr_image_free(&src);
        return;
    }
    ((unsigned char *)buf)[payload] ^= 0xffu;
    rc = exr_load_from_memory(buf, sz, NULL, &back);
    CHECK(!EXR_OK(rc), "corrupted zstd payload rejected");
    if (EXR_OK(rc)) exr_image_free(&back);
    printf("  ok: corrupted zstd payload rejected\n");
    free(buf);
    exr_image_free(&src);
}

static int test_put_u8(uint8_t **p, uint8_t *end, uint8_t v) {
    if (*p >= end) return 0;
    *(*p)++ = v;
    return 1;
}

static int test_put_be16(uint8_t **p, uint8_t *end, uint16_t v) {
    return test_put_u8(p, end, (uint8_t)(v >> 8)) &&
           test_put_u8(p, end, (uint8_t)v);
}

static int test_put_be32(uint8_t **p, uint8_t *end, uint32_t v) {
    return test_put_u8(p, end, (uint8_t)(v >> 24)) &&
           test_put_u8(p, end, (uint8_t)(v >> 16)) &&
           test_put_u8(p, end, (uint8_t)(v >> 8)) &&
           test_put_u8(p, end, (uint8_t)v);
}

static int test_put_bytes(uint8_t **p, uint8_t *end, const uint8_t *src,
                          size_t n) {
    if ((size_t)(end - *p) < n) return 0;
    memcpy(*p, src, n);
    *p += n;
    return 1;
}

static size_t test_make_jph_profile_n(uint8_t *buf, size_t cap, uint16_t nch,
                                      uint8_t mc_trans,
                                      const uint8_t *tile_payload,
                                      size_t tile_payload_size) {
    uint8_t *p = buf;
    uint8_t *end = buf + cap;
    uint32_t psot;
    size_t i, payload_len;

    if (!buf || !tile_payload || nch == 0) return 0;
    if (tile_payload_size > UINT32_MAX - 14u) return 0;
    payload_len = 2u + (size_t)nch * 2u;
    if (payload_len > UINT32_MAX) return 0;
    psot = 14u + (uint32_t)tile_payload_size;

    if (!test_put_be16(&p, end, 0x4854u) ||
        !test_put_be32(&p, end, (uint32_t)payload_len) ||
        !test_put_be16(&p, end, nch))
        return 0;
    for (i = 0; i < nch; ++i)
        if (!test_put_be16(&p, end, (uint16_t)i)) return 0;
    if (!test_put_be16(&p, end, 0xff4fu) ||
        !test_put_be16(&p, end, 0xff51u) ||
        !test_put_be16(&p, end, (uint16_t)(38u + 3u * nch)) ||
        !test_put_be16(&p, end, 0x4000u) ||
        !test_put_be32(&p, end, 1u) || !test_put_be32(&p, end, 1u) ||
        !test_put_be32(&p, end, 0u) || !test_put_be32(&p, end, 0u) ||
        !test_put_be32(&p, end, 1u) || !test_put_be32(&p, end, 1u) ||
        !test_put_be32(&p, end, 0u) || !test_put_be32(&p, end, 0u) ||
        !test_put_be16(&p, end, nch))
        return 0;
    for (i = 0; i < nch; ++i) {
        if (!test_put_u8(&p, end, 0x8fu) ||
            !test_put_u8(&p, end, 1u) || !test_put_u8(&p, end, 1u))
            return 0;
    }
    if (!test_put_be16(&p, end, 0xff50u) ||
        !test_put_be16(&p, end, 6u) ||
        !test_put_be32(&p, end, 0x00020000u) ||
        !test_put_be16(&p, end, 0xff52u) ||
        !test_put_be16(&p, end, 12u) ||
        !test_put_u8(&p, end, 0u) || !test_put_u8(&p, end, 2u) ||
        !test_put_be16(&p, end, 1u) ||
        !test_put_u8(&p, end, mc_trans) || !test_put_u8(&p, end, 5u) ||
        !test_put_u8(&p, end, 5u) || !test_put_u8(&p, end, 3u) ||
        !test_put_u8(&p, end, 0x40u) || !test_put_u8(&p, end, 1u) ||
        !test_put_be16(&p, end, 0xff5cu) ||
        !test_put_be16(&p, end, 19u) ||
        !test_put_u8(&p, end, 0u))
        return 0;
    for (i = 0; i < 16; ++i)
        if (!test_put_u8(&p, end, 0x40u)) return 0;
    if (!test_put_be16(&p, end, 0xff76u) ||
        !test_put_be16(&p, end, 6u) ||
        !test_put_be16(&p, end, 0xffffu) ||
        !test_put_u8(&p, end, 0x8fu) || !test_put_u8(&p, end, 3u) ||
        !test_put_be16(&p, end, 0xff90u) ||
        !test_put_be16(&p, end, 10u) ||
        !test_put_be16(&p, end, 0u) ||
        !test_put_be32(&p, end, psot) ||
        !test_put_u8(&p, end, 0u) || !test_put_u8(&p, end, 1u) ||
        !test_put_be16(&p, end, 0xff93u) ||
        !test_put_bytes(&p, end, tile_payload, tile_payload_size) ||
        !test_put_be16(&p, end, 0xffd9u))
        return 0;
    return (size_t)(p - buf);
}

static size_t test_make_jph_profile(uint8_t *buf, size_t cap,
                                    const uint8_t *tile_payload,
                                    size_t tile_payload_size) {
    return test_make_jph_profile_n(buf, cap, 1u, 0u, tile_payload,
                                   tile_payload_size);
}

static void jph_frontend_rejects_malformed(void) {
    exr_channel ch;
    exr_channel ch3[3];
    exr_codec_ctx ctx;
    exr_codec_ctx ctx3;
    uint8_t dst[2] = {0, 0};
    uint8_t dst3[6] = {1, 2, 3, 4, 5, 6};
    uint8_t packet_ok[256];
    uint8_t packet_short[256];
    uint8_t packet_bad_scup[256];
    uint8_t packet_empty[256];
    uint8_t packet_empty_rct[256];
    uint8_t packet_bad_stuffing[256];
    size_t packet_ok_size, packet_short_size, packet_bad_scup_size;
    size_t packet_empty_size, packet_empty_rct_size, packet_bad_stuffing_size;
    const uint8_t bad_magic[] = {0x00, 0x00, 0x00, 0x00};
    const uint8_t no_codestream[] = {
        0x48, 0x54, 0x00, 0x00, 0x00, 0x04, 0x00, 0x01, 0x00, 0x00
    };
    const uint8_t only_soc[] = {
        0x48, 0x54, 0x00, 0x00, 0x00, 0x04, 0x00, 0x01, 0x00, 0x00,
        0xff, 0x4f
    };
    const uint8_t valid_profile_unsupported[] = {
        /* OpenEXR HT wrapper: magic, payload length, one-channel map. */
        0x48, 0x54, 0x00, 0x00, 0x00, 0x04, 0x00, 0x01, 0x00, 0x00,
        /* SOC */
        0xff, 0x4f,
        /* SIZ: HT profile, 1x1 image/tile, one signed 16-bit component. */
        0xff, 0x51, 0x00, 0x29, 0x40, 0x00,
        0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x01, 0x8f, 0x01, 0x01,
        /* CAP: Pcap bit for HTJ2K. */
        0xff, 0x50, 0x00, 0x06, 0x00, 0x02, 0x00, 0x00,
        /* COD: RPCL, one layer, no RCT, 5 decomps, 128x32 HT block, 5/3. */
        0xff, 0x52, 0x00, 0x0c, 0x00, 0x02, 0x00, 0x01,
        0x00, 0x05, 0x05, 0x03, 0x40, 0x01,
        /* QCD: reversible scalar quantization for 16 subbands. */
        0xff, 0x5c, 0x00, 0x13, 0x00,
        0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,
        0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,
        /* NLT: component 0, signed 16-bit, type 3. */
        0xff, 0x76, 0x00, 0x06, 0x00, 0x00, 0x8f, 0x03,
        /* SOT/SOD: one-byte tile payload, then EOC. */
        0xff, 0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x0f, 0x00, 0x01, 0xff, 0x93, 0x00, 0xff, 0xd9
    };
    const uint8_t nonempty_packet_payload[] = {
        0xe2, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    };
    const uint8_t short_packet_payload[] = {0xe2, 0x02};
    const uint8_t bad_scup_packet_payload[] = {0xe2, 0x00, 0x00};
    const uint8_t bad_stuffing_packet_payload[] = {
        0xe4, 0xff, 0x80, 0x02, 0x00
    };
    const uint8_t empty_packet_payload[] = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    };
    const uint8_t empty_rct_packet_payload[] = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    };

    memset(&ch, 0, sizeof(ch));
    strcpy(ch.name, "A");
    ch.pixel_type = EXR_PIXEL_HALF;
    ch.x_sampling = 1;
    ch.y_sampling = 1;
    memset(ch3, 0, sizeof(ch3));
    strcpy(ch3[0].name, "B");
    strcpy(ch3[1].name, "G");
    strcpy(ch3[2].name, "R");
    ch3[0].pixel_type = EXR_PIXEL_HALF;
    ch3[1].pixel_type = EXR_PIXEL_HALF;
    ch3[2].pixel_type = EXR_PIXEL_HALF;
    ch3[0].x_sampling = ch3[1].x_sampling = ch3[2].x_sampling = 1;
    ch3[0].y_sampling = ch3[1].y_sampling = ch3[2].y_sampling = 1;

    memset(&ctx, 0, sizeof(ctx));
    ctx.compression = EXR_COMPRESSION_HTJ2K32;
    ctx.channels = &ch;
    ctx.num_channels = 1;
    ctx.width = 1;
    ctx.num_lines = 1;
    memset(&ctx3, 0, sizeof(ctx3));
    ctx3.compression = EXR_COMPRESSION_HTJ2K32;
    ctx3.channels = ch3;
    ctx3.num_channels = 3;
    ctx3.width = 1;
    ctx3.num_lines = 1;

    packet_ok_size = test_make_jph_profile(packet_ok, sizeof(packet_ok),
                                           nonempty_packet_payload,
                                           sizeof(nonempty_packet_payload));
    packet_short_size = test_make_jph_profile(packet_short,
                                              sizeof(packet_short),
                                              short_packet_payload,
                                              sizeof(short_packet_payload));
    packet_bad_scup_size = test_make_jph_profile(packet_bad_scup,
                                                 sizeof(packet_bad_scup),
                                                 bad_scup_packet_payload,
                                                 sizeof(bad_scup_packet_payload));
    packet_empty_size = test_make_jph_profile(packet_empty,
                                              sizeof(packet_empty),
                                              empty_packet_payload,
                                              sizeof(empty_packet_payload));
    packet_empty_rct_size =
        test_make_jph_profile_n(packet_empty_rct, sizeof(packet_empty_rct),
                                3u, 1u, empty_rct_packet_payload,
                                sizeof(empty_rct_packet_payload));
    packet_bad_stuffing_size =
        test_make_jph_profile(packet_bad_stuffing,
                              sizeof(packet_bad_stuffing),
                              bad_stuffing_packet_payload,
                              sizeof(bad_stuffing_packet_payload));

    CHECK(exr_lines_per_block(EXR_COMPRESSION_HTJ2K32) == 32,
          "HTJ2K32 line count");
    CHECK(exr_lines_per_block(EXR_COMPRESSION_HTJ2K256) == 256,
          "HTJ2K256 line count");
    CHECK(exr_jph_decompress(&ctx, bad_magic, sizeof(bad_magic), dst,
                             sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH bad magic rejected");
    CHECK(exr_jph_decompress(&ctx, no_codestream, sizeof(no_codestream), dst,
                             sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH empty codestream rejected");
    CHECK(exr_jph_decompress(&ctx, only_soc, sizeof(only_soc), dst,
                             sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH truncated codestream rejected");
    CHECK(exr_jph_decompress(&ctx, valid_profile_unsupported,
                             sizeof(valid_profile_unsupported), dst,
                             sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH incomplete RPCL packet sequence rejected");
    dst[0] = 0x7a;
    dst[1] = 0x55;
    CHECK(packet_empty_size != 0 &&
              exr_jph_decompress(&ctx, packet_empty, packet_empty_size, dst,
                                 sizeof(dst)) == EXR_SUCCESS &&
              dst[0] == 0 && dst[1] == 0,
          "JPH complete all-empty packet sequence decodes zero block");
    CHECK(packet_empty_rct_size != 0 &&
              exr_jph_decompress(&ctx3, packet_empty_rct,
                                 packet_empty_rct_size, dst3,
                                 sizeof(dst3)) == EXR_SUCCESS &&
              memcmp(dst3, "\0\0\0\0\0\0", sizeof(dst3)) == 0,
          "JPH all-empty RCT packet sequence decodes zero RGB block");
    {
        test_alloc_stats stats;
        exr_allocator counting_alloc;
        memset(&stats, 0, sizeof(stats));
        counting_alloc.user = &stats;
        counting_alloc.alloc = test_counting_alloc;
        counting_alloc.free = test_counting_free;
        ctx.alloc = &counting_alloc;
        dst[0] = 0x11;
        dst[1] = 0x22;
        CHECK(exr_jph_decompress(&ctx, packet_empty, packet_empty_size, dst,
                                 sizeof(dst)) == EXR_SUCCESS &&
                  stats.allocs == stats.frees &&
                  dst[0] == 0 && dst[1] == 0,
              "JPH decode balances custom allocator allocations");
        ctx.alloc = NULL;
    }
    CHECK(packet_ok_size != 0 &&
              exr_jph_decompress(&ctx, packet_ok, packet_ok_size, dst,
                                 sizeof(dst)) == EXR_SUCCESS,
          "JPH non-empty packet entropy decode completes");
    CHECK(packet_short_size != 0 &&
              exr_jph_decompress(&ctx, packet_short, packet_short_size, dst,
                                 sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH packet codeblock byte overrun rejected");
    CHECK(packet_bad_scup_size != 0 &&
              exr_jph_decompress(&ctx, packet_bad_scup,
                                 packet_bad_scup_size, dst,
                                 sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH packet cleanup segment footer rejected");
    CHECK(packet_bad_stuffing_size != 0 &&
              exr_jph_decompress(&ctx, packet_bad_stuffing,
                                 packet_bad_stuffing_size, dst,
                                 sizeof(dst)) == EXR_ERROR_CORRUPT,
          "JPH packet stuffed MagSgn byte rejected");
    printf("  ok: HTJ2K/JPH front end rejects malformed payloads\n");
}

static int64_t test_floor_div_pow2(int64_t v, unsigned shift) {
    int64_t d = (int64_t)1 << shift;
    if (v >= 0) return v / d;
    return -(((-v) + d - 1) / d);
}

static void test_forward_53(const int32_t *src, size_t n, int32_t *low,
                            int32_t *high) {
    size_t nl = (n + 1u) / 2u;
    size_t nh = n / 2u;
    size_t i;
    for (i = 0; i < nh; ++i) {
        int64_t e0 = src[2u * i];
        int64_t e1 = (i + 1u < nl) ? src[2u * (i + 1u)] : e0;
        high[i] = (int32_t)((int64_t)src[2u * i + 1u] -
                            test_floor_div_pow2(e0 + e1, 1));
    }
    for (i = 0; i < nl; ++i) {
        int64_t dl = high[i > 0 ? i - 1u : 0u];
        int64_t dr = high[i < nh ? i : nh - 1u];
        low[i] = (int32_t)((int64_t)src[2u * i] +
                           test_floor_div_pow2(dl + dr + 2, 2));
    }
}

static size_t test_ceil_div_pow2_size(size_t v, unsigned shift) {
    while (shift--) v = (v + 1u) / 2u;
    return v;
}

static void test_forward_53_2d(int32_t *data, size_t width, size_t height,
                               unsigned levels) {
    unsigned level;
    for (level = 1; level <= levels; ++level) {
        size_t rw = test_ceil_div_pow2_size(width, level - 1u);
        size_t rh = test_ceil_div_pow2_size(height, level - 1u);
        size_t lw = (rw + 1u) / 2u, hw = rw / 2u;
        size_t lh = (rh + 1u) / 2u, hh = rh / 2u;
        int32_t temp[32], line[8], low[8], high[8];
        size_t x, y;

        memset(temp, 0, sizeof(temp));
        for (x = 0; x < rw; ++x) {
            for (y = 0; y < rh; ++y) line[y] = data[y * width + x];
            test_forward_53(line, rh, low, high);
            for (y = 0; y < lh; ++y) temp[y * rw + x] = low[y];
            for (y = 0; y < hh; ++y) temp[(lh + y) * rw + x] = high[y];
        }
        for (y = 0; y < rh; ++y) {
            test_forward_53(temp + y * rw, rw, low, high);
            for (x = 0; x < lw; ++x) data[y * width + x] = low[x];
            for (x = 0; x < hw; ++x) data[y * width + lw + x] = high[x];
        }
    }
}

static void jph_transforms_roundtrip(void) {
    const int32_t signal[] = {7, -3, 12, 19, -8, 5, 4, -11, 2};
    const int32_t tile_src[20] = {
        5, -1, 7,  9, -4,
        2, 11, 0, -3,  8,
       -6,  4, 3, 12, -9,
        1, -8, 6, 10,  2
    };
    int32_t tile[20];
    int32_t low[5], high[4], recon[9];
    int32_t r[] = {10, -20, 300, -400};
    int32_t g[] = {3, 8, -30, 100};
    int32_t b[] = {-5, 40, 7, -9};
    int32_t y[4], db[4], dr[4];
    int32_t nlt16[] = {-32768, -123, -1, 0, 1, 32767};
    const int32_t nlt16_orig[] = {-32768, -123, -1, 0, 1, 32767};
    int32_t nlt32[] = {INT32_MIN, -1000000, -1, 0, 1, INT32_MAX};
    const int32_t nlt32_orig[] = {INT32_MIN, -1000000, -1, 0, 1, INT32_MAX};
    size_t i;

    test_forward_53(signal, 9, low, high);
    memset(recon, 0, sizeof(recon));
    CHECK(exr_jph_inverse_53_i32(low, 5, high, 4, recon, 9) == EXR_SUCCESS &&
              memcmp(signal, recon, sizeof(signal)) == 0,
          "JPH inverse 5/3 roundtrip");
    memcpy(tile, tile_src, sizeof(tile));
    test_forward_53_2d(tile, 5, 4, 2);
    CHECK(exr_jph_inverse_53_2d_i32(NULL, tile, 5, 4, 2) == EXR_SUCCESS &&
              memcmp(tile, tile_src, sizeof(tile)) == 0,
          "JPH inverse 2D 5/3 roundtrip");

    for (i = 0; i < 4; ++i) {
        y[i] = (int32_t)test_floor_div_pow2((int64_t)r[i] + 2 * (int64_t)g[i] +
                                                (int64_t)b[i],
                                            2);
        db[i] = b[i] - g[i];
        dr[i] = r[i] - g[i];
    }
    CHECK(exr_jph_inverse_rct_i32(y, db, dr, 4) == EXR_SUCCESS,
          "JPH inverse RCT returns success");
    CHECK(memcmp(y, r, sizeof(r)) == 0 && memcmp(db, g, sizeof(g)) == 0 &&
              memcmp(dr, b, sizeof(b)) == 0,
          "JPH inverse RCT roundtrip");
    CHECK(exr_jph_apply_nlt_type3_i32(nlt16, 6, 16) == EXR_SUCCESS &&
              exr_jph_apply_nlt_type3_i32(nlt16, 6, 16) == EXR_SUCCESS &&
              memcmp(nlt16, nlt16_orig, sizeof(nlt16)) == 0,
          "JPH NLT type 3 16-bit involution");
    CHECK(exr_jph_apply_nlt_type3_i32(nlt32, 6, 32) == EXR_SUCCESS &&
              exr_jph_apply_nlt_type3_i32(nlt32, 6, 32) == EXR_SUCCESS &&
              memcmp(nlt32, nlt32_orig, sizeof(nlt32)) == 0,
          "JPH NLT type 3 32-bit involution");
    printf("  ok: HTJ2K/JPH reversible transforms round-trip\n");
}

static void jph_packet_helpers(void) {
    const exr_allocator *a = exr_default_allocator();
    exr_jph_bitreader br;
    exr_jph_ht_forward_reader fr;
    exr_jph_ht_reverse_reader rr;
    exr_jph_mel_reader mr;
    exr_jph_tag_tree tree;
    uint32_t v = 0;
    int has_one = 0;
    const uint8_t bits_a5[] = {0xa5};
    const uint8_t stuffed[] = {0xff, 0x00};
    const uint8_t marker[] = {0xff, 0x90};
    const uint8_t ht_forward[] = {0x0d, 0xff, 0x7f};
    const uint8_t ht_forward_bad[] = {0xff, 0x80};
    const uint8_t ht_reverse[] = {0x12, 0x34};
    const uint8_t ht_reverse_stuffed[] = {0x7f, 0x90};
    const uint8_t ht_reverse_bad[] = {0xff, 0x90};
    const uint8_t mel_term[] = {0x00};
    const uint8_t mel_progress[] = {0xe0};
    const uint8_t mel_stuffed[] = {0xff, 0x8f};
    const uint8_t mel_bad[] = {0xff, 0x90};
    const uint8_t tag_known_zero[] = {0x80};
    const uint8_t tag_value_one[] = {0x40};
    const uint8_t pass_one[] = {0x00};
    const uint8_t pass_two[] = {0x80};
    const uint8_t pass_three[] = {0xc0};
    const uint8_t pass_four[] = {0xd0};
    const uint8_t len_one[] = {0x50};
    const uint8_t len_two[] = {0x68};
    const uint8_t len_three[] = {0x79};
    const uint8_t len_extended[] = {0xd4};
    const uint8_t len_placeholder[] = {0x28};
    const uint8_t len_bad_cleanup[] = {0x10};
    uint32_t raw = 0, active = 0, groups = 0, lengths[2] = {0, 0};

    exr_jph_bitreader_init(&br, bits_a5, sizeof(bits_a5));
    CHECK(exr_jph_bitreader_read(&br, 4, &v) == EXR_SUCCESS && v == 0xau,
          "JPH packet bitreader high nibble");
    CHECK(exr_jph_bitreader_read(&br, 4, &v) == EXR_SUCCESS && v == 0x5u,
          "JPH packet bitreader low nibble");

    exr_jph_bitreader_init(&br, stuffed, sizeof(stuffed));
    CHECK(exr_jph_bitreader_read(&br, 15, &v) == EXR_SUCCESS && v == 0x7f80u,
          "JPH packet bitreader byte stuffing");
    exr_jph_bitreader_init(&br, marker, sizeof(marker));
    CHECK(exr_jph_bitreader_read(&br, 9, &v) == EXR_ERROR_CORRUPT,
          "JPH packet bitreader marker guard");

    exr_jph_ht_forward_init(&fr, ht_forward, sizeof(ht_forward), 0xff);
    CHECK(exr_jph_ht_forward_read(&fr, 4, &v) == EXR_SUCCESS && v == 0xdu,
          "JPH HT forward reader low nibble first");
    CHECK(exr_jph_ht_forward_read(&fr, 4, &v) == EXR_SUCCESS && v == 0,
          "JPH HT forward reader high nibble second");
    CHECK(exr_jph_ht_forward_read(&fr, 15, &v) == EXR_SUCCESS && v == 0x7fffu,
          "JPH HT forward reader byte unstuffing");
    exr_jph_ht_forward_init(&fr, ht_forward_bad, sizeof(ht_forward_bad), 0);
    CHECK(exr_jph_ht_forward_read(&fr, 9, &v) == EXR_ERROR_CORRUPT,
          "JPH HT forward reader rejects stuffed high bit");

    exr_jph_ht_reverse_init(&rr, ht_reverse, sizeof(ht_reverse), 0, 0);
    CHECK(exr_jph_ht_reverse_read(&rr, 8, &v) == EXR_SUCCESS && v == 0x34u,
          "JPH HT reverse reader starts at end");
    CHECK(exr_jph_ht_reverse_read(&rr, 8, &v) == EXR_SUCCESS && v == 0x12u,
          "JPH HT reverse reader moves backward");
    exr_jph_ht_reverse_init(&rr, ht_reverse_stuffed,
                            sizeof(ht_reverse_stuffed), 0, 0);
    CHECK(exr_jph_ht_reverse_read(&rr, 15, &v) == EXR_SUCCESS &&
              v == 0x7f90u,
          "JPH HT reverse reader byte unstuffing");
    exr_jph_ht_reverse_init(&rr, ht_reverse_bad, sizeof(ht_reverse_bad), 0, 0);
    CHECK(exr_jph_ht_reverse_read(&rr, 15, &v) == EXR_ERROR_CORRUPT,
          "JPH HT reverse reader rejects stuffed high bit");

    exr_jph_mel_init(&mr, mel_term, sizeof(mel_term));
    CHECK(exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              v == 0 && has_one == 1,
          "JPH MEL terminating zero run");
    exr_jph_mel_init(&mr, mel_progress, sizeof(mel_progress));
    CHECK(exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              v == 0 && has_one == 0 &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              v == 0 && has_one == 0 &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              v == 0 && has_one == 0 &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              v == 1 && has_one == 1,
          "JPH MEL state progression");
    exr_jph_mel_init(&mr, mel_stuffed, sizeof(mel_stuffed));
    CHECK(exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS,
          "JPH MEL accepts 0x8f stuffed byte");
    exr_jph_mel_init(&mr, mel_bad, sizeof(mel_bad));
    CHECK(exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_SUCCESS &&
              exr_jph_mel_get_run(&mr, &v, &has_one) == EXR_ERROR_CORRUPT,
          "JPH MEL rejects overlarge stuffed byte");

    CHECK(exr_jph_tag_tree_init(a, &tree, 1, 1) == EXR_SUCCESS,
          "JPH tag tree init 1x1");
    exr_jph_bitreader_init(&br, tag_known_zero, sizeof(tag_known_zero));
    CHECK(exr_jph_tag_tree_decode(&tree, &br, 0, 0, 1, &v) == EXR_SUCCESS &&
              v == 0,
          "JPH tag tree value zero");
    exr_jph_tag_tree_free(a, &tree);

    CHECK(exr_jph_tag_tree_init(a, &tree, 1, 1) == EXR_SUCCESS,
          "JPH tag tree init 1x1 second");
    exr_jph_bitreader_init(&br, tag_value_one, sizeof(tag_value_one));
    CHECK(exr_jph_tag_tree_decode(&tree, &br, 0, 0, 2, &v) == EXR_SUCCESS &&
              v == 1,
          "JPH tag tree value one");
    exr_jph_tag_tree_free(a, &tree);

    exr_jph_bitreader_init(&br, pass_one, sizeof(pass_one));
    CHECK(exr_jph_packet_read_pass_count(&br, &raw, &active, &groups) ==
              EXR_SUCCESS &&
              raw == 1 && active == 1 && groups == 0,
          "JPH packet one pass");
    exr_jph_bitreader_init(&br, pass_two, sizeof(pass_two));
    CHECK(exr_jph_packet_read_pass_count(&br, &raw, &active, &groups) ==
              EXR_SUCCESS &&
              raw == 2 && active == 2 && groups == 0,
          "JPH packet two passes");
    exr_jph_bitreader_init(&br, pass_three, sizeof(pass_three));
    CHECK(exr_jph_packet_read_pass_count(&br, &raw, &active, &groups) ==
              EXR_SUCCESS &&
              raw == 3 && active == 3 && groups == 0,
          "JPH packet three passes");
    exr_jph_bitreader_init(&br, pass_four, sizeof(pass_four));
    CHECK(exr_jph_packet_read_pass_count(&br, &raw, &active, &groups) ==
              EXR_SUCCESS &&
              raw == 4 && active == 1 && groups == 1,
          "JPH packet placeholder pass group");

    exr_jph_bitreader_init(&br, len_one, sizeof(len_one));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 1, 0, lengths) ==
              EXR_SUCCESS &&
              lengths[0] == 5 && lengths[1] == 0,
          "JPH packet one pass length");
    exr_jph_bitreader_init(&br, len_two, sizeof(len_two));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 2, 0, lengths) ==
              EXR_SUCCESS &&
              lengths[0] == 6 && lengths[1] == 4,
          "JPH packet two pass lengths");
    exr_jph_bitreader_init(&br, len_three, sizeof(len_three));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 3, 0, lengths) ==
              EXR_SUCCESS &&
              lengths[0] == 7 && lengths[1] == 9,
          "JPH packet three pass lengths");
    exr_jph_bitreader_init(&br, len_extended, sizeof(len_extended));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 1, 0, lengths) ==
              EXR_SUCCESS &&
              lengths[0] == 20 && lengths[1] == 0,
          "JPH packet extended Lblock length");
    exr_jph_bitreader_init(&br, len_placeholder, sizeof(len_placeholder));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 1, 1, lengths) ==
              EXR_SUCCESS &&
              lengths[0] == 5 && lengths[1] == 0,
          "JPH packet placeholder length bits");
    exr_jph_bitreader_init(&br, len_bad_cleanup, sizeof(len_bad_cleanup));
    CHECK(exr_jph_packet_read_pass_lengths(&br, 1, 0, lengths) ==
              EXR_ERROR_CORRUPT,
          "JPH packet rejects short cleanup segment");
    printf("  ok: HTJ2K/JPH packet bitreader and tag tree\n");
}

/* fpnge PSHUFB literal encoder: SIMD output must equal scalar, and both must
 * round-trip through the inflater. */
static void fpnge_check(void) {
    const exr_allocator *a = exr_default_allocator();
    static const size_t sizes[] = {0, 1, 16, 17, 1000, 50000};
    size_t s;
    for (s = 0; s < sizeof(sizes) / sizeof(sizes[0]); ++s) {
        size_t n = sizes[s], i;
        uint8_t *src = (uint8_t *)malloc(n ? n : 1);
        uint8_t *c0 = NULL, *c1 = NULL, *dec = NULL;
        size_t l0 = 0, l1 = 0, got = 0;
        unsigned rng = 1234567u;
        for (i = 0; i < n; ++i) {
            rng = rng * 1664525u + 1013904223u;
            src[i] = (uint8_t)((i % 40 < 6) ? (rng >> 9) : (i / 11));
        }
        if (EXR_OK(exr_fpnge_deflate(a, src, n, &c0, &l0, 0)) &&
            EXR_OK(exr_fpnge_deflate(a, src, n, &c1, &l1, 1))) {
            CHECK(l0 == l1 && (l0 == 0 || memcmp(c0, c1, l0) == 0),
                  "fpnge simd==scalar");
            dec = (uint8_t *)malloc(n ? n : 1);
            CHECK(EXR_OK(exr_inflate_zlib(c1, l1, dec, n, &got)) && got == n &&
                      (n == 0 || memcmp(src, dec, n) == 0),
                  "fpnge round-trip");
        } else {
            g_fail++;
        }
        free(src);
        free(c0);
        free(c1);
        free(dec);
    }
    printf("  ok: fpnge PSHUFB encoder (scalar==simd, round-trip)\n");

#if defined(__x86_64__) || defined(__i386__) || defined(_M_X64) || defined(_M_IX86)
    /* SSE4.1 and AVX2 lookup kernels must match the scalar reference exactly. */
    {
        size_t n = 100000, i;
        uint8_t *buf = (uint8_t *)malloc(n);
        uint8_t *ns = (uint8_t *)malloc(n), *ls = (uint8_t *)malloc(n),
                *hs = (uint8_t *)malloc(n);
        uint8_t *nx = (uint8_t *)malloc(n), *lx = (uint8_t *)malloc(n),
                *hx = (uint8_t *)malloc(n);
        uint64_t freqs[286];
        exr_fpnge_table tbl;
        unsigned rng = 42;
        uint32_t caps = exr_simd_capabilities();
        memset(freqs, 0, sizeof(freqs));
        for (i = 0; i < n; ++i) {
            rng = rng * 1664525u + 1013904223u;
            buf[i] = (uint8_t)(rng >> 8);
            freqs[buf[i]]++;
        }
        if (exr_fpnge_build_table(exr_default_allocator(), freqs, &tbl)) {
            exr_fpnge_lookup_scalar(&tbl, buf, n, ns, ls, hs);
            if (caps & EXR_SIMD_SSE41) {
                exr_fpnge_lookup_sse41(&tbl, buf, n, nx, lx, hx);
                CHECK(!memcmp(ns, nx, n) && !memcmp(ls, lx, n) && !memcmp(hs, hx, n),
                      "fpnge sse4.1 lookup == scalar");
            }
            if (caps & EXR_SIMD_AVX2) {
                exr_fpnge_lookup_avx2(&tbl, buf, n, nx, lx, hx);
                CHECK(!memcmp(ns, nx, n) && !memcmp(ls, lx, n) && !memcmp(hs, hx, n),
                      "fpnge avx2 lookup == scalar");
            }
            printf("  ok: fpnge lookup kernels match scalar\n");
        }
        free(buf); free(ns); free(ls); free(hs); free(nx); free(lx); free(hx);
    }
#endif
}

/* ============================================================================
 * B44 perceptual-table correctness (runtime tables == libm reference)
 * ========================================================================== */

static float b44t_h2f(uint16_t h) {
    union { uint32_t i; float f; } u;
    int s = (h >> 15) & 1, e = (h >> 10) & 0x1f, m = h & 0x3ff;
    if (e == 0) {
        if (m == 0) { u.i = (uint32_t)s << 31; return u.f; }
        { float f = (float)m / 1024.0f * (1.0f / 16384.0f); return s ? -f : f; }
    } else if (e == 31) {
        u.i = ((uint32_t)s << 31) | 0x7f800000u | ((uint32_t)m << 13); return u.f;
    }
    u.i = ((uint32_t)s << 31) | ((uint32_t)(e + 112) << 23) | ((uint32_t)m << 13);
    return u.f;
}
static uint16_t b44t_f2h(float f) {
    union { uint32_t i; float f; } u; int s, e, m;
    u.f = f; s = (int)((u.i >> 31) & 1); e = (int)((u.i >> 23) & 0xff);
    m = (int)(u.i & 0x7fffff);
    if (e == 0) return (uint16_t)(s << 15);
    if (e == 255) return (uint16_t)((s << 15) | 0x7c00 | (m >> 13));
    if (e < 113) { if (e < 103) return (uint16_t)(s << 15);
        m = (m | 0x800000) >> (114 - e); return (uint16_t)((s << 15) | (m >> 13)); }
    if (e > 142) return (uint16_t)((s << 15) | 0x7c00);
    return (uint16_t)((s << 15) | ((e - 112) << 10) | (m >> 13));
}

/* The B44 tables are now computed at runtime with a freestanding exp/log. Verify
 * they reproduce the libm-built tables bit-for-bit over the whole half domain. */
static void b44_table_check(void) {
    const uint16_t *exp_t = NULL, *log_t = NULL;
    int i, exp_mis = 0, log_mis = 0;
    exr_b44_debug_tables(&exp_t, &log_t);
    for (i = 0; i < 65536; ++i) {
        uint16_t x = (uint16_t)i, ref;
        if ((x & 0x7c00) == 0x7c00) ref = 0;
        else if (x >= 0x558c && x < 0x8000) ref = 0x7bff;
        else ref = b44t_f2h((float)exp((double)b44t_h2f(x) / 8.0));
        if (ref != exp_t[i]) exp_mis++;
        if ((x & 0x7c00) == 0x7c00) ref = 0;
        else if (x > 0x8000) ref = 0;
        else { float ff = b44t_h2f(x); ref = (ff <= 0.0f) ? 0
                   : b44t_f2h((float)(8.0 * log((double)ff))); }
        if (ref != log_t[i]) log_mis++;
    }
    CHECK(exp_mis == 0, "B44 exp table matches libm reference");
    CHECK(log_mis == 0, "B44 log table matches libm reference");
    if (!exp_mis && !log_mis)
        printf("  ok: B44 runtime tables == libm reference (131072 entries)\n");
    else
        printf("  FAIL: B44 table mismatches exp=%d log=%d\n", exp_mis, log_mis);
}

/* ============================================================================
 * Streaming block API tests
 * ========================================================================== */

/* Decode a part block-by-block, reassemble per channel, and compare to a full
 * read. Assumes x/y sampling == 1 (true for the corpus). Only level-0 blocks
 * are reconstructed (read_part materializes level 0). */
static void stream_decode_check(const char *path, exr_compression comp,
                                int tiled, exr_tile_level_mode lvl,
                                const char *name) {
    exr_image src;
    void *buf = NULL;
    size_t sz = 0;
    exr_reader *r = NULL;
    exr_part ref;
    const exr_header *h;
    uint32_t nb = 0, i;
    int c, ok = 1, xmin, ymin, fullw;
    uint8_t **recon = NULL;
    exr_result rc;

    memset(&src, 0, sizeof(src));
    memset(&ref, 0, sizeof(ref));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (stream decode %s)\n", path, name);
        return;
    }
    if (tiled) {
        src.parts[0].header.tiled = 1;
        src.parts[0].header.part_type = EXR_PART_TILED;
        src.parts[0].header.tile_x_size = 64;
        src.parts[0].header.tile_y_size = 64;
        src.parts[0].header.level_mode = lvl;
        src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    }
    rc = exr_save_to_memory(&buf, &sz, NULL, &src, comp);
    exr_image_free(&src);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: save (stream decode %s)\n", name);
        return;
    }
    if (!EXR_OK(exr_reader_open_memory(buf, sz, NULL, &r)) ||
        !EXR_OK(exr_reader_read_part(r, 0, &ref))) {
        g_fail++;
        printf("  FAIL: open/read (stream decode %s)\n", name);
        if (r) exr_reader_close(r);
        free(buf);
        return;
    }
    h = exr_reader_part_header(r, 0);
    xmin = h->data_window.min_x;
    ymin = h->data_window.min_y;
    fullw = ref.width;

    recon = (uint8_t **)calloc((size_t)h->num_channels, sizeof(uint8_t *));
    for (c = 0; c < h->num_channels; ++c) {
        size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
        recon[c] = (uint8_t *)calloc((size_t)ref.width * ref.height, ps);
    }

    if (!EXR_OK(exr_reader_num_blocks(r, 0, &nb))) ok = 0;
    for (i = 0; ok && i < nb; ++i) {
        exr_block_info bi;
        void *dst;
        uint8_t *tmp;
        if (!EXR_OK(exr_reader_block_info(r, 0, i, &bi))) { ok = 0; break; }
        if (bi.level_x != 0 || bi.level_y != 0) continue; /* level 0 only */
        dst = malloc(bi.uncompressed_size ? bi.uncompressed_size : 1);
        if (!EXR_OK(exr_reader_decode_block(r, 0, i, dst, bi.uncompressed_size))) {
            free(dst);
            ok = 0;
            break;
        }
        tmp = (uint8_t *)malloc((size_t)bi.width * bi.height * 4 + 1);
        for (c = 0; c < h->num_channels; ++c) {
            size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
            int row0 = bi.y0 - ymin, col0 = bi.x0 - xmin, rr;
            if (!EXR_OK(exr_block_extract_channel(h, &bi, dst,
                                                  bi.uncompressed_size, c, tmp))) {
                ok = 0;
                break;
            }
            for (rr = 0; rr < bi.height; ++rr)
                memcpy(recon[c] + ((size_t)(row0 + rr) * fullw + col0) * ps,
                       tmp + (size_t)rr * bi.width * ps, (size_t)bi.width * ps);
        }
        free(tmp);
        free(dst);
    }
    if (ok)
        for (c = 0; c < h->num_channels; ++c) {
            size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
            if (memcmp(recon[c], ref.images[c],
                       (size_t)ref.width * ref.height * ps) != 0)
                ok = 0;
        }
    CHECK(ok, name);
    if (ok) printf("  ok: stream decode %s (%u blocks)\n", name, nb);

    for (c = 0; c < h->num_channels; ++c) free(recon[c]);
    free(recon);
    exr_part_free(NULL, &ref);
    exr_reader_close(r);
    free(buf);
}

/* Encode a part block-by-block via the streaming writer, reload, compare. */
static void stream_encode_check(const char *path, exr_compression comp,
                                int tiled, const char *name) {
    exr_image src, back;
    exr_writer *w = NULL;
    const char *tmp = "build/_stream_enc.exr";
    const exr_header *h;
    int c, ok = 1;

    memset(&src, 0, sizeof(src));
    memset(&back, 0, sizeof(back));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (stream encode %s)\n", path, name);
        return;
    }
    if (tiled) {
        src.parts[0].header.tiled = 1;
        src.parts[0].header.part_type = EXR_PART_TILED;
        src.parts[0].header.tile_x_size = 64;
        src.parts[0].header.tile_y_size = 64;
        src.parts[0].header.level_mode = EXR_TILE_ONE_LEVEL;
        src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    }
    h = &src.parts[0].header;
    if (!EXR_OK(exr_writer_create(NULL, &w)) ||
        !EXR_OK(exr_writer_add_part(w, h, NULL)) ||
        !EXR_OK(exr_writer_begin_stream_file(w, tmp, comp))) {
        g_fail++;
        printf("  FAIL: begin (stream encode %s)\n", name);
        if (w) exr_writer_destroy(w);
        exr_image_free(&src);
        return;
    }

    if (tiled) {
        int W = src.parts[0].width, H = src.parts[0].height;
        int tsx = 64, tsy = 64;
        int nxt = (W + tsx - 1) / tsx, nyt = (H + tsy - 1) / tsy, txi, tyi;
        const void **cd = (const void **)malloc((size_t)h->num_channels * sizeof(void *));
        uint8_t **tb = (uint8_t **)malloc((size_t)h->num_channels * sizeof(void *));
        for (tyi = 0; ok && tyi < nyt; ++tyi)
            for (txi = 0; ok && txi < nxt; ++txi) {
                int x0 = txi * tsx, y0 = tyi * tsy;
                int tw = (tsx < W - x0) ? tsx : (W - x0);
                int th = (tsy < H - y0) ? tsy : (H - y0), rr;
                for (c = 0; c < h->num_channels; ++c) {
                    size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
                    tb[c] = (uint8_t *)malloc((size_t)tw * th * ps);
                    for (rr = 0; rr < th; ++rr)
                        memcpy(tb[c] + (size_t)rr * tw * ps,
                               (uint8_t *)src.parts[0].images[c] +
                                   ((size_t)(y0 + rr) * W + x0) * ps,
                               (size_t)tw * ps);
                    cd[c] = tb[c];
                }
                if (!EXR_OK(exr_writer_write_tile(w, 0, txi, tyi, 0, 0,
                                                  (const void *const *)cd)))
                    ok = 0;
                for (c = 0; c < h->num_channels; ++c) free(tb[c]);
            }
        free(cd);
        free(tb);
    } else {
        int W = src.parts[0].width;
        int ymin = h->data_window.min_y, ymax = h->data_window.max_y;
        int lpb = exr_lines_per_block(comp), y0;
        const void **cd = (const void **)malloc((size_t)h->num_channels * sizeof(void *));
        for (y0 = ymin; ok && y0 <= ymax; y0 += lpb) {
            for (c = 0; c < h->num_channels; ++c) {
                size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
                cd[c] = (uint8_t *)src.parts[0].images[c] +
                        (size_t)(y0 - ymin) * W * ps;
            }
            if (!EXR_OK(exr_writer_write_scanline_block(w, 0, y0,
                                                        (const void *const *)cd)))
                ok = 0;
        }
        free(cd);
    }

    if (ok && !EXR_OK(exr_writer_end_stream(w))) ok = 0;
    exr_writer_destroy(w);
    if (ok && !EXR_OK(exr_load_from_file(tmp, NULL, &back))) ok = 0;
    if (ok) CHECK(images_equal(&src, &back), name);
    else CHECK(0, name);
    if (ok) printf("  ok: stream encode %s\n", name);
    exr_image_free(&src);
    exr_image_free(&back);
}

/* Closed-loop check of streaming-encode tile ordering across all levels:
 * read every tile of a serialize-written mip/ripmap file, re-stream them via
 * exr_writer_write_tile, then verify the result decodes block-for-block
 * identically. Exercises w_tile_index / w_chunk_count for every level mode.
 * Assumes x/y sampling == 1. */
static void stream_tiled_levels_check(const char *path, exr_tile_level_mode lvl,
                                      const char *name) {
    exr_image src;
    void *buf = NULL;
    size_t sz = 0;
    exr_reader *R = NULL, *S = NULL;
    exr_writer *w = NULL;
    const char *tmp = "build/_stream_lvl.exr";
    const exr_header *h;
    exr_block_info *bis = NULL;
    uint8_t ***chan = NULL;
    uint32_t nb = 0, ns = 0, i;
    int c, nch, ok = 1;
    exr_result rc;

    memset(&src, 0, sizeof(src));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (stream levels %s)\n", path, name);
        return;
    }
    src.parts[0].header.tiled = 1;
    src.parts[0].header.part_type = EXR_PART_TILED;
    src.parts[0].header.tile_x_size = 32;
    src.parts[0].header.tile_y_size = 32;
    src.parts[0].header.level_mode = lvl;
    src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    rc = exr_save_to_memory(&buf, &sz, NULL, &src, EXR_COMPRESSION_ZIP);
    exr_image_free(&src);
    if (!EXR_OK(rc)) { g_fail++; printf("  FAIL: save (stream levels %s)\n", name); return; }

    if (!EXR_OK(exr_reader_open_memory(buf, sz, NULL, &R)) ||
        !EXR_OK(exr_reader_num_blocks(R, 0, &nb))) {
        g_fail++; printf("  FAIL: open (stream levels %s)\n", name);
        if (R) exr_reader_close(R);
        free(buf); return;
    }
    h = exr_reader_part_header(R, 0);
    nch = h->num_channels;
    bis = (exr_block_info *)calloc(nb ? nb : 1, sizeof(exr_block_info));
    chan = (uint8_t ***)calloc(nb ? nb : 1, sizeof(uint8_t **));

    /* gather every tile's per-channel planar data */
    for (i = 0; ok && i < nb; ++i) {
        void *blk;
        if (!EXR_OK(exr_reader_block_info(R, 0, i, &bis[i]))) { ok = 0; break; }
        blk = malloc(bis[i].uncompressed_size ? bis[i].uncompressed_size : 1);
        if (!EXR_OK(exr_reader_decode_block(R, 0, i, blk, bis[i].uncompressed_size))) {
            free(blk); ok = 0; break;
        }
        chan[i] = (uint8_t **)calloc(nch ? (size_t)nch : 1, sizeof(uint8_t *));
        for (c = 0; c < nch; ++c) {
            size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
            chan[i][c] = (uint8_t *)malloc((size_t)bis[i].width * bis[i].height * ps);
            if (!EXR_OK(exr_block_extract_channel(h, &bis[i], blk,
                                                  bis[i].uncompressed_size, c,
                                                  chan[i][c])))
                ok = 0;
        }
        free(blk);
    }

    /* re-stream every tile */
    if (ok && EXR_OK(exr_writer_create(NULL, &w)) &&
        EXR_OK(exr_writer_add_part(w, h, NULL)) &&
        EXR_OK(exr_writer_begin_stream_file(w, tmp, EXR_COMPRESSION_ZIP))) {
        for (i = 0; ok && i < nb; ++i)
            if (!EXR_OK(exr_writer_write_tile(w, 0, bis[i].tile_x, bis[i].tile_y,
                                              bis[i].level_x, bis[i].level_y,
                                              (const void *const *)chan[i])))
                ok = 0;
        if (ok && !EXR_OK(exr_writer_end_stream(w))) ok = 0;
        exr_writer_destroy(w);
    } else {
        ok = 0;
        if (w) exr_writer_destroy(w);
    }

    /* verify the streamed file decodes block-for-block identically */
    if (ok) {
        /* reopen from file via a fresh reader */
        {
            void *fb = NULL;
            size_t fsz = 0;
            FILE *fp = fopen(tmp, "rb");
            if (fp) {
                fseek(fp, 0, SEEK_END); fsz = (size_t)ftell(fp); fseek(fp, 0, SEEK_SET);
                fb = malloc(fsz ? fsz : 1);
                if (fb && fread(fb, 1, fsz, fp) != fsz) ok = 0;
                fclose(fp);
            } else ok = 0;
            if (ok && EXR_OK(exr_reader_open_memory(fb, fsz, NULL, &S)) &&
                EXR_OK(exr_reader_num_blocks(S, 0, &ns)) && ns == nb) {
                for (i = 0; ok && i < nb; ++i) {
                    exr_block_info bs;
                    void *ds, *dr;
                    if (!EXR_OK(exr_reader_block_info(S, 0, i, &bs))) { ok = 0; break; }
                    if (bs.uncompressed_size != bis[i].uncompressed_size) { ok = 0; break; }
                    ds = malloc(bs.uncompressed_size ? bs.uncompressed_size : 1);
                    dr = malloc(bis[i].uncompressed_size ? bis[i].uncompressed_size : 1);
                    if (!EXR_OK(exr_reader_decode_block(S, 0, i, ds, bs.uncompressed_size)) ||
                        !EXR_OK(exr_reader_decode_block(R, 0, i, dr, bis[i].uncompressed_size)) ||
                        memcmp(ds, dr, bs.uncompressed_size) != 0)
                        ok = 0;
                    free(ds); free(dr);
                }
            } else ok = 0;
            if (S) exr_reader_close(S);
            free(fb);
        }
    }

    CHECK(ok, name);
    if (ok) printf("  ok: stream tiled levels %s (%u blocks)\n", name, nb);

    for (i = 0; i < nb; ++i)
        if (chan && chan[i]) {
            for (c = 0; c < nch; ++c) free(chan[i][c]);
            free(chan[i]);
        }
    free(chan);
    free(bis);
    exr_reader_close(R);
    free(buf);
}

/* Regression: a deep-tiled file with a non-monotonic (attacker-controlled)
 * per-pixel offset table must be rejected, not crash with a heap OOB. Builds a
 * tiny deep-tiled image, saves it uncompressed (so the offset table is stored
 * verbatim), corrupts the cumulative table to be decreasing, and reloads. */
static void deep_tiled_oob_rejects(void) {
    exr_channel ch;
    exr_part part;
    exr_image img, back;
    int32_t counts[4] = {1, 1, 1, 1};
    float samples[4] = {1.0f, 2.0f, 3.0f, 4.0f};
    void *zimg[1];
    void *buf = NULL;
    size_t sz = 0, i;
    uint8_t pat[16], rep[16];
    int found = 0;
    exr_result rc;

    memset(&ch, 0, sizeof(ch));
    strcpy(ch.name, "Z");
    ch.pixel_type = EXR_PIXEL_FLOAT;
    ch.x_sampling = 1;
    ch.y_sampling = 1;
    memset(&part, 0, sizeof(part));
    part.header.part_type = EXR_PART_DEEP_TILED;
    part.header.compression = EXR_COMPRESSION_NONE;
    part.header.data_window.max_x = 1;
    part.header.data_window.max_y = 1;
    part.header.display_window = part.header.data_window;
    part.header.pixel_aspect_ratio = 1.0f;
    part.header.screen_window_width = 1.0f;
    part.header.num_channels = 1;
    part.header.channels = &ch;
    part.header.tiled = 1;
    part.header.tile_x_size = 2;
    part.header.tile_y_size = 2;
    part.header.level_mode = EXR_TILE_ONE_LEVEL;
    part.header.rounding_mode = EXR_TILE_ROUND_DOWN;
    part.width = 2;
    part.height = 2;
    part.is_deep = 1;
    part.deep_sample_counts = counts;
    zimg[0] = samples;
    part.deep_images = zimg;
    part.deep_total_samples = 4;
    memset(&img, 0, sizeof(img));
    img.num_parts = 1;
    img.parts = &part;

    rc = exr_save_to_memory(&buf, &sz, NULL, &img, EXR_COMPRESSION_NONE);
    if (!EXR_OK(rc)) {
        g_fail++;
        printf("  FAIL: deep-tiled OOB test save: %s\n", exr_result_string(rc));
        return;
    }
    /* positive control: the well-formed file loads */
    memset(&back, 0, sizeof(back));
    if (EXR_OK(exr_load_from_memory(buf, sz, NULL, &back))) exr_image_free(&back);

    /* offset table stored verbatim = cumulative-per-row int32 LE [1,2,1,2]
     * (each tile row restarts); corrupt row 0 to decreasing [2,1,2,1] so pixel
     * (0,1) yields a negative count. */
    {
        static const uint8_t patv[4] = {1, 2, 1, 2};
        static const uint8_t repv[4] = {2, 1, 2, 1};
        for (i = 0; i < 4; ++i) {
            pat[i * 4 + 0] = patv[i]; pat[i * 4 + 1] = 0;
            pat[i * 4 + 2] = 0; pat[i * 4 + 3] = 0;
            rep[i * 4 + 0] = repv[i]; rep[i * 4 + 1] = 0;
            rep[i * 4 + 2] = 0; rep[i * 4 + 3] = 0;
        }
    }
    for (i = 0; sz >= 16 && i + 16 <= sz; ++i) {
        if (memcmp((uint8_t *)buf + i, pat, 16) == 0) {
            memcpy((uint8_t *)buf + i, rep, 16);
            found = 1;
            break;
        }
    }
    CHECK(found, "deep-tiled OOB: located offset table");
    memset(&back, 0, sizeof(back));
    rc = exr_load_from_memory(buf, sz, NULL, &back);
    CHECK(!EXR_OK(rc), "deep-tiled non-monotonic offset table rejected");
    if (EXR_OK(rc)) exr_image_free(&back);
    if (found && !EXR_OK(rc))
        printf("  ok: deep-tiled OOB rejected (%s)\n", exr_result_string(rc));
    free(buf);
}

/* Stream a deep scanline part out block-by-block and verify it round-trips. */
static void stream_deep_check(const char *path, exr_compression comp,
                              const char *name) {
    exr_image src, back;
    exr_writer *w = NULL;
    const char *tmp = "build/_stream_deep.exr";
    const exr_header *h;
    int c, ok = 1, ymin, ymax, lpb, W, y0;
    uint64_t *prefix = NULL;
    size_t npix, i;

    memset(&src, 0, sizeof(src));
    memset(&back, 0, sizeof(back));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        printf("  skip: %s missing (stream deep %s)\n", path, name);
        return;
    }
    if (!src.parts[0].is_deep) {
        printf("  skip: %s not deep\n", path);
        exr_image_free(&src);
        return;
    }
    h = &src.parts[0].header;
    W = src.parts[0].width;
    ymin = h->data_window.min_y;
    ymax = h->data_window.max_y;
    npix = (size_t)W * src.parts[0].height;
    prefix = (uint64_t *)malloc(npix * sizeof(uint64_t));
    {
        uint64_t acc = 0;
        for (i = 0; i < npix; ++i) {
            prefix[i] = acc;
            acc += (uint64_t)src.parts[0].deep_sample_counts[i];
        }
    }
    if (!EXR_OK(exr_writer_create(NULL, &w)) ||
        !EXR_OK(exr_writer_add_part(w, h, NULL)) ||
        !EXR_OK(exr_writer_begin_stream_file(w, tmp, comp))) {
        g_fail++;
        printf("  FAIL: begin (stream deep %s)\n", name);
        if (w) exr_writer_destroy(w);
        free(prefix);
        exr_image_free(&src);
        return;
    }
    lpb = exr_lines_per_block(comp);
    {
        const void **cs = (const void **)malloc((size_t)h->num_channels * sizeof(void *));
        for (y0 = ymin; ok && y0 <= ymax; y0 += lpb) {
            size_t fp = (size_t)(y0 - ymin) * W;
            const int32_t *counts = src.parts[0].deep_sample_counts + fp;
            for (c = 0; c < h->num_channels; ++c) {
                size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
                cs[c] = (uint8_t *)src.parts[0].deep_images[c] + prefix[fp] * ps;
            }
            if (!EXR_OK(exr_writer_write_deep_scanline_block(
                    w, 0, y0, counts, (const void *const *)cs)))
                ok = 0;
        }
        free(cs);
    }
    if (ok && !EXR_OK(exr_writer_end_stream(w))) ok = 0;
    exr_writer_destroy(w);
    free(prefix);
    if (ok && !EXR_OK(exr_load_from_file(tmp, NULL, &back))) ok = 0;
    if (ok) {
        ok = back.parts[0].is_deep &&
             back.parts[0].deep_total_samples ==
                 src.parts[0].deep_total_samples &&
             memcmp(back.parts[0].deep_sample_counts,
                    src.parts[0].deep_sample_counts,
                    npix * sizeof(int32_t)) == 0;
        for (c = 0; ok && c < h->num_channels; ++c) {
            size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
            if (memcmp(back.parts[0].deep_images[c], src.parts[0].deep_images[c],
                       (size_t)src.parts[0].deep_total_samples * ps) != 0)
                ok = 0;
        }
    }
#if defined(EXR_USE_THREADS)
    /* Re-decode the (1-line-per-block) deep image with 4 workers: the parallel
     * pass-2 scatter must reproduce the single-threaded decode bit-for-bit. */
    if (ok) {
        exr_image b4;
        memset(&b4, 0, sizeof(b4));
        exr_set_num_threads(4);
        if (!EXR_OK(exr_load_from_file(tmp, NULL, &b4))) ok = 0;
        else {
            ok = b4.parts[0].deep_total_samples ==
                     back.parts[0].deep_total_samples &&
                 memcmp(b4.parts[0].deep_sample_counts,
                        back.parts[0].deep_sample_counts,
                        npix * sizeof(int32_t)) == 0;
            for (c = 0; ok && c < h->num_channels; ++c) {
                size_t ps = (h->channels[c].pixel_type == EXR_PIXEL_HALF) ? 2 : 4;
                if (memcmp(b4.parts[0].deep_images[c],
                           back.parts[0].deep_images[c],
                           (size_t)back.parts[0].deep_total_samples * ps) != 0)
                    ok = 0;
            }
        }
        exr_set_num_threads(1);
        exr_image_free(&b4);
    }
#endif
    CHECK(ok, name);
    if (ok) printf("  ok: stream deep %s\n", name);
    exr_image_free(&src);
    exr_image_free(&back);
}

static exr_result blocking_read(void *user, uint64_t off, uint64_t len,
                                void *dst) {
    (void)user; (void)off; (void)len; (void)dst;
    return EXR_WOULD_BLOCK; /* force the suspend/resume path */
}

/* Re-issue exr_reader_decode_block while it suspends, feeding the pending range
 * in 64K steps; *fed counts how many supply cycles happened. */
static exr_result stream_drive_decode(exr_reader *rs, const uint8_t *file,
                                      uint32_t blk, void *dst, size_t dst_size,
                                      int *fed) {
    int guard = 0;
    for (;;) {
        exr_result rc = exr_reader_decode_block(rs, 0, blk, dst, dst_size);
        exr_pending_read pr;
        size_t step;
        if (rc != EXR_WOULD_BLOCK) return rc;
        if (!EXR_OK(exr_reader_pending(rs, &pr))) return EXR_ERROR_CORRUPT;
        step = pr.size < 65536u ? (size_t)pr.size : 65536u;
        if (!EXR_OK(exr_reader_supply(rs, file + pr.offset, step)))
            return EXR_ERROR_CORRUPT;
        *fed += 1;
        if (++guard > 2000000) return EXR_ERROR_CORRUPT;
    }
}

/* Decode EVERY block over a streaming source that always blocks, driving the
 * suspend/resume loop through decode_block itself; each block must match the
 * memory-path decode, and the suspend path must actually fire (fed > 0). */
static void stream_would_block_check(const char *path, exr_compression comp,
                                     const char *name) {
    exr_image tmpimg;
    void *buf = NULL;
    size_t sz = 0;
    exr_reader *rm = NULL, *rs = NULL;
    void *ref = NULL, *got = NULL;
    uint32_t nb = 0, b;
    int ok = 1, fed = 0;
    exr_data_source dsrc;

    memset(&tmpimg, 0, sizeof(tmpimg));
    if (!EXR_OK(exr_load_from_file(path, NULL, &tmpimg))) {
        g_fail++;
        printf("  FAIL: %s load (would-block %s)\n", path, name);
        return;
    }
    if (!EXR_OK(exr_save_to_memory(&buf, &sz, NULL, &tmpimg, comp))) {
        g_fail++;
        exr_image_free(&tmpimg);
        return;
    }
    exr_image_free(&tmpimg);

    if (!EXR_OK(exr_reader_open_memory(buf, sz, NULL, &rm)) ||
        !EXR_OK(exr_reader_num_blocks(rm, 0, &nb))) {
        g_fail++; printf("  FAIL: mem setup (would-block %s)\n", name);
        if (rm) exr_reader_close(rm);
        free(buf); return;
    }

    dsrc.user = NULL;
    dsrc.read = blocking_read;
    dsrc.total_size = sz;
    if (!EXR_OK(exr_reader_open_source(&dsrc, NULL, &rs))) {
        g_fail++; exr_reader_close(rm); free(buf); return;
    }
    for (b = 0; b < nb && ok; ++b) {
        exr_block_info bi;
        if (!EXR_OK(exr_reader_block_info(rm, 0, b, &bi))) { ok = 0; break; }
        ref = realloc(ref, bi.uncompressed_size ? bi.uncompressed_size : 1);
        got = realloc(got, bi.uncompressed_size ? bi.uncompressed_size : 1);
        if (!EXR_OK(exr_reader_decode_block(rm, 0, b, ref, bi.uncompressed_size)))
            ok = 0;
        else if (!EXR_OK(stream_drive_decode(rs, (uint8_t *)buf, b, got,
                                             bi.uncompressed_size, &fed)))
            ok = 0;
        else if (memcmp(ref, got, bi.uncompressed_size) != 0)
            ok = 0;
    }
    if (fed == 0) ok = 0; /* the suspend/resume path must have actually run */
    exr_reader_close(rm);
    exr_reader_close(rs);
    CHECK(ok, name);
    if (ok) printf("  ok: stream WOULD_BLOCK %s (%u blocks, %d supplies)\n",
                   name, nb, fed);
    free(ref);
    free(got);
    free(buf);
}

/* Peak-tracking allocator to confirm block streaming bounds working memory. */
typedef struct { size_t live, peak; } memstat;
static void *ms_alloc(void *u, size_t n) {
    memstat *m = (memstat *)u;
    size_t *p = (size_t *)malloc(n + sizeof(size_t));
    if (!p) return NULL;
    p[0] = n;
    m->live += n;
    if (m->live > m->peak) m->peak = m->live;
    return p + 1;
}
static void ms_free(void *u, void *ptr) {
    memstat *m = (memstat *)u;
    size_t *p;
    if (!ptr) return;
    p = (size_t *)ptr - 1;
    m->live -= p[0];
    free(p);
}

static void stream_memory_bound_check(const char *path, exr_compression comp,
                                      const char *name) {
    exr_image tmpimg;
    void *buf = NULL;
    size_t sz = 0, full_peak, stream_peak;
    memstat fm = {0, 0}, sm = {0, 0};
    exr_allocator fa, sa;
    exr_reader *rf = NULL, *rs = NULL;
    exr_part ref;
    uint32_t nb = 0, i;

    memset(&tmpimg, 0, sizeof(tmpimg));
    memset(&ref, 0, sizeof(ref));
    if (!EXR_OK(exr_load_from_file(path, NULL, &tmpimg)) ||
        !EXR_OK(exr_save_to_memory(&buf, &sz, NULL, &tmpimg, comp))) {
        g_fail++;
        printf("  FAIL: setup (memory-bound %s)\n", name);
        if (tmpimg.parts) exr_image_free(&tmpimg);
        return;
    }
    exr_image_free(&tmpimg);

    fa.user = &fm; fa.alloc = ms_alloc; fa.free = ms_free;
    exr_reader_open_memory(buf, sz, &fa, &rf);
    exr_reader_read_part(rf, 0, &ref);
    full_peak = fm.peak;
    exr_part_free(&fa, &ref);
    exr_reader_close(rf);

    sa.user = &sm; sa.alloc = ms_alloc; sa.free = ms_free;
    exr_reader_open_memory(buf, sz, &sa, &rs);
    exr_reader_num_blocks(rs, 0, &nb);
    for (i = 0; i < nb; ++i) {
        exr_block_info bi;
        void *dst;
        if (!EXR_OK(exr_reader_block_info(rs, 0, i, &bi))) break;
        dst = malloc(bi.uncompressed_size ? bi.uncompressed_size : 1); /* caller buffer */
        exr_reader_decode_block(rs, 0, i, dst, bi.uncompressed_size);
        free(dst);
    }
    stream_peak = sm.peak;
    exr_reader_close(rs);

    CHECK(stream_peak * 2 < full_peak, name);
    printf("  %s: full peak=%zu B, stream peak=%zu B\n", name, full_peak,
           stream_peak);
    free(buf);
}

/* JPH SIMD kernels must be bit-identical to their scalar reference. */
static void jph_simd_check(void) {
#if defined(EXR_X86)
    uint32_t caps = exr_simd_capabilities();
    const size_t n = 1003; /* not a multiple of 4 -> exercises SIMD tails */
    int64_t *orig = (int64_t *)malloc(n * sizeof(int64_t));
    int64_t *ref = (int64_t *)malloc(n * sizeof(int64_t));
    int64_t *got = (int64_t *)malloc(n * sizeof(int64_t));
    uint32_t rng = 0xC0FFEEu;
    int bds[2] = {16, 32};
    int ok = 1, k;
    if (!orig || !ref || !got) { free(orig); free(ref); free(got); return; }
    for (k = 0; k < 2; ++k) {
        uint32_t bd = (uint32_t)bds[k];
        int64_t bias = ((int64_t)1 << (bd - 1)) + 1;
        size_t i;
        for (i = 0; i < n; ++i) {
            int64_t v;
            rng = rng * 1664525u + 1013904223u;
            v = (int64_t)(int32_t)rng;                  /* full int32 range */
            if (bd == 32u && (rng & 7u) == 0u) v *= 41; /* widen beyond int32 */
            orig[i] = v;
        }
        memcpy(ref, orig, n * sizeof(int64_t));
        jph_nlt_type3_i64_scalar(ref, n, bias);
        if (caps & EXR_SIMD_SSE2) {
            memcpy(got, orig, n * sizeof(int64_t));
            jph_nlt_type3_i64_sse2(got, n, bias);
            if (memcmp(ref, got, n * sizeof(int64_t)) != 0) ok = 0;
        }
        if (caps & EXR_SIMD_AVX2) {
            memcpy(got, orig, n * sizeof(int64_t));
            jph_nlt_type3_i64_avx2(got, n, bias);
            if (memcmp(ref, got, n * sizeof(int64_t)) != 0) ok = 0;
        }
    }
    CHECK(ok, "JPH NLT type3 SIMD == scalar");
    if (ok) printf("  ok: JPH NLT type3 SIMD == scalar\n");
    free(orig); free(ref); free(got);

    /* int32 -> uint16 pack (all-HALF store): truncation must match scalar even
     * for out-of-int16 values. */
    {
        const size_t pn = 1003;
        int32_t *ps = (int32_t *)malloc(pn * sizeof(int32_t));
        uint8_t *pr = (uint8_t *)malloc(pn * 2);
        uint8_t *px = (uint8_t *)malloc(pn * 2);
        int pok = 1;
        if (ps && pr && px) {
            size_t i;
            uint32_t r2 = 0x12345u;
            for (i = 0; i < pn; ++i) {
                r2 = r2 * 1664525u + 1013904223u;
                ps[i] = (int32_t)r2; /* full int32 range incl. out-of-int16 */
            }
            jph_pack_i32_to_half_scalar(pr, ps, pn);
            if (caps & EXR_SIMD_SSE41) {
                jph_pack_i32_to_half_sse41(px, ps, pn);
                if (memcmp(pr, px, pn * 2) != 0) pok = 0;
            }
            if (caps & EXR_SIMD_AVX2) {
                jph_pack_i32_to_half_avx2(px, ps, pn);
                if (memcmp(pr, px, pn * 2) != 0) pok = 0;
            }
            CHECK(pok, "JPH pack i32->half SIMD == scalar");
            if (pok) printf("  ok: JPH pack i32->half SIMD == scalar\n");
        }
        free(ps); free(pr); free(px);
    }

    /* int32 NLT type3: SIMD must match scalar over several bit depths. */
    {
        const size_t nn = 1003;
        int32_t *ref = (int32_t *)malloc(nn * sizeof(int32_t));
        int32_t *got = (int32_t *)malloc(nn * sizeof(int32_t));
        int32_t *src = (int32_t *)malloc(nn * sizeof(int32_t));
        int bds[3] = {16, 24, 31};
        int nok = 1, k;
        uint32_t rng = 0x9e3779b9u;
        if (ref && got && src) {
            for (k = 0; k < 3 && nok; ++k) {
                int32_t biasm1 = (int32_t)((int64_t)1 << (bds[k] - 1));
                size_t i;
                for (i = 0; i < nn; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    /* mix of small and large, positive and negative */
                    src[i] = (int32_t)rng >> (int)(rng % 24u);
                }
                memcpy(ref, src, nn * sizeof(int32_t));
                jph_nlt_type3_i32_scalar(ref, nn, biasm1);
                if (caps & EXR_SIMD_SSE2) {
                    memcpy(got, src, nn * sizeof(int32_t));
                    jph_nlt_type3_i32_sse2(got, nn, biasm1);
                    if (memcmp(ref, got, nn * sizeof(int32_t)) != 0) nok = 0;
                }
                if (caps & EXR_SIMD_AVX2) {
                    memcpy(got, src, nn * sizeof(int32_t));
                    jph_nlt_type3_i32_avx2(got, nn, biasm1);
                    if (memcmp(ref, got, nn * sizeof(int32_t)) != 0) nok = 0;
                }
            }
            CHECK(nok, "JPH NLT type3 i32 SIMD == scalar");
            if (nok) printf("  ok: JPH NLT type3 i32 SIMD == scalar\n");
        }
        free(ref); free(got); free(src);
    }

    /* HT encode quad prepare: the SSE2 int64- and int32-plane kernels must
     * compute rho / e_q / e_qmax / s / max_val identically to the scalar
     * reference for every quad (full int32 range, incl. zero/insignificant
     * lanes and the float-CLZ boundaries). This guards the prepare against the
     * horizontal-max and sample-order regressions found during development. */
    {
        uint32_t rng = 0x5eed1234u;
        int qok = 1;
        long it;
        for (it = 0; it < 100000 && qok; ++it) {
            int32_t q[4]; /* [s0,s1,s2,s3] = (x,y),(x,y+1),(x+1,y),(x+1,y+1) */
            int kk;
            uint32_t shift, p;
            int rrho = 0, reqmax = 0, req[4] = {0,0,0,0};
            uint64_t rs[4] = {0,0,0,0}, rmax = 0;
            for (kk = 0; kk < 4; ++kk) {
                int32_t v;
                rng = rng * 1664525u + 1013904223u;
                v = (int32_t)((rng >> 9) & 0x3ffffu); /* HALF coeff range */
                rng = rng * 1664525u + 1013904223u;
                if (rng & 0x10000u) v = -v;
                if ((rng & 0xe0000u) == 0u) v = 0; /* exercise insignificant */
                q[kk] = v;
            }
            shift = 11u; p = 11u; /* kmax=20 (all-HALF) */
            /* scalar reference (mirrors jph_encode_block_prepare_sample32) */
            for (kk = 0; kk < 4; ++kk) {
                int bit = 1 << kk;
                int32_t sv = q[kk];
                uint32_t mag = (uint32_t)(sv < 0 ? -(int64_t)sv : sv);
                uint32_t t, val;
                if ((uint64_t)mag > rmax) rmax = mag;
                t = (sv < 0 ? 0x80000000u : 0u) | (mag << shift);
                val = t + t; val >>= p; val &= ~1u;
                if (val) {
                    int eq = 32 - (val - 1 ? __builtin_clz(val - 1) : 32);
                    rrho |= bit; req[kk] = eq;
                    if (eq > reqmax) reqmax = eq;
                    rs[kk] = (uint64_t)((val - 2) + (t >> 31));
                } else { req[kk] = 0; rs[kk] = 0; }
            }
            /* int32-plane (from32) kernel: plane[y*2+x] = (0,0)=s0,(1,0)=s2,
             * (0,1)=s1,(1,1)=s3. */
            if (caps & EXR_SIMD_SSE2) {
                int32_t pl32[4] = { q[0], q[2], q[1], q[3] };
                int64_t pl64[4] = { q[0], q[2], q[1], q[3] };
                int e0 = 0, em0 = 0, eq0[4] = {0,0,0,0};
                uint64_t s0[4] = {0,0,0,0}, mx0 = 0;
                int e1 = 0, em1 = 0, eq1[4] = {0,0,0,0};
                uint64_t s1[4] = {0,0,0,0}, mx1 = 0;
                jph_encode_prepare_quad_from32_sse2(pl32, 2,0,0,0,0, shift, p,
                                                    &e0, &em0, eq0, s0, &mx0);
                jph_encode_prepare_quad_i32_sse2(pl64, 2,0,0,0,0, shift, p,
                                                 &e1, &em1, eq1, s1, &mx1);
                if (e0 != rrho || em0 != reqmax || mx0 != rmax) qok = 0;
                if (e1 != rrho || em1 != reqmax) qok = 0;
                for (kk = 0; kk < 4; ++kk) {
                    if (eq0[kk] != req[kk] || s0[kk] != rs[kk]) qok = 0;
                    if (eq1[kk] != req[kk] || s1[kk] != rs[kk]) qok = 0;
                }
            }
        }
        CHECK(qok, "JPH HT encode prepare quad SIMD == scalar");
        if (qok) printf("  ok: JPH HT encode prepare quad SIMD == scalar\n");
    }

    /* inverse 5/3 1D wavelet: AVX2 must match scalar (output AND return code,
     * incl. CORRUPT on out-of-int32 reconstruction) over many sizes/magnitudes. */
    if (caps & EXR_SIMD_AVX2) {
        uint32_t rng = 0xABCDEFu;
        int wok = 1;
        size_t trial;
        int32_t *low = (int32_t *)malloc(2048 * sizeof(int32_t));
        int32_t *high = (int32_t *)malloc(2048 * sizeof(int32_t));
        int32_t *o0 = (int32_t *)malloc(4096 * sizeof(int32_t));
        int32_t *o1 = (int32_t *)malloc(4096 * sizeof(int32_t));
        int64_t *ev = (int64_t *)malloc(2048 * sizeof(int64_t));
        int64_t *od = (int64_t *)malloc(2048 * sizeof(int64_t));
        if (low && high && o0 && o1 && ev && od) {
            for (trial = 0; trial < 4000 && wok; ++trial) {
                size_t oc, lc, hc, i;
                exr_result r0, r1;
                int shiftbits;
                rng = rng * 1664525u + 1013904223u;
                oc = (trial < 130) ? trial : (rng % 2000u);
                lc = (oc + 1u) / 2u;
                hc = oc / 2u;
                /* vary magnitude: small (no overflow) ... up to full int32 */
                shiftbits = (int)(trial % 32u);
                for (i = 0; i < lc; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    low[i] = (int32_t)((int32_t)rng >> shiftbits);
                }
                for (i = 0; i < hc; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    high[i] = (int32_t)((int32_t)rng >> shiftbits);
                }
                memset(o0, 0x5a, 4096 * sizeof(int32_t));
                memset(o1, 0x5a, 4096 * sizeof(int32_t));
                r0 = exr_jph_inverse_53_i32(low, lc, high, hc, o0, oc);
                r1 = jph_inverse_53_i32_avx2(low, lc, high, hc, o1, oc, ev, od);
                if (r0 != r1) { wok = 0; break; }
                if (r0 == EXR_SUCCESS &&
                    memcmp(o0, o1, oc * sizeof(int32_t)) != 0) { wok = 0; break; }
            }
            CHECK(wok, "JPH inverse 5/3 1D AVX2 == scalar");
            if (wok) printf("  ok: JPH inverse 5/3 1D AVX2 == scalar\n");
        }
        free(low); free(high); free(o0); free(o1); free(ev); free(od);
    }

    /* vertical (column) inverse 5/3: the row-wise scalar must equal the trusted
     * per-column 1D path, and the AVX2 variant must match the scalar -- output
     * AND return code (incl. CORRUPT on out-of-int32 reconstruction). Covers
     * hh==0 (rh==1), even rh (lh==hh), odd rh (lh==hh+1), non-mult-of-4 rw. */
    {
        const size_t RWMAX = 300u, RHMAX = 64u;
        uint32_t rng = 0x13572468u;
        int vok = 1, has_avx2 = (caps & EXR_SIMD_AVX2) != 0;
        size_t trial;
        int32_t *temp = (int32_t *)malloc(RWMAX * RHMAX * sizeof(int32_t));
        int32_t *ds = (int32_t *)malloc(RWMAX * RHMAX * sizeof(int32_t));
        int32_t *da = (int32_t *)malloc(RWMAX * RHMAX * sizeof(int32_t));
        int32_t *ref = (int32_t *)malloc(RWMAX * RHMAX * sizeof(int32_t));
        int32_t *cl = (int32_t *)malloc(RHMAX * sizeof(int32_t));
        int32_t *ch = (int32_t *)malloc(RHMAX * sizeof(int32_t));
        int32_t *co = (int32_t *)malloc(RHMAX * sizeof(int32_t));
        if (temp && ds && da && ref && cl && ch && co) {
            for (trial = 0; trial < 6000 && vok; ++trial) {
                size_t rw, rh, lh, hh, x, y, i, n;
                int shiftbits, ref_corrupt = 0;
                exr_result rs, ra;
                rng = rng * 1664525u + 1013904223u;
                rw = 1u + (rng % RWMAX);
                rng = rng * 1664525u + 1013904223u;
                rh = 1u + (rng % RHMAX);
                lh = (rh + 1u) / 2u;
                hh = rh / 2u;
                shiftbits = (int)(trial % 32u); /* magnitude: small ... full */
                n = (lh + hh) * rw;
                for (i = 0; i < n; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    temp[i] = (int32_t)((int32_t)rng >> shiftbits);
                }
                /* trusted reference: per-column gather -> 1D scalar -> scatter */
                for (x = 0; x < rw && !ref_corrupt; ++x) {
                    for (y = 0; y < lh; ++y) cl[y] = temp[y * rw + x];
                    for (y = 0; y < hh; ++y) ch[y] = temp[(lh + y) * rw + x];
                    if (exr_jph_inverse_53_i32(cl, lh, ch, hh, co, rh) !=
                        EXR_SUCCESS) { ref_corrupt = 1; break; }
                    for (y = 0; y < rh; ++y) ref[y * rw + x] = co[y];
                }
                memset(ds, 0x5a, RWMAX * RHMAX * sizeof(int32_t));
                memset(da, 0x5a, RWMAX * RHMAX * sizeof(int32_t));
                rs = exr_jph_inverse_53_vert_i32(temp, rw, lh, hh, ds, rw);
                /* scalar-vert return code matches the per-column reference */
                if ((rs == EXR_SUCCESS) == ref_corrupt) { vok = 0; break; }
                if (rs == EXR_SUCCESS) {
                    for (y = 0; y < rh && vok; ++y)
                        if (memcmp(ds + y * rw, ref + y * rw,
                                   rw * sizeof(int32_t)) != 0) vok = 0;
                    if (!vok) break;
                }
                if (has_avx2) {
                    ra = jph_inverse_53_vert_i32_avx2(temp, rw, lh, hh, da, rw);
                    if (ra != rs) { vok = 0; break; }
                    if (ra == EXR_SUCCESS &&
                        memcmp(da, ds, (lh + hh) * rw * sizeof(int32_t)) != 0) {
                        vok = 0; break;
                    }
                }
            }
            CHECK(vok, "JPH inverse 5/3 vertical == per-column (+AVX2)");
            if (vok) printf("  ok: JPH inverse 5/3 vertical == per-column (+AVX2)\n");
        }
        free(temp); free(ds); free(da); free(ref); free(cl); free(ch); free(co);
    }

    /* sign-magnitude codeblock word -> signed int64: AVX2 == scalar over all
     * shifts and the full uint32 range (incl. sign bit and max magnitude). */
    if (caps & EXR_SIMD_AVX2) {
        const size_t en = 1027u;
        uint32_t *src = (uint32_t *)malloc(en * sizeof(uint32_t));
        int64_t *r0 = (int64_t *)malloc(en * sizeof(int64_t));
        int64_t *r1 = (int64_t *)malloc(en * sizeof(int64_t));
        int32_t *r2 = (int32_t *)malloc(en * sizeof(int32_t));
        int32_t *r3 = (int32_t *)malloc(en * sizeof(int32_t));
        int eok = 1;
        uint32_t rng = 0x2468aceu;
        if (src && r0 && r1 && r2 && r3) {
            unsigned shift;
            for (shift = 0u; shift <= 30u && eok; ++shift) {
                size_t i;
                for (i = 0; i < en; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    src[i] = rng; /* full 32-bit incl. sign bit */
                }
                for (i = 0; i < en; ++i) {
                    uint32_t v = src[i];
                    int32_t mag = (int32_t)((v & 0x7fffffffu) >> shift);
                    r0[i] = (v & 0x80000000u) ? -mag : mag;
                    r2[i] = (int32_t)r0[i];
                }
                memset(r1, 0x5a, en * sizeof(int64_t));
                memset(r3, 0x5a, en * sizeof(int32_t));
                jph_extract_signmag_i32_to_i64_avx2(r1, src, en, shift);
                jph_extract_signmag_i32_to_i32_avx2(r3, src, en, shift);
                if (memcmp(r0, r1, en * sizeof(int64_t)) != 0) eok = 0;
                if (memcmp(r2, r3, en * sizeof(int32_t)) != 0) eok = 0;
            }
            CHECK(eok, "JPH sign-mag extract AVX2 == scalar");
            if (eok) printf("  ok: JPH sign-mag extract AVX2 == scalar\n");
        }
        free(src); free(r0); free(r1); free(r2); free(r3);
    }

    /* vertical (column) forward 5/3 (int64, encode): AVX2 must match the scalar
     * source of truth over random sizes incl. hh==0 (rh==1), even/odd rh, and
     * non-mult-of-4 rw. (Codestream-level bit-exactness vs the prior per-column
     * forward is additionally covered by the asakusa HTJ2K round-trip tests.) */
    if (caps & EXR_SIMD_AVX2) {
        const size_t RWMAX = 300u, RHMAX = 64u;
        uint32_t rng = 0x0badf00du;
        int fok = 1;
        size_t trial;
        int64_t *data = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *ts = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *ta = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        if (data && ts && ta) {
            for (trial = 0; trial < 4000 && fok; ++trial) {
                size_t rw, rh, lh, hh, i, n;
                int shiftbits;
                rng = rng * 1664525u + 1013904223u;
                rw = 1u + (rng % RWMAX);
                rng = rng * 1664525u + 1013904223u;
                rh = 1u + (rng % RHMAX);
                lh = (rh + 1u) / 2u;
                hh = rh / 2u;
                shiftbits = (int)(trial % 40u); /* up to ~full int64 range */
                n = rh * rw; /* data uses stride rw here (width == rw) */
                for (i = 0; i < n; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    data[i] = (int64_t)(((uint64_t)rng << 32) | (rng * 2654435761u));
                    data[i] >>= shiftbits;
                }
                memset(ts, 0x5a, RWMAX * RHMAX * sizeof(int64_t));
                memset(ta, 0x5a, RWMAX * RHMAX * sizeof(int64_t));
                jph_forward_53_vert_i64(data, rw, rw, lh, hh, ts);
                jph_forward_53_vert_i64_avx2(data, rw, rw, lh, hh, ta);
                if (memcmp(ts, ta, rh * rw * sizeof(int64_t)) != 0) { fok = 0; break; }
            }
            CHECK(fok, "JPH forward 5/3 vertical AVX2 == scalar");
            if (fok) printf("  ok: JPH forward 5/3 vertical AVX2 == scalar\n");
        }
        free(data); free(ts); free(ta);
    }

    /* int64 inverse 5/3 (float/32-bit decode): AVX2 1D and AVX2 vertical must
     * match their scalar sources of truth, and the row-wise vertical must equal
     * the per-column 1D path. Covers hh==0, even/odd rh, non-mult-of-4 rw. */
    if (caps & EXR_SIMD_AVX2) {
        const size_t RWMAX = 300u, RHMAX = 64u;
        uint32_t rng = 0xfeed1234u;
        int iok = 1, vok = 1;
        size_t trial;
        int64_t *low = (int64_t *)malloc(RWMAX * sizeof(int64_t));
        int64_t *high = (int64_t *)malloc(RWMAX * sizeof(int64_t));
        int64_t *o0 = (int64_t *)malloc(2u * RWMAX * sizeof(int64_t));
        int64_t *o1 = (int64_t *)malloc(2u * RWMAX * sizeof(int64_t));
        int64_t *ev = (int64_t *)malloc(RWMAX * sizeof(int64_t));
        int64_t *od = (int64_t *)malloc(RWMAX * sizeof(int64_t));
        int64_t *temp = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *ds = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *da = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *ref = (int64_t *)malloc(RWMAX * RHMAX * sizeof(int64_t));
        int64_t *cl = (int64_t *)malloc(RHMAX * sizeof(int64_t));
        int64_t *ch = (int64_t *)malloc(RHMAX * sizeof(int64_t));
        int64_t *co = (int64_t *)malloc(RHMAX * sizeof(int64_t));
        if (low && high && o0 && o1 && ev && od && temp && ds && da && ref &&
            cl && ch && co) {
            for (trial = 0; trial < 4000 && (iok && vok); ++trial) {
                size_t rw, rh, lh, hh, x, y, i, oc, lc, hc;
                int shiftbits;
                rng = rng * 1664525u + 1013904223u;
                rw = 1u + (rng % RWMAX);
                rng = rng * 1664525u + 1013904223u;
                rh = 1u + (rng % RHMAX);
                lh = (rh + 1u) / 2u; hh = rh / 2u;
                shiftbits = (int)(trial % 40u);
                /* --- 1D AVX2 == scalar --- */
                oc = rw; lc = (oc + 1u) / 2u; hc = oc / 2u;
                for (i = 0; i < lc; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    low[i] = (int64_t)(((uint64_t)rng << 32) | rng*2654435761u) >> shiftbits;
                }
                for (i = 0; i < hc; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    high[i] = (int64_t)(((uint64_t)rng << 32) | rng*2654435761u) >> shiftbits;
                }
                jph_inverse_53_i64(low, lc, high, hc, o0, oc);
                jph_inverse_53_i64_avx2(low, lc, high, hc, o1, oc, ev, od);
                if (memcmp(o0, o1, oc * sizeof(int64_t)) != 0) { iok = 0; break; }
                /* --- vertical AVX2 == scalar == per-column --- */
                for (i = 0; i < (lh + hh) * rw; ++i) {
                    rng = rng * 1664525u + 1013904223u;
                    temp[i] = (int64_t)(((uint64_t)rng << 32) | rng*2654435761u) >> shiftbits;
                }
                for (x = 0; x < rw; ++x) {
                    for (y = 0; y < lh; ++y) cl[y] = temp[y * rw + x];
                    for (y = 0; y < hh; ++y) ch[y] = temp[(lh + y) * rw + x];
                    jph_inverse_53_i64(cl, lh, ch, hh, co, rh);
                    for (y = 0; y < rh; ++y) ref[y * rw + x] = co[y];
                }
                jph_inverse_53_vert_i64(temp, rw, lh, hh, ds, rw);
                jph_inverse_53_vert_i64_avx2(temp, rw, lh, hh, da, rw);
                if (memcmp(ds, ref, rh * rw * sizeof(int64_t)) != 0) { vok = 0; break; }
                if (memcmp(da, ds, rh * rw * sizeof(int64_t)) != 0) { vok = 0; break; }
            }
            CHECK(iok, "JPH inverse 5/3 1D i64 AVX2 == scalar");
            if (iok) printf("  ok: JPH inverse 5/3 1D i64 AVX2 == scalar\n");
            CHECK(vok, "JPH inverse 5/3 vertical i64 == per-column (+AVX2)");
            if (vok) printf("  ok: JPH inverse 5/3 vertical i64 == per-column (+AVX2)\n");
        }
        free(low); free(high); free(o0); free(o1); free(ev); free(od);
        free(temp); free(ds); free(da); free(ref); free(cl); free(ch); free(co);
    }
#elif defined(EXR_NEON)
    /* NEON JPH kernels vs scalar (compile-time selected on aarch64). */
    {
        const size_t n = 1003; /* not a multiple of 4 -> exercises SIMD tails */
        int64_t *orig = (int64_t *)malloc(n * sizeof(int64_t));
        int64_t *ref = (int64_t *)malloc(n * sizeof(int64_t));
        int64_t *got = (int64_t *)malloc(n * sizeof(int64_t));
        uint32_t rng = 0xC0FFEEu;
        int bds[2] = {16, 32};
        int ok = 1, k;
        if (!orig || !ref || !got) { free(orig); free(ref); free(got); return; }
        for (k = 0; k < 2; ++k) {
            uint32_t bd = (uint32_t)bds[k];
            int64_t bias = ((int64_t)1 << (bd - 1)) + 1;
            size_t i;
            for (i = 0; i < n; ++i) {
                int64_t v;
                rng = rng * 1664525u + 1013904223u;
                v = (int64_t)(int32_t)rng;
                if (bd == 32u && (rng & 7u) == 0u) v *= 41;
                orig[i] = v;
            }
            memcpy(ref, orig, n * sizeof(int64_t));
            jph_nlt_type3_i64_scalar(ref, n, bias);
            memcpy(got, orig, n * sizeof(int64_t));
            jph_nlt_type3_i64_neon(got, n, bias);
            if (memcmp(ref, got, n * sizeof(int64_t)) != 0) ok = 0;
        }
        CHECK(ok, "JPH NLT type3 i64 NEON == scalar");
        if (ok) printf("  ok: JPH NLT type3 i64 NEON == scalar\n");
        free(orig); free(ref); free(got);
    }
    {   /* int32 NLT */
        const size_t n = 1003;
        int32_t *orig = (int32_t *)malloc(n * 4), *ref = (int32_t *)malloc(n * 4);
        int32_t *got = (int32_t *)malloc(n * 4);
        uint32_t rng = 0x5151u;
        int ok = 1;
        if (orig && ref && got) {
            size_t i;
            int32_t biasm1 = (int32_t)((((int64_t)1 << 15) + 1) - 1);
            for (i = 0; i < n; ++i) { rng = rng * 1664525u + 1013904223u;
                orig[i] = (int32_t)(rng & 0x7fffffffu) - 0x40000000; }
            memcpy(ref, orig, n * 4); jph_nlt_type3_i32_scalar(ref, n, biasm1);
            memcpy(got, orig, n * 4); jph_nlt_type3_i32_neon(got, n, biasm1);
            if (memcmp(ref, got, n * 4) != 0) ok = 0;
        }
        CHECK(ok, "JPH NLT type3 i32 NEON == scalar");
        free(orig); free(ref); free(got);
    }
    {   /* int32 -> uint16 pack: truncation, incl. out-of-int16 values. */
        const size_t pn = 1003;
        int32_t *ps = (int32_t *)malloc(pn * 4);
        uint8_t *pr = (uint8_t *)malloc(pn * 2), *px = (uint8_t *)malloc(pn * 2);
        int pok = 1;
        if (ps && pr && px) {
            size_t i; uint32_t r2 = 0x12345u;
            for (i = 0; i < pn; ++i) { r2 = r2 * 1664525u + 1013904223u;
                ps[i] = (int32_t)r2; }
            jph_pack_i32_to_half_scalar(pr, ps, pn);
            jph_pack_i32_to_half_neon(px, ps, pn);
            if (memcmp(pr, px, pn * 2) != 0) pok = 0;
        }
        CHECK(pok, "JPH pack i32->half NEON == scalar");
        free(ps); free(pr); free(px);
    }
    {   /* sign-magnitude extraction over several shifts. */
        const size_t en = 1003;
        uint32_t *src = (uint32_t *)malloc(en * 4);
        int64_t *r0 = (int64_t *)malloc(en * 8), *r1 = (int64_t *)malloc(en * 8);
        int ok = 1; unsigned shifts[3] = {0u, 7u, 30u}; int s;
        if (src && r0 && r1) {
            size_t i; uint32_t rr = 0x9e37u;
            for (i = 0; i < en; ++i) { rr = rr * 1664525u + 1013904223u; src[i] = rr; }
            for (s = 0; s < 3; ++s) {
                size_t x; unsigned shift = shifts[s];
                for (x = 0; x < en; ++x) { uint32_t v = src[x];
                    int32_t mag = (int32_t)((v & 0x7fffffffu) >> shift);
                    r0[x] = (v & 0x80000000u) ? -mag : mag; }
                jph_extract_signmag_i32_to_i64_neon(r1, src, en, shift);
                if (memcmp(r0, r1, en * 8) != 0) ok = 0;
            }
        }
        CHECK(ok, "JPH extract signmag NEON == scalar");
        free(src); free(r0); free(r1);
    }
    {   /* inverse 5/3 1D: i32 (range-checked) and i64, NEON == scalar. */
        int32_t *low = (int32_t *)malloc(2048 * 4), *high = (int32_t *)malloc(2048 * 4);
        int32_t *o0 = (int32_t *)malloc(4096 * 4), *o1 = (int32_t *)malloc(4096 * 4);
        int64_t *L = (int64_t *)malloc(2048 * 8), *H = (int64_t *)malloc(2048 * 8);
        int64_t *q0 = (int64_t *)malloc(4096 * 8), *q1 = (int64_t *)malloc(4096 * 8);
        int64_t *ev = (int64_t *)malloc(2048 * 8), *od = (int64_t *)malloc(2048 * 8);
        uint32_t rng = 0xBEEF01u;
        int wok = 1, w64 = 1, trial;
        if (low && high && o0 && o1 && L && H && q0 && q1 && ev && od) {
            for (trial = 0; trial < 3000 && wok && w64; ++trial) {
                size_t oc, lc, hc, i; exr_result r0, r1; int sb;
                rng = rng * 1664525u + 1013904223u;
                oc = (trial < 100) ? (size_t)trial : (rng % 2000u);
                lc = (oc + 1u) / 2u; hc = oc / 2u; sb = (int)(trial % 32u);
                for (i = 0; i < lc; ++i) { rng = rng * 1664525u + 1013904223u;
                    low[i] = (int32_t)((int32_t)rng >> sb); L[i] = low[i]; }
                for (i = 0; i < hc; ++i) { rng = rng * 1664525u + 1013904223u;
                    high[i] = (int32_t)((int32_t)rng >> sb); H[i] = high[i]; }
                memset(o0, 0x5a, 4096 * 4); memset(o1, 0x5a, 4096 * 4);
                r0 = exr_jph_inverse_53_i32(low, lc, high, hc, o0, oc);
                r1 = jph_inverse_53_i32_neon(low, lc, high, hc, o1, oc, ev, od);
                if (r0 != r1) wok = 0;
                else if (r0 == EXR_SUCCESS && memcmp(o0, o1, oc * 4) != 0) wok = 0;
                jph_inverse_53_i64(L, lc, H, hc, q0, oc);
                jph_inverse_53_i64_neon(L, lc, H, hc, q1, oc, ev, od);
                if (memcmp(q0, q1, oc * 8) != 0) w64 = 0;
            }
        }
        CHECK(wok, "JPH inverse 5/3 1D i32 NEON == scalar");
        CHECK(w64, "JPH inverse 5/3 1D i64 NEON == scalar");
        free(low); free(high); free(o0); free(o1);
        free(L); free(H); free(q0); free(q1); free(ev); free(od);
    }
    {   /* vertical inverse 5/3 (i32 + i64) and forward 5/3 (i64) NEON==scalar. */
        const size_t RWMAX = 130u, RHMAX = 40u, N = 130u * 40u;
        int32_t *t32 = (int32_t *)malloc(N * 4), *ds = (int32_t *)malloc(N * 4);
        int32_t *da = (int32_t *)malloc(N * 4);
        int64_t *t64 = (int64_t *)malloc(N * 8), *vs = (int64_t *)malloc(N * 8);
        int64_t *va = (int64_t *)malloc(N * 8);
        int64_t *fd = (int64_t *)malloc(N * 8), *fs = (int64_t *)malloc(N * 8);
        int64_t *fa = (int64_t *)malloc(N * 8);
        int vi32 = 1, vi64 = 1, ff = 1;
        uint32_t rng = 0x1357abcu;
        size_t trial;
        if (t32 && ds && da && t64 && vs && va && fd && fs && fa) {
            for (trial = 0; trial < 3000 && vi32 && vi64 && ff; ++trial) {
                size_t rw, rh, lh, hh, i, n; int sb; exr_result rs, ra;
                rng = rng * 1664525u + 1013904223u; rw = 1u + (rng % RWMAX);
                rng = rng * 1664525u + 1013904223u; rh = 1u + (rng % RHMAX);
                lh = (rh + 1u) / 2u; hh = rh / 2u; sb = (int)(trial % 32u);
                n = (lh + hh) * rw;
                for (i = 0; i < n; ++i) { rng = rng * 1664525u + 1013904223u;
                    t32[i] = (int32_t)((int32_t)rng >> sb); t64[i] = t32[i]; }
                /* inverse vertical i32 */
                memset(ds, 0x5a, N * 4); memset(da, 0x5a, N * 4);
                rs = exr_jph_inverse_53_vert_i32(t32, rw, lh, hh, ds, rw);
                ra = jph_inverse_53_vert_i32_neon(t32, rw, lh, hh, da, rw);
                if (rs != ra) vi32 = 0;
                else if (rs == EXR_SUCCESS && memcmp(ds, da, n * 4) != 0) vi32 = 0;
                /* inverse vertical i64 */
                memset(vs, 0x5a, N * 8); memset(va, 0x5a, N * 8);
                jph_inverse_53_vert_i64(t64, rw, lh, hh, vs, rw);
                jph_inverse_53_vert_i64_neon(t64, rw, lh, hh, va, rw);
                if (memcmp(vs, va, n * 8) != 0) vi64 = 0;
                /* forward vertical i64 (data interleaved rh rows -> subbands) */
                for (i = 0; i < rh * rw; ++i) { rng = rng * 1664525u + 1013904223u;
                    fd[i] = (int32_t)((int32_t)rng >> sb); }
                jph_forward_53_vert_i64(fd, rw, rw, lh, hh, fs);
                jph_forward_53_vert_i64_neon(fd, rw, rw, lh, hh, fa);
                if (memcmp(fs, fa, n * 8) != 0) ff = 0;
            }
        }
        CHECK(vi32, "JPH inverse 5/3 vertical i32 NEON == scalar");
        CHECK(vi64, "JPH inverse 5/3 vertical i64 NEON == scalar");
        CHECK(ff, "JPH forward 5/3 vertical i64 NEON == scalar");
        free(t32); free(ds); free(da); free(t64); free(vs); free(va);
        free(fd); free(fs); free(fa);
    }
    {   /* forward 5/3 1D i64 NEON: round-trips losslessly through the (already
         * scalar-verified) inverse 1D i64 NEON kernel -> reconstructs the input.
         * (The scalar forward 1D is static; the forward arithmetic is also
         * directly checked scalar-vs-NEON by the vertical test above.) */
        int64_t *src = (int64_t *)malloc(4096 * 8), *rec = (int64_t *)malloc(4096 * 8);
        int64_t *lo = (int64_t *)malloc(2048 * 8), *hi = (int64_t *)malloc(2048 * 8);
        int64_t *ev = (int64_t *)malloc(2048 * 8), *od = (int64_t *)malloc(2048 * 8);
        uint32_t rng = 0x9a7f3u;
        int fok = 1, trial;
        if (src && rec && lo && hi && ev && od) {
            for (trial = 0; trial < 3000 && fok; ++trial) {
                size_t n, nl, nh, i; int sb;
                rng = rng * 1664525u + 1013904223u;
                n = (trial < 100) ? (size_t)trial : (rng % 4000u);
                nl = (n + 1u) / 2u; nh = n / 2u; sb = (int)(trial % 16u);
                for (i = 0; i < n; ++i) { rng = rng * 1664525u + 1013904223u;
                    src[i] = (int32_t)((int32_t)rng >> sb); }
                jph_forward_53_i64_neon(src, n, lo, nl, hi, nh, ev, od);
                jph_inverse_53_i64_neon(lo, nl, hi, nh, rec, n, ev, od);
                if (n && memcmp(src, rec, n * 8) != 0) fok = 0;
            }
        }
        CHECK(fok, "JPH forward 5/3 1D i64 NEON round-trips (fwd->inv)");
        free(src); free(rec); free(lo); free(hi); free(ev); free(od);
    }
#endif
}

#if defined(EXR_USE_THREADS)
/* Multithreading: encode must be byte-deterministic and decode bit-identical
 * regardless of thread count. Exercises scanline (all codecs) + single-level
 * tiled, on the in-memory load/save paths the parallel code targets. */
static void thread_save(exr_image *img, exr_compression comp, int nthreads,
                        void **buf, size_t *sz) {
    exr_set_num_threads(nthreads);
    *buf = NULL;
    *sz = 0;
    (void)exr_save_to_memory(buf, sz, NULL, img, comp);
}

static void thread_tests(const char *path) {
    static const exr_compression codecs[] = {
        EXR_COMPRESSION_NONE, EXR_COMPRESSION_RLE, EXR_COMPRESSION_ZIPS,
        EXR_COMPRESSION_ZIP,  EXR_COMPRESSION_PIZ, EXR_COMPRESSION_PXR24,
        EXR_COMPRESSION_B44};
    static const char *names[] = {"none", "rle", "zips", "zip",
                                  "piz",  "pxr24", "b44"};
    exr_image src;
    size_t i;

    memset(&src, 0, sizeof(src));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src))) {
        g_fail++;
        printf("  FAIL: %s load (threads)\n", path);
        return;
    }

    for (i = 0; i < sizeof(codecs) / sizeof(codecs[0]); ++i) {
        void *a = NULL, *b = NULL;
        size_t na = 0, nb = 0;
        exr_image d1, d4;
        thread_save(&src, codecs[i], 1, &a, &na);
        thread_save(&src, codecs[i], 4, &b, &nb);
        CHECK(a && b && na == nb && memcmp(a, b, na) == 0, names[i]);
        /* decode the (serial-encoded) bytes serially and with 4 workers */
        memset(&d1, 0, sizeof(d1));
        memset(&d4, 0, sizeof(d4));
        exr_set_num_threads(1);
        (void)exr_load_from_memory(a, na, NULL, &d1);
        exr_set_num_threads(4);
        (void)exr_load_from_memory(a, na, NULL, &d4);
        CHECK(images_equal(&d1, &d4), names[i]);
        printf("  ok: scanline %s  enc-deterministic + decode parity\n",
               names[i]);
        exr_image_free(&d1);
        exr_image_free(&d4);
        free(a);
        free(b);
    }

    /* single-level tiled (77 tiles for 660x440 @ 64) */
    src.parts[0].header.tiled = 1;
    src.parts[0].header.part_type = EXR_PART_TILED;
    src.parts[0].header.tile_x_size = 64;
    src.parts[0].header.tile_y_size = 64;
    src.parts[0].header.level_mode = EXR_TILE_ONE_LEVEL;
    src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    {
        void *a = NULL, *b = NULL;
        size_t na = 0, nb = 0;
        exr_image t1, t4;
        thread_save(&src, EXR_COMPRESSION_ZIP, 1, &a, &na);
        thread_save(&src, EXR_COMPRESSION_ZIP, 4, &b, &nb);
        CHECK(a && b && na == nb && memcmp(a, b, na) == 0, "tiled zip enc");
        memset(&t1, 0, sizeof(t1));
        memset(&t4, 0, sizeof(t4));
        exr_set_num_threads(1);
        (void)exr_load_from_memory(a, na, NULL, &t1);
        exr_set_num_threads(4);
        (void)exr_load_from_memory(a, na, NULL, &t4);
        CHECK(images_equal(&t1, &t4), "tiled zip decode parity");
        printf("  ok: tiled zip  enc-deterministic + decode parity\n");
        exr_image_free(&t1);
        exr_image_free(&t4);
        free(a);
        free(b);
    }

    /* mipmap + ripmap level generation: the parallel downsample must be
     * bit-deterministic, so a 1-thread and a 4-thread save produce identical
     * bytes (asakusa's level 1+ rows clear the dh>=64 parallel threshold). */
    {
        int modes[2] = {EXR_TILE_MIPMAP_LEVELS, EXR_TILE_RIPMAP_LEVELS};
        const char *mn[2] = {"mipmap", "ripmap"};
        int m;
        for (m = 0; m < 2; ++m) {
            void *a = NULL, *b = NULL;
            size_t na = 0, nb = 0;
            src.parts[0].header.level_mode = modes[m];
            thread_save(&src, EXR_COMPRESSION_ZIP, 1, &a, &na);
            thread_save(&src, EXR_COMPRESSION_ZIP, 4, &b, &nb);
            CHECK(a && b && na == nb && na > 0 && memcmp(a, b, na) == 0, mn[m]);
            printf("  ok: %s level gen  enc-deterministic (parallel downsample)\n",
                   mn[m]);
            free(a);
            free(b);
        }
    }

    exr_set_num_threads(1);
    exr_image_free(&src);
}

/* Deep encode: the parallel per-block compress must be byte-deterministic, so a
 * 1-thread and a 4-thread save produce identical bytes, for both the scanline
 * (emit_deep_scanlines) and tiled (emit_deep_tile_level) writers. */
static void deep_encode_thread_check(const char *path) {
    exr_image src;
    void *a1 = NULL, *a4 = NULL;
    size_t n1 = 0, n4 = 0;
    int pass = 1;
    memset(&src, 0, sizeof(src));
    if (!EXR_OK(exr_load_from_file(path, NULL, &src)) || !src.parts[0].is_deep) {
        printf("  skip: %s (deep encode threads)\n", path);
        exr_image_free(&src);
        return;
    }
    exr_set_num_threads(1);
    (void)exr_save_to_memory(&a1, &n1, NULL, &src, EXR_COMPRESSION_ZIPS);
    exr_set_num_threads(4);
    (void)exr_save_to_memory(&a4, &n4, NULL, &src, EXR_COMPRESSION_ZIPS);
    pass = a1 && a4 && n1 == n4 && n1 > 0 && memcmp(a1, a4, n1) == 0;
    CHECK(pass, "deep scanline encode deterministic (1 vs 4 threads)");
    free(a1); free(a4); a1 = a4 = NULL; n1 = n4 = 0;

    /* deep tiled (one level, 32x32 tiles) */
    src.parts[0].header.tiled = 1;
    src.parts[0].header.part_type = EXR_PART_DEEP_TILED;
    src.parts[0].header.tile_x_size = 32;
    src.parts[0].header.tile_y_size = 32;
    src.parts[0].header.level_mode = EXR_TILE_ONE_LEVEL;
    src.parts[0].header.rounding_mode = EXR_TILE_ROUND_DOWN;
    exr_set_num_threads(1);
    (void)exr_save_to_memory(&a1, &n1, NULL, &src, EXR_COMPRESSION_ZIPS);
    exr_set_num_threads(4);
    (void)exr_save_to_memory(&a4, &n4, NULL, &src, EXR_COMPRESSION_ZIPS);
    pass = a1 && a4 && n1 == n4 && n1 > 0 && memcmp(a1, a4, n1) == 0;
    CHECK(pass, "deep tiled encode deterministic (1 vs 4 threads)");
    if (pass)
        printf("  ok: deep encode 1-vs-4 deterministic (scanline + tiled)\n");
    free(a1); free(a4);
    exr_set_num_threads(1);
    exr_image_free(&src);
}
#endif /* EXR_USE_THREADS */

/* Spectral: channel-name helpers, emissive cube round-trip, custom-attribute
 * round-trip through the writer. */
static void spectral_tests(void) {
    char nm[64];
    float wl;

    /* name format + parse (comma decimal, 6 fractional digits) */
    exr_spectral_channel_name(nm, sizeof(nm), EXR_SPECTRUM_EMISSIVE, 0, 550.0f);
    CHECK(strcmp(nm, "S0.550,000000nm") == 0, "spectral emissive name format");
    exr_spectral_channel_name(nm, sizeof(nm), EXR_SPECTRUM_REFLECTIVE, 0, 700.0f);
    CHECK(strcmp(nm, "T.700,000000nm") == 0, "spectral reflective name format");
    wl = exr_spectral_channel_wavelength("S0.550,000000nm");
    CHECK(wl > 549.9f && wl < 550.1f, "spectral wavelength parse");
    CHECK(exr_spectral_channel_stokes("S2.480,000000nm") == 2, "stokes parse");
    CHECK(exr_spectral_channel_stokes("T.480,000000nm") == -1, "reflective stokes -1");
    CHECK(exr_is_spectral_channel("S0.480,000000nm") == 1, "is-spectral-channel");
    CHECK(exr_is_spectral_channel("R") == 0, "non-spectral channel");

    /* build a 3x2 emissive image with 4 wavelengths, save, reload, compare */
    {
        const int W = 3, H = 2, NWL = 4;
        float wls[4] = {480.0f, 550.0f, 620.0f, 700.0f};
        float *samples = (float *)malloc((size_t)NWL * W * H * sizeof(float));
        exr_image img;
        void *blob = NULL;
        size_t blob_size = 0;
        exr_spectral_image spec;
        int k, p, ok = 1;

        for (k = 0; k < NWL; ++k)
            for (p = 0; p < W * H; ++p)
                samples[(size_t)k * W * H + p] = (float)(k * 100 + p) * 0.5f;

        memset(&img, 0, sizeof(img));
        CHECK(EXR_OK(exr_spectral_setup_emissive(NULL, W, H, NWL, wls, samples,
                                                 "W.m^-2.sr^-1", &img)),
              "spectral setup emissive");
        CHECK(EXR_OK(exr_save_to_memory(&blob, &blob_size, NULL, &img,
                                        EXR_COMPRESSION_ZIP)),
              "spectral save to memory");
        exr_image_free(&img);

        memset(&spec, 0, sizeof(spec));
        CHECK(EXR_OK(exr_spectral_load_from_memory(blob, blob_size, NULL, &spec)),
              "spectral load from memory");
        CHECK(spec.type == EXR_SPECTRUM_EMISSIVE, "reloaded spectrum type emissive");
        CHECK(spec.num_wavelengths == NWL && spec.width == W && spec.height == H,
              "reloaded spectral dimensions");
        CHECK(strcmp(spec.units, "W.m^-2.sr^-1") == 0, "reloaded spectral units");
        for (k = 0; k < spec.num_wavelengths; ++k)
            if (spec.wavelengths[k] < wls[k] - 0.5f ||
                spec.wavelengths[k] > wls[k] + 0.5f)
                ok = 0;
        CHECK(ok, "reloaded wavelengths sorted + correct");
        ok = 1;
        for (k = 0; k < NWL; ++k)
            for (p = 0; p < W * H; ++p) {
                float got = exr_spectral_sample(&spec, 0, k, p % W, p / W);
                float want = (float)(k * 100 + p) * 0.5f;
                if (got < want - 0.01f || got > want + 0.01f) ok = 0;
            }
        CHECK(ok, "reloaded spectral samples match");
        {
            float ps[4];
            int n = exr_spectral_pixel(&spec, 0, 1, 0, ps); /* pixel index p=1 */
            CHECK(n == NWL && ps[0] == 0.5f && ps[1] == 50.5f,
                  "per-pixel spectrum extract");
        }
        exr_spectral_image_free(&spec);
        free(samples);
        free(blob);
    }

    /* Subsampled spectral channel: make the 550nm plane 2x2-subsampled, save,
     * reload, and confirm it point-expands to full resolution. */
    {
        const int W = 4, H = 4, NWL = 4;
        float wls[4] = {480.0f, 550.0f, 620.0f, 700.0f};
        float *samples = (float *)malloc((size_t)NWL * W * H * sizeof(float));
        exr_image img;
        void *blob = NULL;
        size_t blob_size = 0;
        exr_spectral_image spec;
        float grid[4]; /* 2x2 subsampled plane for the 550nm channel */
        int x, y, ok = 1;
        size_t i;

        for (i = 0; i < (size_t)NWL * W * H; ++i) samples[i] = (float)i;
        memset(&img, 0, sizeof(img));
        if (EXR_OK(exr_spectral_setup_emissive(NULL, W, H, NWL, wls, samples,
                                               "W.m^-2.sr^-1", &img))) {
            /* channel 1 == 550nm: replace its full plane with a 2x2 grid. */
            grid[0] = 10.0f; grid[1] = 20.0f; grid[2] = 30.0f; grid[3] = 40.0f;
            free(img.parts[0].images[1]);
            img.parts[0].images[1] = malloc(sizeof(grid));
            memcpy(img.parts[0].images[1], grid, sizeof(grid));
            img.parts[0].header.channels[1].x_sampling = 2;
            img.parts[0].header.channels[1].y_sampling = 2;

            CHECK(EXR_OK(exr_save_to_memory(&blob, &blob_size, NULL, &img,
                                            EXR_COMPRESSION_ZIP)),
                  "subsampled spectral save");
            exr_image_free(&img);

            memset(&spec, 0, sizeof(spec));
            CHECK(EXR_OK(exr_spectral_load_from_memory(blob, blob_size, NULL,
                                                       &spec)),
                  "subsampled spectral load (no longer rejected)");
            for (y = 0; y < H; ++y)
                for (x = 0; x < W; ++x) {
                    float got = exr_spectral_sample(&spec, 0, 1, x, y);
                    float want = grid[(y / 2) * 2 + (x / 2)];
                    if (got < want - 0.01f || got > want + 0.01f) ok = 0;
                }
            CHECK(ok, "subsampled 550nm plane point-expanded to full res");
            exr_spectral_image_free(&spec);
            free(blob);
        } else {
            CHECK(0, "subsampled spectral setup");
            exr_image_free(&img);
        }
        free(samples);
    }
}

/* ============================================================================
 * Util module: conversions, resize, tonemap, colorspace, transfer, LUT
 * ========================================================================== */

static int approx(float a, float b, float eps) {
    float d = a - b;
    if (d < 0) d = -d;
    return d <= eps;
}

static void util_convert_tests(void) {
    int i;
    uint16_t u16[256], r16[256];
    float f[256];
    /* u16 normalized round-trip (exact: 65535 is representable). */
    for (i = 0; i < 256; ++i) u16[i] = (uint16_t)(i * 257); /* 0..65535 */
    exr_u16_to_float(u16, f, 256, 1);
    exr_float_to_u16(f, r16, 256, 1);
    {
        int ok = 1;
        for (i = 0; i < 256; ++i)
            if (u16[i] != r16[i]) ok = 0;
        CHECK(ok, "u16<->float normalized round-trip exact");
    }
    CHECK(approx(f[0], 0.0f, 0.0f) && approx(f[255], 1.0f, 1e-6f),
          "u16 normalized endpoints");

    /* clamp + round: HDR/negative inputs. */
    {
        float in[4] = {-1.0f, 0.4f / 65535.0f, 2.0f, 0.50001f / 65535.0f};
        uint16_t o[4];
        exr_float_to_u16(in, o, 4, 1);
        CHECK(o[0] == 0 && o[2] == 65535, "float->u16 clamps out-of-range");
        CHECK(o[1] == 0 && o[3] == 1, "float->u16 round-to-nearest");
    }
    /* convert_pixels: HALF<->FLOAT matches the dedicated kernels. */
    {
        uint16_t h[64];
        float a[64], b[64];
        for (i = 0; i < 64; ++i) a[i] = (float)i * 0.123f - 3.0f;
        exr_float_to_half(a, h, 64);
        exr_convert_pixels(b, EXR_PIXEL_FLOAT, h, EXR_PIXEL_HALF, 64,
                           EXR_CONVERT_RAW);
        {
            float ref[64];
            int ok = 1;
            exr_half_to_float(h, ref, 64);
            for (i = 0; i < 64; ++i)
                if (b[i] != ref[i]) ok = 0;
            CHECK(ok, "convert_pixels HALF->FLOAT matches kernel");
        }
    }
    /* uint32 normalized round-trip via convert_pixels. */
    {
        uint32_t u[5] = {0u, 1u, 2147483648u, 4294967294u, 4294967295u}, ru[5];
        float fv[5];
        exr_convert_pixels(fv, EXR_PIXEL_FLOAT, u, EXR_PIXEL_UINT, 5,
                           EXR_CONVERT_NORMALIZED);
        exr_convert_pixels(ru, EXR_PIXEL_UINT, fv, EXR_PIXEL_FLOAT, 5,
                           EXR_CONVERT_NORMALIZED);
        CHECK(ru[0] == 0u && ru[4] == 4294967295u, "u32 normalized endpoints");
        CHECK(approx(fv[4], 1.0f, 1e-6f), "u32 normalized 1.0");
    }
}

static void util_simd_parity_tests(void) {
    int i, n = 1000;
    static uint16_t u16[1000];
    static uint8_t u8[1000];
    static float fin[1000], a_s[1000], a_v[1000], b_s[1000], b_v[1000];
    static uint16_t q_s[1000], q_v[1000];
    static uint8_t c_s[1000], c_v[1000];
    srand(12345);
    for (i = 0; i < n; ++i) {
        u16[i] = (uint16_t)(rand() & 0xffff);
        u8[i] = (uint8_t)(rand() & 0xff);
        /* mix of normal, HDR, negative, and non-finite-ish values */
        switch (i % 5) {
            case 0: fin[i] = (float)(rand() % 200000) / 65535.0f; break;
            case 1: fin[i] = -(float)(rand() % 100) / 65535.0f; break;
            case 2: fin[i] = 1.5f; break;
            default: fin[i] = (float)(rand() % 70000) / 65535.0f; break;
        }
    }
    /* scalar tier */
    exr_simd_force(0);
    exr_u16_to_float(u16, a_s, n, 1);
    exr_u8_to_float(u8, b_s, n, 1);
    exr_float_to_u16(fin, q_s, n, 1);
    exr_float_to_u8(fin, c_s, n, 1);
    /* best tier */
    exr_simd_force(2);
    exr_u16_to_float(u16, a_v, n, 1);
    exr_u8_to_float(u8, b_v, n, 1);
    exr_float_to_u16(fin, q_v, n, 1);
    exr_float_to_u8(fin, c_v, n, 1);
    {
        int ok = 1;
        for (i = 0; i < n; ++i) {
            if (!approx(a_s[i], a_v[i], 1e-6f)) ok = 0;
            if (!approx(b_s[i], b_v[i], 1e-6f)) ok = 0;
            if (q_s[i] != q_v[i]) ok = 0;
            if (c_s[i] != c_v[i]) ok = 0;
        }
        CHECK(ok, "SIMD convert kernels match scalar (incl. clamp/round)");
    }
    /* axpy + mat3 parity */
    {
        static float acc_s[1000], acc_v[1000], x[1000];
        float m[9] = {0.6f, 0.3f, 0.1f, 0.2f, 0.7f, 0.1f, 0.1f, 0.2f, 0.7f};
        int ok = 1;
        for (i = 0; i < n; ++i) { x[i] = fin[i]; acc_s[i] = acc_v[i] = 0.25f; }
        exr_simd_force(0);
        exr_simd.axpy(acc_s, x, 0.5f, n);
        exr_simd_force(2);
        exr_simd.axpy(acc_v, x, 0.5f, n);
        for (i = 0; i < n; ++i)
            if (!approx(acc_s[i], acc_v[i], 1e-5f)) ok = 0;
        CHECK(ok, "SIMD axpy matches scalar");
        {
            static float ms[1000], mv[1000];
            int px = n / 4;
            exr_simd_force(0);
            exr_simd.mat3(ms, x, (size_t)px, 4, m);
            exr_simd_force(2);
            exr_simd.mat3(mv, x, (size_t)px, 4, m);
            ok = 1;
            for (i = 0; i < px * 4; ++i)
                if (!approx(ms[i], mv[i], 1e-5f)) ok = 0;
            CHECK(ok, "SIMD mat3 matches scalar");
        }
    }
    /* half<->float SIMD parity vs scalar. The hardware-convert tiers (x86 F16C,
     * ARM NEON FCVTL/FCVTN) are bit-exact with the integer scalar for every
     * finite / zero / inf / subnormal value; like F16C they quiet signalling
     * NaNs, so NaN inputs need only stay NaN (not bit-identical). float->half is
     * fully bit-exact, NaN payloads included. */
    {
        static uint16_t hin[65536];
        static float hf_s[65536], hf_v[65536];
        int q, hok = 1;
        for (q = 0; q < 65536; ++q) hin[q] = (uint16_t)q;
        exr_simd_force(0);
        exr_half_to_float(hin, hf_s, 65536);
        exr_simd_force(2);
        exr_half_to_float(hin, hf_v, 65536);
        for (q = 0; q < 65536; ++q) {
            if (((q & 0x7c00) == 0x7c00) && (q & 0x3ff)) {
                if (!(hf_v[q] != hf_v[q])) hok = 0; /* NaN must stay NaN */
            } else {
                uint32_t a, b;
                memcpy(&a, &hf_s[q], 4);
                memcpy(&b, &hf_v[q], 4);
                if (a != b) hok = 0;
            }
        }
        CHECK(hok, "SIMD half->float matches scalar (NaN stays NaN)");
        {
            static uint16_t qs[65536], qv[65536];
            static float fv[65536];
            uint32_t rng = 0x1234567u;
            int j;
            hok = 1;
            for (q = 0; q < 65536; ++q) fv[q] = hf_s[q]; /* every half's float */
            exr_simd_force(0); exr_float_to_half(fv, qs, 65536);
            exr_simd_force(2); exr_float_to_half(fv, qv, 65536);
            for (q = 0; q < 65536; ++q) if (qs[q] != qv[q]) hok = 0;
            for (j = 0; j < 4 && hok; ++j) { /* + raw float bit patterns */
                for (q = 0; q < 65536; ++q) {
                    rng = rng * 1664525u + 1013904223u;
                    memcpy(&fv[q], &rng, 4);
                }
                exr_simd_force(0); exr_float_to_half(fv, qs, 65536);
                exr_simd_force(2); exr_float_to_half(fv, qv, 65536);
                for (q = 0; q < 65536; ++q) if (qs[q] != qv[q]) hok = 0;
            }
            CHECK(hok, "SIMD float->half bit-exact with scalar");
        }
    }
    exr_simd_force(2);
}

static void util_resize_tests(void) {
    const exr_allocator *a = NULL;
    int w = 8, h = 6, i;
    float src[8 * 6]; /* 1 channel */
    /* identity resize reproduces input (triangle). */
    for (i = 0; i < w * h; ++i) src[i] = (float)i;
    {
        float dst[8 * 6];
        exr_result rc = exr_resize_float(a, src, w, h, 0, dst, w, h, 0, 1,
                                         EXR_RESIZE_TRIANGLE, EXR_EDGE_CLAMP, -1);
        int ok = EXR_OK(rc);
        for (i = 0; i < w * h; ++i)
            if (!approx(dst[i], src[i], 1e-4f)) ok = 0;
        CHECK(ok, "resize identity (triangle) reproduces input");
    }
    /* 2x box downscale == exact 2x2 block average. */
    {
        float dst[4 * 3];
        int x, y, ok;
        exr_result rc = exr_resize_float(a, src, w, h, 0, dst, 4, 3, 0, 1,
                                         EXR_RESIZE_BOX, EXR_EDGE_CLAMP, -1);
        ok = EXR_OK(rc);
        for (y = 0; y < 3; ++y)
            for (x = 0; x < 4; ++x) {
                float avg = (src[(2 * y) * w + 2 * x] +
                             src[(2 * y) * w + 2 * x + 1] +
                             src[(2 * y + 1) * w + 2 * x] +
                             src[(2 * y + 1) * w + 2 * x + 1]) /
                            4.0f;
                if (!approx(dst[y * 4 + x], avg, 1e-4f)) ok = 0;
            }
        CHECK(ok, "2x box downscale == 2x2 average");
    }
    /* streaming resizer == whole-image (parity). */
    {
        int sw = 17, sh = 13, dw = 9, dh = 7, c = 3, n = sw * sh * 3;
        float *si = (float *)malloc((size_t)n * sizeof(float));
        float *whole = (float *)malloc((size_t)dw * dh * c * sizeof(float));
        float *strm = (float *)malloc((size_t)dw * dh * c * sizeof(float));
        exr_resizer *rz = NULL;
        int sy = 0, ok = 1, k;
        for (k = 0; k < n; ++k) si[k] = (float)((k * 7) % 101) * 0.03f;
        exr_resize_float(a, si, sw, sh, 0, whole, dw, dh, 0, c,
                         EXR_RESIZE_MITCHELL, EXR_EDGE_CLAMP, -1);
        exr_resizer_create(a, sw, sh, dw, dh, c, EXR_PIXEL_FLOAT,
                           EXR_RESIZE_MITCHELL, EXR_EDGE_CLAMP, &rz);
        for (;;) {
            int dy;
            float rowbuf[9 * 3];
            exr_result rc = exr_resizer_pull_row(rz, &dy, rowbuf);
            if (rc == EXR_WOULD_BLOCK) {
                exr_resizer_push_row(rz, sy, si + (size_t)sy * sw * c);
                sy++;
                continue;
            }
            if (dy >= dh) break;
            memcpy(strm + (size_t)dy * dw * c, rowbuf,
                   (size_t)dw * c * sizeof(float));
        }
        for (k = 0; k < dw * dh * c; ++k)
            if (!approx(whole[k], strm[k], 1e-5f)) ok = 0;
        CHECK(ok, "streaming resizer == whole-image resize");
        exr_resizer_destroy(rz);
        free(si); free(whole); free(strm);
    }
}

static void util_tonemap_tests(void) {
    float in[12], out[12];
    int i;
    for (i = 0; i < 4; ++i) {
        in[i * 3 + 0] = (float)i;       /* increasing */
        in[i * 3 + 1] = (float)i * 2.0f;
        in[i * 3 + 2] = (float)i * 0.5f;
    }
    exr_tonemap_float(out, in, 4, 3, EXR_TONEMAP_ACES, NULL);
    CHECK(approx(out[0], 0.0f, 1e-6f), "ACES maps 0 to 0");
    CHECK(out[3] <= out[6] + 1e-6f && out[6] <= out[9] + 1e-6f,
          "ACES monotonic in input");
    CHECK(out[9] <= 1.0f + 1e-6f, "ACES saturates <= 1");
    /* in-place == out-of-place (Reinhard). */
    {
        float a[12], b[12];
        memcpy(a, in, sizeof(in));
        memcpy(b, in, sizeof(in));
        exr_tonemap_float(a, a, 4, 3, EXR_TONEMAP_REINHARD, NULL);
        exr_tonemap_float(out, b, 4, 3, EXR_TONEMAP_REINHARD, NULL);
        {
            int ok = 1;
            for (i = 0; i < 12; ++i)
                if (a[i] != out[i]) ok = 0;
            CHECK(ok, "tonemap in-place == out-of-place");
        }
    }
}

static void util_color_tests(void) {
    float m1[9], m2[9], comp[9];
    int i, j;
    /* round-trip: M(to,from) * M(from,to) ~ I */
    exr_color_matrix(EXR_CS_SRGB, EXR_CS_REC2020, m1);
    exr_color_matrix(EXR_CS_REC2020, EXR_CS_SRGB, m2);
    for (i = 0; i < 3; ++i)
        for (j = 0; j < 3; ++j) {
            float s = 0.0f;
            int k;
            for (k = 0; k < 3; ++k) s += m2[i * 3 + k] * m1[k * 3 + j];
            comp[i * 3 + j] = s;
        }
    {
        int ok = 1;
        for (i = 0; i < 3; ++i)
            for (j = 0; j < 3; ++j)
                if (!approx(comp[i * 3 + j], i == j ? 1.0f : 0.0f, 1e-4f))
                    ok = 0;
        CHECK(ok, "colorspace matrix round-trip ~ identity");
    }
    /* sRGB white -> XYZ ~ D65 white (apply matrix). */
    {
        float white[3] = {1.0f, 1.0f, 1.0f}, xyz[3];
        exr_color_matrix(EXR_CS_SRGB, EXR_CS_XYZ, m1);
        exr_color_apply_matrix(xyz, white, 1, 3, m1);
        CHECK(approx(xyz[0], 0.95047f, 1e-3f) && approx(xyz[1], 1.0f, 1e-3f) &&
                  approx(xyz[2], 1.08883f, 1e-3f),
              "sRGB(1,1,1) -> XYZ D65");
    }
}

static void util_transfer_tests(void) {
    int i;
    float v[64], lin[64], back[64];
    exr_transfer tfs[5] = {EXR_TF_SRGB, EXR_TF_GAMMA_22, EXR_TF_REC709,
                           EXR_TF_PQ, EXR_TF_HLG};
    int t;
    for (i = 0; i < 64; ++i) v[i] = (float)i / 63.0f;
    for (t = 0; t < 5; ++t) {
        int ok = 1;
        exr_encode_transfer(lin, v, 64, tfs[t]); /* code from "linear" v */
        exr_decode_transfer(back, lin, 64, tfs[t]);
        for (i = 0; i < 64; ++i)
            if (!approx(back[i], v[i], 2e-3f)) ok = 0;
        CHECK(ok, "transfer EOTF(OETF(x)) ~ x");
    }
    /* hand-rolled transcendentals vs libm. */
    {
        int ok = 1;
        for (i = 1; i < 200; ++i) {
            float x = (float)i * 0.05f;
            if (!approx(exr_util_log2f(x), log2f(x), 3e-5f * (1.0f + x))) ok = 0;
            if (!approx(exr_util_exp2f((float)i * 0.03f - 3.0f),
                        exp2f((float)i * 0.03f - 3.0f),
                        1e-5f * exp2f((float)i * 0.03f - 3.0f)))
                ok = 0;
            if (!approx(exr_util_powf(x, 1.0f / 2.4f), powf(x, 1.0f / 2.4f),
                        2e-5f * (1.0f + x)))
                ok = 0;
        }
        CHECK(ok, "hand-rolled log2/exp2/pow match libm (~1e-5)");
    }
}

static void util_lut_tests(void) {
    int N = 2, ir, ig, ib, ok;
    float data[2 * 2 * 2 * 3];
    exr_lut3d lut;
    float in[12], out[12];
    int i;
    /* identity LUT on [0,1]: sample(ir,ig,ib) = (ir,ig,ib)/(N-1). */
    for (ib = 0; ib < N; ++ib)
        for (ig = 0; ig < N; ++ig)
            for (ir = 0; ir < N; ++ir) {
                size_t idx = (((size_t)ib * N + ig) * N + ir) * 3;
                data[idx + 0] = (float)ir / (N - 1);
                data[idx + 1] = (float)ig / (N - 1);
                data[idx + 2] = (float)ib / (N - 1);
            }
    lut.size = N;
    lut.data = data;
    lut.domain_min[0] = lut.domain_min[1] = lut.domain_min[2] = 0.0f;
    lut.domain_max[0] = lut.domain_max[1] = lut.domain_max[2] = 1.0f;
    for (i = 0; i < 4; ++i) {
        in[i * 3 + 0] = 0.1f + 0.2f * i;
        in[i * 3 + 1] = 0.3f;
        in[i * 3 + 2] = 0.8f - 0.1f * i;
    }
    exr_lut3d_apply(out, in, 4, 3, &lut, EXR_LUT_TRILINEAR);
    ok = 1;
    for (i = 0; i < 12; ++i)
        if (!approx(out[i], in[i], 1e-5f)) ok = 0;
    CHECK(ok, "identity LUT (trilinear) reproduces input");
    exr_lut3d_apply(out, in, 4, 3, &lut, EXR_LUT_TETRAHEDRAL);
    ok = 1;
    for (i = 0; i < 12; ++i)
        if (!approx(out[i], in[i], 1e-5f)) ok = 0;
    CHECK(ok, "identity LUT (tetrahedral) reproduces input");
    /* parse a tiny .cube and apply identity. */
    {
        const char *cube =
            "# comment\nTITLE \"id\"\nLUT_3D_SIZE 2\n"
            "DOMAIN_MIN 0 0 0\nDOMAIN_MAX 1 1 1\n"
            "0 0 0\n1 0 0\n0 1 0\n1 1 0\n"
            "0 0 1\n1 0 1\n0 1 1\n1 1 1\n";
        exr_lut3d pl;
        float *owned = NULL;
        exr_result rc =
            exr_lut3d_parse_cube(NULL, cube, strlen(cube), &pl, &owned);
        CHECK(EXR_OK(rc) && pl.size == 2 && owned != NULL, ".cube parse ok");
        if (EXR_OK(rc)) {
            exr_lut3d_apply(out, in, 4, 3, &pl, EXR_LUT_TRILINEAR);
            ok = 1;
            for (i = 0; i < 12; ++i)
                if (!approx(out[i], in[i], 1e-5f)) ok = 0;
            CHECK(ok, "parsed .cube identity reproduces input");
            free(owned);
        }
    }
}

static void util_tests(void) {
    exr_simd_init(); /* ensure dispatch is initialized so force() sticks */
    printf("== util: conversions ==\n");
    util_convert_tests();
    printf("== util: SIMD parity ==\n");
    util_simd_parity_tests();
    printf("== util: resize ==\n");
    util_resize_tests();
    printf("== util: tonemap ==\n");
    util_tonemap_tests();
    printf("== util: colorspace ==\n");
    util_color_tests();
    printf("== util: transfer functions ==\n");
    util_transfer_tests();
    printf("== util: 3D LUT ==\n");
    util_lut_tests();
}

int main(void) {
    static const char *poc[] = {
        "test/unit/regression/poc-1383755b301e5f505b2198dc0508918b537fdf48bbfc6deeffe268822e6f6cd6",
        "test/unit/regression/poc-255456016cca60ddb5c5ed6898182e13739bf687b17d1411e97bb60ad95e7a84_min",
        "test/unit/regression/poc-360c3b0555cb979ca108f2d178cf8a80959cfeabaa4ec1d310d062fa653a8c6b_min",
        "test/unit/regression/poc-e7fa6404daa861369d2172fe68e08f9d38c0989f57da7bcfb510bab67e19ca9f",
    };
    size_t i;

    printf("== valid corpus ==\n");
    expect_load("asakusa.exr", 1, 660, 440, 4);
    expect_load("test/unit/regression/2by2.exr", 1, 2, 2, 4);
    expect_load("test/unit/regression/flaga.exr", 1, 128, 64, 8);
    expect_load("test/unit/regression/000-issue194.exr", 1, 1024, 1024, 3);
    expect_load("test/unit/regression/issue-160-piz-decode.exr", 1, 420, 32, 3);
    expect_load("test/unit/regression/piz-bug-issue-100.exr", 1, 35, 1, 1);
    expect_load("test/unit/regression/tiled_half_1x1_alpha.exr", 1, 1, 1, 1);

    printf("== malformed (must reject + free safely) ==\n");
    expect_fail("test/unit/regression/issue-238-double-free.exr");
    expect_fail("test/unit/regression/issue-238-double-free-multipart.exr");

    printf("== fuzzer PoCs (must not crash) ==\n");
    for (i = 0; i < sizeof(poc) / sizeof(poc[0]); ++i) run_safe(poc[i]);

    printf("== writer round-trip (load -> save -> reload) ==\n");
    roundtrip("asakusa.exr", EXR_COMPRESSION_NONE, "NONE");
    roundtrip("asakusa.exr", EXR_COMPRESSION_RLE, "RLE");
    roundtrip("asakusa.exr", EXR_COMPRESSION_ZIPS, "ZIPS");
    roundtrip("asakusa.exr", EXR_COMPRESSION_ZIP, "ZIP");
    roundtrip("test/unit/regression/flaga.exr", EXR_COMPRESSION_ZIP, "ZIP-8ch");
    roundtrip("asakusa.exr", EXR_COMPRESSION_PIZ, "PIZ");
    roundtrip("test/unit/regression/000-issue194.exr", EXR_COMPRESSION_PIZ, "PIZ-3ch");
    roundtrip("asakusa.exr", EXR_COMPRESSION_ZSTD, "ZSTD");
    roundtrip("test/unit/regression/flaga.exr", EXR_COMPRESSION_ZSTD, "ZSTD-8ch");
    /* HTJ2K encode->decode on a real multi-channel HALF image. The htj2k32
     * geometry (16-line res5 codeblocks) exposed a packet-header bit-stuffing
     * bug: a header ending in 0xFF needs a trailing 0x00 stuffing byte, else the
     * codeblock data desyncs by one byte (regression guard). */
    roundtrip("asakusa.exr", EXR_COMPRESSION_HTJ2K256, "HTJ2K256");
    roundtrip("asakusa.exr", EXR_COMPRESSION_HTJ2K32, "HTJ2K32");
    tiled_roundtrip("asakusa.exr", EXR_COMPRESSION_ZIP, "ZIP");
    tiled_roundtrip("asakusa.exr", EXR_COMPRESSION_ZSTD, "ZSTD");
    zstd_corruption_rejects("asakusa.exr");
    jph_frontend_rejects_malformed();
    jph_transforms_roundtrip();
    jph_packet_helpers();

    printf("== HTJ2K / JPH real-file decode ==\n");
    jph_decode_matches("openexr-images/TestImages/AllHalfValues.exr",
                       "openexr-images/TestImages/htj2k256_AllHalfValues.exr",
                       "htj2k256_AllHalfValues");
    jph_decode_matches("openexr-images/TestImages/AllHalfValues.exr",
                       "openexr-images/TestImages/htj2k32_AllHalfValues.exr",
                       "htj2k32_AllHalfValues");
    jph_decode_matches("openexr-images/TestImages/BrightRingsNanInf.exr",
                       "openexr-images/TestImages/htj2k256_BrightRingsNanInf.exr",
                       "htj2k256_BrightRingsNanInf");
    jph_decode_matches("openexr-images/TestImages/BrightRingsNanInf.exr",
                       "openexr-images/TestImages/htj2k32_BrightRingsNanInf.exr",
                       "htj2k32_BrightRingsNanInf");
    jph_decode_matches("openexr-images/TestImages/stripes.exr",
                       "openexr-images/TestImages/htj2k256_stripes.exr",
                       "htj2k256_stripes");
    jph_decode_matches("openexr-images/TestImages/stripes.exr",
                       "openexr-images/TestImages/htj2k32_stripes.exr",
                       "htj2k32_stripes");
    jph_decode_matches("openexr-images/TestImages/RgbRampsDiagonal.exr",
                       "openexr-images/TestImages/htj2k256_RgbRampsDiagonal.exr",
                       "htj2k256_RgbRampsDiagonal");
    jph_decode_matches("openexr-images/TestImages/RgbRampsDiagonal.exr",
                       "openexr-images/TestImages/htj2k32_RgbRampsDiagonal.exr",
                       "htj2k32_RgbRampsDiagonal");
    jph_decode_matches("openexr-images/TestImages/WideFloatRange.exr",
                       "openexr-images/TestImages/htj2k256_WideFloatRange.exr",
                       "htj2k256_WideFloatRange");
    jph_decode_matches("openexr-images/TestImages/WideFloatRange.exr",
                       "openexr-images/TestImages/htj2k32_WideFloatRange.exr",
                       "htj2k32_WideFloatRange");

    {
        /* test/unit/regression/2by2_htj2k32.exr: 2x2 RGBA HALF, HTJ2K32.
         * Captured from a known-good v3 decode; used here to assert that
         * decode produces byte-equal output independent of the openexr-images
         * corpus. */
        static const unsigned char px_A[] = {0x00,0x3c, 0x00,0x3c, 0x04,0x34, 0x00,0x3c};
        static const unsigned char px_B[] = {0x00,0x3c, 0x00,0x00, 0x00,0x3c, 0x00,0x00};
        static const unsigned char px_G[] = {0x00,0x3c, 0x00,0x00, 0x27,0x37, 0x00,0x00};
        static const unsigned char px_R[] = {0x00,0x3c, 0x00,0x3c, 0x00,0x00, 0x00,0x00};
        const unsigned char *exp[] = {px_A, px_B, px_G, px_R};
        const size_t sizes[] = {sizeof(px_A), sizeof(px_B), sizeof(px_G), sizeof(px_R)};
        static const char *names[] = {"A", "B", "G", "R"};
        int w = 2, h = 2;
        jph_decode_known_pixels("test/unit/regression/2by2_htj2k32.exr",
                                "2by2_htj2k32", &w, &h, names, exp, sizes, 4);
    }
    {
        /* test/unit/regression/tiled_htj2k256.exr: 1x1 A HALF, HTJ2K256, tiled. */
        static const unsigned char px_A[] = {0x00,0x3c};
        const unsigned char *exp[] = {px_A};
        const size_t sizes[] = {sizeof(px_A)};
        static const char *names[] = {"A"};
        int w = 1, h = 1;
        jph_decode_known_pixels("test/unit/regression/tiled_htj2k256.exr",
                                "tiled_htj2k256", &w, &h, names, exp, sizes, 1);
    }

    printf("== HTJ2K/JPH writer ==\n");
    roundtrip("test/unit/regression/2by2.exr",
              EXR_COMPRESSION_HTJ2K32, "HTJ2K32");
    roundtrip("test/unit/regression/2by2.exr",
              EXR_COMPRESSION_HTJ2K256, "HTJ2K256");
    roundtrip("openexr-images/TestImages/AllHalfValues.exr",
              EXR_COMPRESSION_HTJ2K32, "HTJ2K32 AllHalfValues");
    roundtrip("openexr-images/TestImages/AllHalfValues.exr",
              EXR_COMPRESSION_HTJ2K256, "HTJ2K256 AllHalfValues");
    roundtrip("openexr-images/TestImages/BrightRingsNanInf.exr",
              EXR_COMPRESSION_HTJ2K256, "HTJ2K256 BrightRingsNanInf");
    roundtrip("openexr-images/TestImages/RgbRampsDiagonal.exr",
              EXR_COMPRESSION_HTJ2K32, "HTJ2K32 RgbRampsDiagonal");
    roundtrip("openexr-images/TestImages/WideFloatRange.exr",
              EXR_COMPRESSION_HTJ2K32, "HTJ2K32 WideFloatRange");
    roundtrip("openexr-images/TestImages/WideFloatRange.exr",
              EXR_COMPRESSION_HTJ2K256, "HTJ2K256 WideFloatRange");
    jph_encode_subsampling_roundtrip();
    jph_encode_uint_roundtrip();
    jph_encode_rct_roundtrip();
    jph_encode_mixed_precision_roundtrip();

    printf("== JPH SIMD kernels ==\n");
    jph_simd_check();

    printf("== fpnge PSHUFB Huffman-emit ==\n");
    fpnge_check();

    printf("== B44 perceptual tables ==\n");
    b44_table_check();

    printf("== streaming block decode (parity vs full read) ==\n");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_NONE, 0,
                        EXR_TILE_ONE_LEVEL, "decode scanline NONE");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 0,
                        EXR_TILE_ONE_LEVEL, "decode scanline ZIP");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_PIZ, 0,
                        EXR_TILE_ONE_LEVEL, "decode scanline PIZ");
    stream_decode_check("test/unit/regression/flaga.exr", EXR_COMPRESSION_ZIP, 0,
                        EXR_TILE_ONE_LEVEL, "decode scanline ZIP 8ch");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 1,
                        EXR_TILE_ONE_LEVEL, "decode tiled ONE_LEVEL ZIP");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 1,
                        EXR_TILE_MIPMAP_LEVELS, "decode tiled MIPMAP ZIP (L0)");
    stream_decode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 1,
                        EXR_TILE_RIPMAP_LEVELS, "decode tiled RIPMAP ZIP (L0)");

    printf("== streaming block encode (round-trip) ==\n");
    stream_encode_check("asakusa.exr", EXR_COMPRESSION_NONE, 0,
                        "encode scanline NONE");
    stream_encode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 0,
                        "encode scanline ZIP");
    stream_encode_check("asakusa.exr", EXR_COMPRESSION_PIZ, 0,
                        "encode scanline PIZ");
    stream_encode_check("test/unit/regression/flaga.exr", EXR_COMPRESSION_ZIP, 0,
                        "encode scanline ZIP 8ch");
    stream_encode_check("asakusa.exr", EXR_COMPRESSION_ZIP, 1,
                        "encode tiled ONE_LEVEL ZIP");
    stream_tiled_levels_check("asakusa.exr", EXR_TILE_ONE_LEVEL,
                              "encode tiled ONE_LEVEL (all tiles)");
    stream_tiled_levels_check("asakusa.exr", EXR_TILE_MIPMAP_LEVELS,
                              "encode tiled MIPMAP (all levels)");
    stream_tiled_levels_check("asakusa.exr", EXR_TILE_RIPMAP_LEVELS,
                              "encode tiled RIPMAP (all levels)");

    printf("== streaming deep + suspend/resume + memory bound ==\n");
    deep_tiled_oob_rejects();
    stream_deep_check("data/deepscanline.exr", EXR_COMPRESSION_ZIPS,
                      "deep scanline ZIPS");
#ifndef EXR_NO_ZSTD
    stream_deep_check("data/deepscanline.exr", EXR_COMPRESSION_ZSTD,
                      "deep scanline ZSTD");
#endif
#if defined(EXR_USE_THREADS)
    deep_encode_thread_check("data/deepscanline.exr");
#endif
    /* Regression: an OpenEXR-authored deep-tiled file (per-row cumulative
     * offset tables) decodes via the high-level loader. */
    {
        exr_image di;
        memset(&di, 0, sizeof(di));
        if (EXR_OK(exr_load_from_file("data/deep_tiled_sample.exr", NULL, &di))) {
            int ok = di.num_parts == 1 && di.parts[0].is_deep &&
                     di.parts[0].deep_total_samples > 0;
            CHECK(ok, "deep-tiled sample loads (data/deep_tiled_sample.exr)");
#if defined(EXR_USE_THREADS)
            /* Re-decode the deep tiles with 4 workers: the parallel per-tile
             * scatter must match the single-threaded decode bit-for-bit. */
            if (ok) {
                exr_image d4;
                int c;
                size_t npix = (size_t)di.parts[0].width * di.parts[0].height;
                memset(&d4, 0, sizeof(d4));
                exr_set_num_threads(4);
                if (!EXR_OK(exr_load_from_file("data/deep_tiled_sample.exr",
                                               NULL, &d4)))
                    ok = 0;
                else {
                    ok = d4.parts[0].deep_total_samples ==
                             di.parts[0].deep_total_samples &&
                         memcmp(d4.parts[0].deep_sample_counts,
                                di.parts[0].deep_sample_counts,
                                npix * sizeof(int32_t)) == 0;
                    for (c = 0; ok && c < di.parts[0].header.num_channels; ++c) {
                        size_t ps = (di.parts[0].header.channels[c].pixel_type ==
                                     EXR_PIXEL_HALF) ? 2 : 4;
                        if (memcmp(d4.parts[0].deep_images[c],
                                   di.parts[0].deep_images[c],
                                   (size_t)di.parts[0].deep_total_samples * ps) != 0)
                            ok = 0;
                    }
                }
                exr_set_num_threads(1);
                exr_image_free(&d4);
                CHECK(ok, "deep-tiled decode parity (1 vs 4 threads)");
            }
#endif
            exr_image_free(&di);
        } else {
            CHECK(0, "deep-tiled sample loads (data/deep_tiled_sample.exr)");
        }
    }
    stream_would_block_check("asakusa.exr", EXR_COMPRESSION_NONE,
                             "asakusa NONE");
    stream_would_block_check("asakusa.exr", EXR_COMPRESSION_ZIP,
                             "asakusa ZIP");
    stream_would_block_check("asakusa.exr", EXR_COMPRESSION_PIZ,
                             "asakusa PIZ");
    stream_memory_bound_check("asakusa.exr", EXR_COMPRESSION_ZIP,
                              "asakusa ZIP");

#if defined(EXR_USE_THREADS)
    printf("== multithreading (serial vs parallel) ==\n");
    thread_tests("asakusa.exr");
#endif

    printf("== spectral (JCGT layout) ==\n");
    spectral_tests();

    printf("== util module ==\n");
    util_tests();

    printf("\n%d passed, %d failed\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}
