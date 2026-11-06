/*
 * codec_diff - differential harness: tinyexr v3 codecs vs the Lean model.
 *
 * Reads the vector file produced by `lake exe codecgen` and, for every
 * record, runs the corresponding tinyexr v3 codec decoder on the bytes the
 * Lean model produced and compares the output bit-exactly with the Lean
 * model's expected decoded bytes.
 *
 * Record kinds:
 *   0  PXR24 UINT  (4-byte planes, lossless)
 *   1  PXR24 HALF  (2-byte planes, lossless)
 *   2  PXR24 FLOAT (3-byte planes, lossy via float24)
 *   3  B44 4x4 block (14- or 3-byte block, HALF channels)
 *
 * The PXR24 decoder is fed the plane bytes directly: when the source size
 * equals the intermediate size the C decoder takes its memcpy fast path and
 * skips zlib, which is exactly the byte-plane algebra the Lean model states.
 *
 * Usage: codec_diff <vectors.bin>
 * Exit status: 0 all records bit-exact, 1 mismatch, 2 usage/io error.
 *
 * Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "exr_internal.h"

static uint32_t rd_u32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

static int run_pxr24(const uint8_t *rec, size_t len, int kind, uint32_t count) {
    const exr_pixel_type ptype =
        kind == 0 ? EXR_PIXEL_UINT : (kind == 1 ? EXR_PIXEL_HALF : EXR_PIXEL_FLOAT);
    const size_t bpc = kind == 0 ? 4u : (kind == 1 ? 2u : 3u);
    const size_t out_bpc = kind == 1 ? 2u : 4u;
    /* record: kind,0,count, count*4 values, encLen, enc, decLen, dec */
    size_t off = 2 + 4 + (size_t)count * 4;
    if (off + 4 > len) return 2;
    const uint32_t enc_len = rd_u32(rec + off);
    off += 4;
    const uint8_t *enc = rec + off;
    off += enc_len;
    if (off + 4 > len) return 2;
    const uint32_t dec_len = rd_u32(rec + off);
    off += 4;
    const uint8_t *dec = rec + off;

    if (enc_len != (size_t)count * bpc || dec_len != (size_t)count * out_bpc) {
        fprintf(stderr, "vector size mismatch (kind %d count %u)\n", kind, count);
        return 2;
    }

    exr_channel ch;
    memset(&ch, 0, sizeof(ch));
    ch.name[0] = 'Y';
    ch.pixel_type = ptype;
    ch.p_linear = 0;
    ch.x_sampling = 1;
    ch.y_sampling = 1;

    exr_codec_ctx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.alloc = exr_default_allocator();
    ctx.compression = EXR_COMPRESSION_PXR24;
    ctx.channels = &ch;
    ctx.num_channels = 1;
    ctx.x = 0;
    ctx.y = 0;
    ctx.width = (int)count;
    ctx.num_lines = 1;

    uint8_t *dst = (uint8_t *)malloc(dec_len ? dec_len : 1);
    if (!dst) return 2;
    exr_result rc = exr_pxr24_decompress(&ctx, enc, enc_len, dst, dec_len);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "pxr24 decode failed rc=%d kind=%d count=%u\n",
                (int)rc, kind, count);
        free(dst);
        return 1;
    }
    int mismatch = memcmp(dst, dec, dec_len) != 0;
    if (mismatch) {
        size_t i;
        fprintf(stderr, "PX mismatch kind=%d count=%u:", kind, count);
        for (i = 0; i < dec_len && i < 64; i++)
            if (dst[i] != dec[i]) {
                fprintf(stderr, " byte %zu c=%02x lean=%02x", i, dst[i], dec[i]);
                break;
            }
        fprintf(stderr, "\n");
    }
    free(dst);
    return mismatch ? 1 : 0;
}

/* B44 / B44A: compare the C pack and unpack byte-exactly with the Lean model
 * (the Lean record carries the packed bytes and the expected decoded halves). */
static int run_b44(const uint8_t *rec, size_t len, int kind) {
    const uint32_t count = 16;
    size_t off = 2 + 4 + (size_t)count * 4;
    if (off + 4 > len) return 2;
    const uint32_t enc_len = rd_u32(rec + off);
    off += 4;
    const uint8_t *enc = rec + off;
    off += enc_len;
    if (off + 4 > len) return 2;
    const uint32_t dec_len = rd_u32(rec + off);
    off += 4;
    const uint8_t *dec = rec + off;
    const int flatfields = (kind == 4);

    exr_channel ch;
    memset(&ch, 0, sizeof(ch));
    ch.name[0] = 'Y';
    ch.pixel_type = EXR_PIXEL_HALF;
    ch.x_sampling = 1;
    ch.y_sampling = 1;

    exr_codec_ctx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.alloc = exr_default_allocator();
    ctx.compression = flatfields ? EXR_COMPRESSION_B44A : EXR_COMPRESSION_B44;
    ctx.channels = &ch;
    ctx.num_channels = 1;
    ctx.x = 0;
    ctx.y = 0;
    ctx.width = 4;
    ctx.num_lines = 4;

    /* 1) decode: C(decode)(Lean packed bytes) == Lean decoded halves */
    if (dec_len != 32) return 2;
    uint8_t dst[32];
    exr_result rc = exr_b44_decompress(&ctx, enc, enc_len, dst, sizeof(dst), flatfields);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "b44 decode failed rc=%d kind=%d\n", (int)rc, kind);
        return 1;
    }
    if (memcmp(dst, dec, 32) != 0) {
        int t;
        fprintf(stderr, "B44 decode mismatch kind=%d c:", kind);
        for (t = 0; t < 32; t++) fprintf(stderr, " %02x", dst[t]);
        fprintf(stderr, "\n  lean:");
        for (t = 0; t < 32; t++) fprintf(stderr, " %02x", dec[t]);
        fprintf(stderr, "\n");
        return 1;
    }

    /* 2) encode: C(compress)(input halves) == Lean packed bytes */
    uint8_t blk[32];
    {
        int i;
        for (i = 0; i < 16; i++) {
            uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
            blk[i * 2] = (uint8_t)(v & 0xff);
            blk[i * 2 + 1] = (uint8_t)((v >> 8) & 0xff);
        }
    }
    uint8_t *out = NULL;
    size_t outsz = 0;
    rc = exr_b44_compress(&ctx, blk, sizeof(blk), &out, &outsz, flatfields);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "b44 encode failed rc=%d kind=%d\n", (int)rc, kind);
        return 1;
    }
    int mismatch = 0;
    if (outsz != enc_len) {
        fprintf(stderr, "B44 encode size mismatch kind=%d c=%zu lean=%u\n",
                kind, outsz, enc_len);
        mismatch = 1;
    } else if (memcmp(out, enc, enc_len) != 0) {
        fprintf(stderr, "B44 encode mismatch kind=%d\n", kind);
        mismatch = 1;
    }
    free(out);
    return mismatch ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <vectors.bin>\n", argv[0]);
        return 2;
    }
    FILE *fp = fopen(argv[1], "rb");
    if (!fp) { perror(argv[1]); return 2; }
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    uint8_t *buf = (uint8_t *)malloc((size_t)sz);
    if (!buf) { fclose(fp); return 2; }
    if (fread(buf, 1, (size_t)sz, fp) != (size_t)sz) { fclose(fp); free(buf); return 2; }
    fclose(fp);

    if (sz < 8 || memcmp(buf, "TEXV", 4) != 0) {
        fprintf(stderr, "bad vector file\n");
        free(buf);
        return 2;
    }
    uint32_t nrec = rd_u32(buf + 4);
    size_t off = 8;
    uint32_t i;
    unsigned failures = 0;
    unsigned checked = 0;
    for (i = 0; i < nrec; i++) {
        if (off + 6 > (size_t)sz) { failures++; break; }
        const uint8_t kind = buf[off];
        const uint8_t reserved = buf[off + 1];
        (void)reserved;
        const uint32_t count = rd_u32(buf + off + 2);
        /* find this record's extent: values + encLen + enc + decLen + dec */
        size_t rec_start = off;
        size_t cursor = off + 6 + (size_t)count * 4;
        if (cursor + 4 > (size_t)sz) { failures++; break; }
        const uint32_t enc_len = rd_u32(buf + cursor);
        cursor += 4 + enc_len;
        if (cursor + 4 > (size_t)sz) { failures++; break; }
        const uint32_t dec_len = rd_u32(buf + cursor);
        cursor += 4 + dec_len;
        if (cursor > (size_t)sz) { failures++; break; }

        int rc;
        if (kind <= 2) {
            rc = run_pxr24(buf + rec_start, cursor - rec_start, kind, count);
        } else if (kind == 3 || kind == 4) {
            rc = run_b44(buf + rec_start, cursor - rec_start, kind);
        } else {
            rc = 0;
        }
        if (rc != 0) { failures++; if (failures <= 3) fprintf(stderr, "FAIL rec %u kind %u count %u\n", i, (unsigned)kind, count); }
        checked++;
        off = cursor;
    }

    printf("codec_diff: %u records checked, %u failures\n", checked, failures);
    free(buf);
    return failures ? 1 : 0;
}
