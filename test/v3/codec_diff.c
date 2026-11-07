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
 *   4  B44A 4x4 block
 *   5  RLE byte-run block (interleave + predictor + run codec)
 *   6  ADLER32 checksum over byte streams
 *
 *   7  ZIP predictor/checksum and wrapper integration
 *   8/9 PIZ small/full-range wavelet pairs and 2x2 cells
 *   10 PIZ bitmap and range LUT
 *   11 PIZ canonical Huffman code assignment
 *   12 PIZ Huffman length-table serialization
 *   13 PIZ symbol/RLE entropy stream with a supplied codebook
 *   14 PXR24 mixed-type, sampled multi-row block
 *   15/16 PIZ small/full-range multilevel traversal, lane strides, canaries
 *   17 PIZ frequency heap -> code lengths and canonical words
 *   18 Complete frequency-derived Huffman packets
 *   19 Huffman packet acceptance/sample comparisons, malformed and lenient
 *
 * Encoder DEFLATE streams are inflated and compared against Lean intermediate
 * bytes. Raw fallback retains canonical input pixels. DEFLATE is opaque to
 * the formal model. PIZ's private kernels are included under test-only names.
 *
 * Usage: codec_diff <vectors.bin>
 * Exit status: 0 all records bit-exact, 1 mismatch, 2 usage/io error.
 *
 * Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "exr_internal.h"

static uint32_t rd_u32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

/* Verify actual encoder output after inflating its opaque DEFLATE payload.
 * The raw fallback retains original float bits, including the low byte. */
static int check_pxr24_stream(exr_codec_ctx *ctx, const uint8_t *raw,
                             const uint8_t *planes, size_t plane_size,
                             const uint8_t *expected, size_t raw_size) {
    uint8_t *inflated = (uint8_t *)malloc(plane_size ? plane_size : 1);
    uint8_t *decoded = (uint8_t *)malloc(raw_size ? raw_size : 1);
    uint8_t *packed = NULL;
    size_t packed_size = 0, got = 0;
    int failed = 1;
    if (!inflated || !decoded) goto done;
    if (!EXR_OK(exr_pxr24_compress(ctx, raw, raw_size, &packed, &packed_size))) goto done;
    if (packed_size == raw_size) {
        if (memcmp(packed, raw, raw_size)) goto done;
    } else {
        if (!EXR_OK(exr_zlib_inflate(packed, packed_size, inflated, plane_size, &got)) ||
            got != plane_size || memcmp(inflated, planes, plane_size)) goto done;
        if (!EXR_OK(exr_pxr24_decompress(ctx, packed, packed_size, decoded, raw_size)) ||
            memcmp(decoded, expected, raw_size)) goto done;
    }
    /* Also exercise compressed decode when the encoder chose raw fallback. */
    exr_free(ctx->alloc, packed);
    packed = NULL;
    if (!EXR_OK(exr_zlib_deflate(ctx->alloc, planes, plane_size, &packed, &packed_size))) goto done;
    if (packed_size != plane_size &&
        (!EXR_OK(exr_pxr24_decompress(ctx, packed, packed_size, decoded, raw_size)) ||
         memcmp(decoded, expected, raw_size))) goto done;
    failed = 0;
done:
    exr_free(ctx->alloc, packed);
    free(inflated); free(decoded);
    if (failed) fprintf(stderr, "PXR24 encoder/DEFLATE integration mismatch raw_size=%zu\n", raw_size);
    return failed;
}

static int check_pxr24_encode(exr_codec_ctx *ctx, const uint8_t *rec,
                             uint32_t count, size_t out_bpc,
                             const uint8_t *planes, size_t plane_size,
                             const uint8_t *expected, size_t raw_size) {
    uint8_t *raw = (uint8_t *)malloc(raw_size ? raw_size : 1);
    int failed;
    if (!raw) return 2;
    for (uint32_t i = 0; i < count; ++i)
        for (size_t j = 0; j < out_bpc; ++j)
            raw[(size_t)i * out_bpc + j] = rec[6 + (size_t)i * 4 + j];
    failed = check_pxr24_stream(ctx, raw, planes, plane_size, expected, raw_size);
    free(raw);
    return failed;
}

static int run_pxr24_mixed(const uint8_t *rec, uint32_t count) {
    const size_t off = 6 + (size_t)count * 4;
    const uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    const uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    const unsigned group_count[] = {6, 12, 4, 12, 4, 6, 12, 4};
    const unsigned group_bpc[] = {2, 4, 4, 4, 4, 2, 4, 4};
    uint8_t raw[216], decoded[216];
    unsigned sample = 0, out = 0;
    exr_channel channels[3];
    exr_codec_ctx ctx;
    if (count != 60 || enc_len != 180 || dec_len != sizeof(raw)) return 2;
    for (unsigned g = 0; g < 8; ++g)
        for (unsigned i = 0; i < group_count[g]; ++i, ++sample)
            for (unsigned j = 0; j < group_bpc[g]; ++j)
                raw[out++] = rec[6 + (size_t)sample * 4 + j];
    memset(channels, 0, sizeof(channels));
    channels[0].pixel_type = EXR_PIXEL_HALF;
    channels[0].x_sampling = 2; channels[0].y_sampling = 2;
    channels[1].pixel_type = EXR_PIXEL_FLOAT;
    channels[1].x_sampling = 1; channels[1].y_sampling = 1;
    channels[2].pixel_type = EXR_PIXEL_UINT;
    channels[2].x_sampling = 3; channels[2].y_sampling = 1;
    memset(&ctx, 0, sizeof(ctx));
    ctx.alloc = exr_default_allocator(); ctx.compression = EXR_COMPRESSION_PXR24;
    ctx.channels = channels; ctx.num_channels = 3;
    ctx.x = -4; ctx.y = -2; ctx.width = 12; ctx.num_lines = 3;
    if (!EXR_OK(exr_pxr24_decompress(&ctx, enc, enc_len, decoded, sizeof(decoded))) ||
        memcmp(decoded, dec, sizeof(decoded))) return 1;
    return check_pxr24_stream(&ctx, raw, enc, enc_len, dec, sizeof(raw));
}

/* ZIP records carry the Lean predictor/interleave stream and its big-endian
 * Adler trailer. Test both compressed and dispatcher-level raw-fallback paths. */
static int run_zip(const uint8_t *rec, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    const uint8_t *raw = enc + enc_len + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const exr_allocator *a = exr_default_allocator();
    uint8_t *tmp = NULL, *dst = NULL, *packed = NULL;
    size_t packed_size = 0, got = 0;
    int failed = 1;
    if (!count || enc_len != (size_t)count + 4 || dec_len != count) return 2;
    tmp = (uint8_t *)malloc(count);
    dst = (uint8_t *)malloc(count);
    if (!tmp || !dst) goto done;
    for (uint32_t i = 0; i < count; ++i)
        if (rd_u32(rec + 6 + (size_t)i * 4) != raw[i]) goto done;
    if (!EXR_OK(exr_zip_compress(a, raw, count, &packed, &packed_size))) goto done;
    if (packed_size == count) {
        if (memcmp(packed, raw, count)) goto done;
    } else {
        if (packed_size < 6 || memcmp(packed + packed_size - 4, enc + count, 4)) goto done;
        if (!EXR_OK(exr_zlib_inflate(packed, packed_size, tmp, count, &got)) ||
            got != count || memcmp(tmp, enc, count)) goto done;
        if (!EXR_OK(exr_zip_decompress(a, packed, packed_size, dst, count)) ||
            memcmp(dst, raw, count)) goto done;
    }
    exr_free(a, packed); packed = NULL;
    if (!EXR_OK(exr_zlib_deflate(a, enc, count, &packed, &packed_size))) goto done;
    if (packed_size < 6 || memcmp(packed + packed_size - 4, enc + count, 4)) goto done;
    if (!EXR_OK(exr_zip_decompress(a, packed, packed_size, dst, count)) || memcmp(dst, raw, count)) goto done;
    /* Check header, trailer, truncation, and inflated-size rejection. */
    packed[0] ^= 1;
    if (EXR_OK(exr_zip_decompress(a, packed, packed_size, dst, count))) goto done;
    packed[0] ^= 1;
    packed[packed_size - 1] ^= 1;
    if (EXR_OK(exr_zip_decompress(a, packed, packed_size, dst, count))) goto done;
    packed[packed_size - 1] ^= 1;
    if (EXR_OK(exr_zip_decompress(a, packed, packed_size - 1, dst, count))) goto done;
    if (count > 1 && EXR_OK(exr_zip_decompress(a, packed, packed_size, dst, count - 1))) goto done;
    failed = 0;
done:
    free(tmp); free(dst); exr_free(a, packed);
    if (failed) fprintf(stderr, "ZIP integration mismatch count=%u\n", count);
    return failed;
}

/* Compile the actual PIZ implementation under test-only public symbol names
 * to access its private kernels without changing the library's API. */
#define exr_piz_context_free lean_probe_piz_context_free
#define exr_piz_compress lean_probe_piz_compress
#define exr_piz_decompress lean_probe_piz_decompress
#include "../../src/exr_piz.c"
#undef exr_piz_context_free
#undef exr_piz_compress
#undef exr_piz_decompress

static int run_piz(const uint8_t *rec, int kind, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    if (kind == 8 || kind == 9) {
        uint16_t x[4], l, h;
        if (count != 4 || enc_len != 12 || dec_len != 8) return 2;
        for (unsigned i = 0; i < 4; ++i) {
            uint32_t v = rd_u32(rec + 6 + i * 4);
            if (v > (kind == 8 ? 16383u : 65535u)) return 2;
            x[i] = (uint16_t)v;
        }
        if (kind == 8) wenc14(x[0], x[1], &l, &h);
        else wenc16(x[0], x[1], &l, &h);
        if (l != exr_rd_u16(enc + 8) || h != exr_rd_u16(enc + 10)) return 1;
        wav2_encode(x, 2, 1, 2, 2, kind == 8 ? 16383 : 65535);
        for (unsigned i = 0; i < 4; ++i)
            if (x[i] != exr_rd_u16(enc + i * 2)) return 1;
        wav2_decode(x, 2, 1, 2, 2, kind == 8 ? 16383 : 65535);
        for (unsigned i = 0; i < 4; ++i)
            if (x[i] != exr_rd_u16(dec + i * 2)) return 1;
        if (kind == 8) wdec14(l, h, &x[0], &x[1]);
        else wdec16(l, h, &x[0], &x[1]);
        return x[0] != exr_rd_u16(dec) || x[1] != exr_rd_u16(dec + 2);
    }
    if (kind == 10) {
        uint8_t bitmap[PIZ_BITMAP_SIZE];
        uint16_t *data = NULL, *lut = NULL, *rev = NULL;
        uint16_t lo, hi, mx;
        int failed = 1;
        if (enc_len != PIZ_BITMAP_SIZE + (size_t)count * 2 || dec_len != (size_t)count * 2) return 2;
        data = (uint16_t *)malloc(count ? (size_t)count * 2 : 2);
        lut = (uint16_t *)malloc(PIZ_USHORT_RANGE * 2);
        rev = (uint16_t *)malloc(PIZ_USHORT_RANGE * 2);
        if (!data || !lut || !rev) goto lut_done;
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
            if (v > 65535) goto lut_done;
            data[i] = (uint16_t)v;
        }
        bitmap_from_data(data, count, bitmap, &lo, &hi);
        if (memcmp(bitmap, enc, PIZ_BITMAP_SIZE)) goto lut_done;
        mx = forward_lut_from_bitmap(bitmap, lut);
        if (reverse_lut_from_bitmap(bitmap, rev) != mx) goto lut_done;
        for (uint32_t i = 0; i < count; ++i) {
            if (lut[data[i]] != exr_rd_u16(enc + PIZ_BITMAP_SIZE + (size_t)i * 2) ||
                rev[lut[data[i]]] != exr_rd_u16(dec + (size_t)i * 2)) goto lut_done;
        }
        failed = 0;
lut_done:
        free(data); free(lut); free(rev);
        return failed;
    }
    if (kind == 11) {
        int64_t *codes;
        uint8_t *lengths;
        uint32_t *symbols;
        size_t ns = 0;
        int failed = 0;
        if (!count || count > PIZ_HUF_ENCSIZE || enc_len != (size_t)count * 8 || dec_len != 0) return 2;
        codes = (int64_t *)calloc(count, sizeof(*codes));
        lengths = (uint8_t *)calloc(count, 1);
        symbols = (uint32_t *)malloc((size_t)count * 4);
        if (!codes || !lengths || !symbols) { free(codes); free(lengths); free(symbols); return 2; }
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
            if (v > 58) { failed = 1; goto codes_done; }
            lengths[i] = (uint8_t)v;
            codes[i] = v;
            if (v) symbols[ns++] = i;
        }
        canonical_code_table64(codes, 0, (int)count - 1);
        for (uint32_t i = 0; i < count; ++i)
            if ((uint64_t)codes[i] != ((uint64_t)rd_u32(enc + (size_t)i * 8) |
                ((uint64_t)rd_u32(enc + (size_t)i * 8 + 4) << 32))) failed = 1;
        memset(codes, 0, (size_t)count * sizeof(*codes));
        canonical_code_table(lengths, codes, symbols, ns);
        for (uint32_t i = 0; i < count; ++i)
            if ((uint64_t)codes[i] != ((uint64_t)rd_u32(enc + (size_t)i * 8) |
                ((uint64_t)rd_u32(enc + (size_t)i * 8 + 4) << 32))) failed = 1;
codes_done:
        free(codes); free(lengths); free(symbols);
        return failed;
    }
    if (kind == 12) {
        int64_t *codes = NULL, *decoded_codes = NULL;
        uint8_t *packed = NULL, *lengths = NULL;
        uint32_t *symbols = NULL;
        uint8_t *end;
        const uint8_t *input;
        size_t ns = 0, capacity;
        int failed = 1;
        if (!count || count > PIZ_HUF_ENCSIZE || dec_len != count ||
            exr_mul_ovf((size_t)count, 2u, &capacity) || exr_add_ovf(capacity, 16u, &capacity)) return 2;
        codes = (int64_t *)calloc(count, sizeof(*codes));
        decoded_codes = (int64_t *)calloc(count, sizeof(*decoded_codes));
        packed = (uint8_t *)calloc(capacity, 1);
        lengths = (uint8_t *)calloc(count, 1);
        symbols = (uint32_t *)malloc((size_t)count * 4);
        if (!codes || !decoded_codes || !packed || !lengths || !symbols) goto lengths_done;
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
            if (v > 58 || v != dec[i]) goto lengths_done;
            codes[i] = v;
        }
        end = packed;
        huf_pack_enc_table(codes, 0, (int)count - 1, &end);
        if ((size_t)(end - packed) != enc_len || memcmp(packed, enc, enc_len)) goto lengths_done;
        input = enc;
        /* This private reader receives table plus entropy payload in the real
         * decoder. Supply one following byte for its read-ahead boundary. */
        if (enc_len >= INT_MAX || !unpack_enc_table(&input, (int)enc_len + 1, 0, (int)count - 1,
            lengths, decoded_codes, symbols, count, &ns) || memcmp(lengths, dec, count)) goto lengths_done;
        failed = 0;
lengths_done:
        free(codes); free(decoded_codes); free(packed); free(lengths); free(symbols);
        return failed;
    }
    if (kind == 13) {
        int64_t codes[17];
        uint16_t *raw = NULL, *decoded = NULL;
        uint8_t *buffer = NULL, *table_end;
        size_t capacity, table_size, payload_size;
        uint32_t expected_bits;
        int nbits, failed = 1;
        if (!count || count > INT_MAX || enc_len < 4 || dec_len != (size_t)count * 2 ||
            exr_mul_ovf((size_t)count, 2u, &capacity) || exr_add_ovf(capacity, 256u, &capacity)) return 2;
        expected_bits = rd_u32(enc);
        payload_size = enc_len - 4;
        if (((uint64_t)expected_bits + 7) / 8 != payload_size) return 2;
        raw = (uint16_t *)malloc((size_t)count * 2);
        decoded = (uint16_t *)malloc((size_t)count * 2);
        buffer = (uint8_t *)calloc(capacity, 1);
        if (!raw || !decoded || !buffer) goto payload_done;
        for (uint32_t i = 0; i < count; ++i) {
            uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
            if (v >= 16 || v != exr_rd_u16(dec + (size_t)i * 2)) goto payload_done;
            raw[i] = (uint16_t)v;
        }
        for (size_t i = 0; i < sizeof(codes) / sizeof(codes[0]); ++i) codes[i] = 5;
        canonical_code_table64(codes, 0, 16);
        table_end = buffer + 20;
        huf_pack_enc_table(codes, 0, 16, &table_end);
        table_size = (size_t)(table_end - buffer - 20);
        nbits = huf_encode(codes, raw, (int)count, 16, table_end);
        if (nbits < 0 || (uint32_t)nbits != expected_bits ||
            memcmp(table_end, enc + 4, payload_size)) goto payload_done;
        /* Feed the Lean payload to the C decoder, with its real table/header. */
        memcpy(table_end, enc + 4, payload_size);
        exr_wr_u32(buffer, 0); exr_wr_u32(buffer + 4, 16);
        exr_wr_u32(buffer + 8, (uint32_t)table_size);
        exr_wr_u32(buffer + 12, expected_bits); exr_wr_u32(buffer + 16, 0);
        if (huf_uncompress(exr_default_allocator(), NULL, buffer, 20 + table_size + payload_size,
                           decoded, count) != 1 || memcmp(decoded, raw, (size_t)count * 2)) goto payload_done;
        failed = 0;
payload_done:
        free(raw); free(decoded); free(buffer);
        return failed;
    }

    return 2;
}
static int run_piz_traversal(const uint8_t *rec, int kind, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    uint32_t w, h, lanes, base;
    size_t n;
    uint16_t *data;
    int failed = 1;
    if (count < 4) return 2;
    w = rd_u32(rec + 6); h = rd_u32(rec + 10);
    lanes = rd_u32(rec + 14); base = rd_u32(rec + 18);
    if (w > 64 || h > 64 || (lanes != 1 && lanes != 2) || base != 3) return 2;
    n = (size_t)w * h * lanes + 8;
    if ((size_t)count != n + 4 || enc_len != 2*n || dec_len != 2*n) return 2;
    data = (uint16_t *)malloc(n * sizeof(*data));
    if (!data) return 2;
    for (size_t i = 0; i < n; ++i) {
        uint32_t v = rd_u32(rec + 22 + i * 4);
        if (v > (kind == 15 ? 16383u : 65535u)) goto done;
        data[i] = (uint16_t)v;
    }
    for (uint32_t lane = 0; lane < lanes; ++lane)
        wav2_encode(data + base + lane, (int)w, (int)lanes, (int)h,
                    (int)(w*lanes), kind == 15 ? 16383 : 65535);
    for (size_t i = 0; i < n; ++i)
        if (data[i] != exr_rd_u16(enc + i * 2)) goto done;
    for (uint32_t lane = 0; lane < lanes; ++lane)
        wav2_decode(data + base + lane, (int)w, (int)lanes, (int)h,
                    (int)(w*lanes), kind == 15 ? 16383 : 65535);
    for (size_t i = 0; i < n; ++i)
        if (data[i] != exr_rd_u16(dec + i * 2) ||
            data[i] != rd_u32(rec + 22 + i * 4)) goto done;
    failed = 0;
done:
    free(data);
    return failed;
}

/* Compare the actual frequency heap/hlink builder, including sparse IDs,
 * trailing zeros, synthetic RLE symbol, and equal-frequency tie cases. */
static int run_piz_frequency(const uint8_t *rec, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    int64_t *codes;
    int im = 0, iM = 0, rc, failed = 0;
    if (count > PIZ_USHORT_RANGE) return 2;
    if (enc_len != 0 && (enc_len != ((size_t)count + 1)*8 || dec_len != count + 1)) return 2;
    codes = (int64_t *)calloc(PIZ_HUF_ENCSIZE, sizeof(*codes));
    if (!codes) return 2;
    for (uint32_t i = 0; i < count; ++i) codes[i] = rd_u32(rec + 6 + (size_t)i * 4);
    rc = huf_build_enc_table(exr_default_allocator(), codes, &im, &iM);
    if (enc_len == 0) {
        failed = rc != 0 || dec_len != 0;
    } else if (!rc) {
        failed = 1;
    } else {
        for (uint32_t i = 0; i <= count; ++i) {
            uint64_t word = (uint64_t)rd_u32(enc + (size_t)i * 8) |
                            ((uint64_t)rd_u32(enc + (size_t)i * 8 + 4) << 32);
            if ((uint64_t)codes[i] != word || ((uint64_t)codes[i] & 63u) != dec[i]) {
                fprintf(stderr, "PIZ frequency heap mismatch count=%u symbol=%u c=%llu lean=%llu\n",
                        count, i, (unsigned long long)codes[i], (unsigned long long)word);
                failed = 1;
                break;
            }
        }
    }
    free(codes);
    return failed;
}

/* Full model-generated PIZ block, including sampled-channel geometry. */
static int run_piz_block(const uint8_t *rec, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    exr_channel channels[1024];
    exr_codec_ctx ctx;
    uint8_t *decoded, *reencoded = NULL;
    size_t reencoded_size = 0;
    uint32_t nc, metadata, words, accepted, dispatched;
    exr_result decoded_rc;
    int failed = 1;
    if (count < 5) return 2;
    nc = rd_u32(rec + 22);
    if (!nc || nc > 1024 || count < 7 + 3 * nc) return 2;
    metadata = 7 + 3 * nc;
    accepted = rd_u32(rec + 6 + (size_t)(metadata - 2) * 4);
    dispatched = rd_u32(rec + 6 + (size_t)(metadata - 1) * 4);
    if (accepted > 1 || dispatched > 1) return 2;
    words = count - metadata;
    if ((size_t)words * 2 != dec_len) return 2;
    memset(channels, 0, sizeof(channels));
    for (uint32_t i = 0; i < nc; ++i) {
        const uint8_t *ch = rec + 26 + (size_t)i * 12;
        uint32_t type = rd_u32(ch), xs = rd_u32(ch + 4), ys = rd_u32(ch + 8);
        if (type > 2 || !xs || !ys || xs > INT_MAX || ys > INT_MAX) return 2;
        channels[i].pixel_type = (exr_pixel_type)type;
        channels[i].x_sampling = (int)xs;
        channels[i].y_sampling = (int)ys;
    }
    memset(&ctx, 0, sizeof(ctx));
    ctx.alloc = exr_default_allocator(); ctx.compression = EXR_COMPRESSION_PIZ;
    ctx.x = (int32_t)rd_u32(rec + 6); ctx.y = (int32_t)rd_u32(rec + 10);
    if (rd_u32(rec + 14) > INT_MAX || rd_u32(rec + 18) > INT_MAX) return 2;
    ctx.width = (int)rd_u32(rec + 14); ctx.num_lines = (int)rd_u32(rec + 18);
    if (ctx.width <= 0 || ctx.num_lines <= 0 ||
        (int64_t)ctx.x + ctx.width - 1 > INT_MAX ||
        (int64_t)ctx.y + ctx.num_lines - 1 > INT_MAX) return 2;
    ctx.channels = channels; ctx.num_channels = (int)nc;
    decoded = (uint8_t *)malloc(dec_len ? dec_len : 1);
    if (!decoded) return 2;
    for (uint32_t i = 0; i < words; ++i)
        if (rd_u32(rec + 6 + (size_t)(metadata + i) * 4) != exr_rd_u16(dec + (size_t)i * 2))
            goto done;
    decoded_rc = exr_piz_decompress(&ctx, enc, enc_len, decoded, dec_len);
    if ((EXR_OK(decoded_rc) ? 1u : 0u) != accepted ||
        (accepted && memcmp(decoded, dec, dec_len))) goto done;
    decoded_rc = exr_decompress_block(&ctx, enc, enc_len, decoded, dec_len);
    if ((EXR_OK(decoded_rc) ? 1u : 0u) != dispatched ||
        (dispatched && memcmp(decoded, enc_len == dec_len ? enc : dec, dec_len))) goto done;
    if (!EXR_OK(exr_piz_compress(&ctx, dec, dec_len, &reencoded, &reencoded_size))) goto done;
    if (enc_len < dec_len) {
        if (reencoded_size != enc_len || memcmp(reencoded, enc, enc_len)) goto done;
    } else if (reencoded_size != dec_len || memcmp(reencoded, dec, dec_len)) goto done;
    if (!EXR_OK(exr_decompress_block(&ctx, reencoded, reencoded_size, decoded, dec_len)) ||
        memcmp(decoded, dec, dec_len)) goto done;
    failed = 0;
done:
    exr_free(ctx.alloc, reencoded);
    free(decoded);
    return failed;
}

/* Compare complete Huffman packets, not only isolated table or payload bits. */
static int run_piz_packet(const uint8_t *rec, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    uint16_t *raw = NULL, *decoded = NULL;
    uint8_t *encoded = NULL;
    size_t cap;
    int err = 0, encoded_size, failed = 1;
    if (count > INT_MAX / 64u || dec_len != (size_t)count * 2 ||
        exr_mul_ovf((size_t)count, 8u, &cap) ||
        exr_add_ovf(cap, PIZ_HUF_ENCSIZE * 2u + 276u, &cap)) return 2;
    raw = (uint16_t *)malloc(count ? (size_t)count * 2 : 2);
    decoded = (uint16_t *)malloc(count ? (size_t)count * 2 : 2);
    encoded = (uint8_t *)calloc(cap, 1);
    if (!raw || !decoded || !encoded) goto done;
    for (uint32_t i = 0; i < count; ++i) {
        uint32_t v = rd_u32(rec + 6 + (size_t)i * 4);
        if (v > 65535 || v != exr_rd_u16(dec + (size_t)i * 2)) goto done;
        raw[i] = (uint16_t)v;
    }
    encoded_size = huf_compress(exr_default_allocator(), raw, (int)count, encoded, &err);
    if (err || encoded_size < 0 || (size_t)encoded_size != enc_len || memcmp(encoded, enc, enc_len)) goto done;
    if (huf_uncompress(exr_default_allocator(), NULL, enc, enc_len, decoded, count) != 1 ||
        memcmp(decoded, raw, (size_t)count * 2)) goto done;
    failed = 0;
done:
    free(raw); free(decoded); free(encoded);
    return failed;
}

static int run_piz_packet_parse(const uint8_t *rec, uint32_t count) {
    size_t off = 6 + (size_t)count * 4;
    uint32_t enc_len = rd_u32(rec + off);
    const uint8_t *enc = rec + off + 4;
    uint32_t dec_len = rd_u32(enc + enc_len);
    const uint8_t *dec = enc + enc_len + 4;
    uint16_t *decoded;
    int rc, failed = 0;
    if (!count || count > INT_MAX / 64u || (dec_len && dec_len != (size_t)count * 2)) return 2;
    decoded = (uint16_t *)malloc((size_t)count * 2);
    if (!decoded) return 2;
    rc = huf_uncompress(exr_default_allocator(), NULL, enc, enc_len, decoded, count);
    if (rc < 0) { free(decoded); return 2; }
    if (dec_len == 0) failed = rc != 0;
    else if (!rc) failed = 1;
    else for (uint32_t i = 0; i < count; ++i)
        if (decoded[i] != exr_rd_u16(dec + (size_t)i * 2)) { failed = 1; break; }
    free(decoded);
    return failed;
}

static int run_pxr24(const uint8_t *rec, size_t len, int kind, uint32_t count) {
    if (count > INT_MAX) return 2;
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
    if (check_pxr24_encode(&ctx, rec, count, out_bpc, enc, enc_len, dec, dec_len)) mismatch = 1;
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
    if (dec_len != 32 || (enc_len != 3 && enc_len != 14)) return 2;
    if ((enc_len == 3) != (enc[2] >= 52)) return 2;
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

/* RLE (kind 5): compare the C run-length codec byte-exactly with the Lean
 * model. The Lean record carries the raw row bytes, the compressed bytes and
 * the expected decoded output (the raw bytes).
 *
 * 1) decode: C(decode)(Lean compressed bytes) == raw bytes.  The C reader's
 *    equal-size memcpy fast path reproduces the raw-fallback records.
 * 2) encode: C(compress)(raw bytes) == Lean compressed bytes. */
static int run_rle(const uint8_t *rec, size_t len, uint32_t count) {
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
    if (dec_len != count) return 2;

    /* raw bytes live in the input values (low byte of each u32) */
    uint8_t *raw = (uint8_t *)malloc(count ? count : 1);
    if (!raw) return 2;
    {
        uint32_t i;
        for (i = 0; i < count; i++) raw[i] = (uint8_t)(rd_u32(rec + 6 + (size_t)i * 4) & 0xff);
    }

    if (memcmp(raw, dec, count) != 0) { free(raw); return 2; }

    /* 1) decode: reader semantics (memcpy fast path on equal sizes, then
     *    run expansion + predictor + deinterleave). */
    uint8_t *dst = (uint8_t *)malloc(count ? count : 1);
    if (!dst) { free(raw); return 2; }
    const exr_allocator *a = exr_default_allocator();
    exr_result rc;
    if (enc_len == count) {
        if (count > 0) memcpy(dst, enc, count);
        rc = EXR_SUCCESS;
    } else {
        rc = exr_rle_decompress(a, enc, enc_len, dst, count);
    }
    if (!EXR_OK(rc)) {
        fprintf(stderr, "rle decode failed rc=%d count=%u\n", (int)rc, count);
        free(raw);
        free(dst);
        return 1;
    }
    if (memcmp(dst, raw, count) != 0) {
        uint32_t i;
        fprintf(stderr, "RLE decode mismatch count=%u\n  c:", count);
        for (i = 0; i < count; i++) fprintf(stderr, " %02x", dst[i]);
        fprintf(stderr, "\n  lean:");
        for (i = 0; i < count; i++) fprintf(stderr, " %02x", raw[i]);
        fprintf(stderr, "\n");
        free(raw);
        free(dst);
        return 1;
    }
    free(dst);

    /* 2) encode: C(compress)(raw bytes) == Lean compressed bytes */
    uint8_t *out = NULL;
    size_t outsz = 0;
    rc = exr_rle_compress(a, raw, count, &out, &outsz);
    if (!EXR_OK(rc)) {
        fprintf(stderr, "rle encode failed rc=%d count=%u\n", (int)rc, count);
        free(raw);
        return 1;
    }
    int mismatch = 0;
    if (outsz != enc_len) {
        fprintf(stderr, "RLE encode size mismatch count=%u c=%zu lean=%u\n",
                count, outsz, enc_len);
        mismatch = 1;
    } else if (enc_len > 0 && memcmp(out, enc, enc_len) != 0) {
        size_t i;
        fprintf(stderr, "RLE encode mismatch count=%u\n  c:", count);
        for (i = 0; i < outsz; i++) fprintf(stderr, " %02x", out[i]);
        fprintf(stderr, "\n  lean:");
        for (i = 0; i < enc_len; i++) fprintf(stderr, " %02x", enc[i]);
        fprintf(stderr, "\n");
        mismatch = 1;
    }
    free(out);
    free(raw);
    return mismatch ? 1 : 0;
}

/* ADLER32 (kind 6): compare the Lean checksum byte-exactly with the C
 * `exr_adler32` over the raw bytes (fresh stream, initial value 1). */
static int run_adler(const uint8_t *rec, size_t len, uint32_t count) {
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
    if (enc_len != 4 || dec_len != count) return 2;
    const uint32_t lean = rd_u32(enc);

    uint8_t *raw = (uint8_t *)malloc(count ? count : 1);
    if (!raw) return 2;
    {
        uint32_t i;
        for (i = 0; i < count; i++) raw[i] = (uint8_t)(rd_u32(rec + 6 + (size_t)i * 4) & 0xff);
    }
    if (memcmp(raw, dec, count) != 0) { free(raw); return 2; }
    const uint32_t c = exr_adler32(raw, count, 1);
    if (c != lean) {
        fprintf(stderr, "adler32 mismatch count=%u c=%08x lean=%08x\n", count, c, lean);
        free(raw);
        return 1;
    }
    free(raw);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2 && argc != 3) {
        fprintf(stderr, "usage: %s <vectors.bin> [--intree|--libdeflate]\n", argv[0]);
        return 2;
    }
    if (argc == 3) {
        exr_zlib_backend backend;
        if (!strcmp(argv[2], "--intree")) backend = EXR_ZLIB_INTREE;
        else if (!strcmp(argv[2], "--libdeflate")) backend = EXR_ZLIB_LIBDEFLATE;
        else return 2;
        if (!EXR_OK(exr_zlib_set_backend(backend))) return 2;
    }
    FILE *fp = fopen(argv[1], "rb");
    if (!fp) { perror(argv[1]); return 2; }
    if (fseek(fp, 0, SEEK_END) != 0) { fclose(fp); return 2; }
    long sz = ftell(fp);
    if (sz < 8 || fseek(fp, 0, SEEK_SET) != 0) { fclose(fp); return 2; }
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
    if (nrec > ((size_t)sz - 8u) / 14u) { free(buf); return 2; }
    size_t off = 8;
    uint32_t i;
    unsigned failures = nrec == 0 ? 1u : 0u;
    unsigned checked = 0;
    enum { CODEC_KIND_COUNT = 21 };
    unsigned kinds[CODEC_KIND_COUNT] = {0};
    for (i = 0; i < nrec; i++) {
        if (off + 6 > (size_t)sz) { failures++; break; }
        const uint8_t kind = buf[off];
        const uint8_t reserved = buf[off + 1];
        if (reserved != 0 || kind >= CODEC_KIND_COUNT ||
            ((kind == 3 || kind == 4) && rd_u32(buf + off + 2) != 16)) {
            failures++; break;
        }
        const uint32_t count = rd_u32(buf + off + 2);
        /* find this record's extent: values + encLen + enc + decLen + dec */
        size_t rec_start = off;
        size_t cursor, values_bytes;
        if (exr_mul_ovf((size_t)count, 4u, &values_bytes) ||
            exr_add_ovf(off + 6u, values_bytes, &cursor)) { failures++; break; }
        if (cursor + 4 > (size_t)sz) { failures++; break; }
        const uint32_t enc_len = rd_u32(buf + cursor);
        if ((size_t)enc_len > (size_t)sz - cursor - 4u) { failures++; break; }
        cursor += 4u + (size_t)enc_len;
        if (cursor + 4 > (size_t)sz) { failures++; break; }
        const uint32_t dec_len = rd_u32(buf + cursor);
        if ((size_t)dec_len > (size_t)sz - cursor - 4u) { failures++; break; }
        cursor += 4u + (size_t)dec_len;
        if (cursor > (size_t)sz) { failures++; break; }

        int rc;
        if (kind <= 2) {
            rc = run_pxr24(buf + rec_start, cursor - rec_start, kind, count);
        } else if (kind == 3 || kind == 4) {
            rc = run_b44(buf + rec_start, cursor - rec_start, kind);
        } else if (kind == 5) {
            rc = run_rle(buf + rec_start, cursor - rec_start, count);
        } else if (kind == 6) {
            rc = run_adler(buf + rec_start, cursor - rec_start, count);
        } else if (kind == 7) {
            rc = run_zip(buf + rec_start, count);
        } else if (kind == 20) {
            rc = run_piz_block(buf + rec_start, count);
        } else if (kind == 19) {
            rc = run_piz_packet_parse(buf + rec_start, count);
        } else if (kind == 18) {
            rc = run_piz_packet(buf + rec_start, count);
        } else if (kind == 17) {
            rc = run_piz_frequency(buf + rec_start, count);
        } else if (kind == 15 || kind == 16) {
            rc = run_piz_traversal(buf + rec_start, kind, count);
        } else if (kind == 14) {
            rc = run_pxr24_mixed(buf + rec_start, count);
        } else if (kind >= 8 && kind <= 13) {
            rc = run_piz(buf + rec_start, kind, count);
        } else {
            rc = 2;
        }
        if (rc != 0) { failures++; if (failures <= 3) fprintf(stderr, "FAIL rec %u kind %u count %u\n", i, (unsigned)kind, count); }
        kinds[kind]++;
        checked++;
        off = cursor;
    }

    if (off != (size_t)sz) failures++;
    for (i = 0; i < CODEC_KIND_COUNT; ++i) {
        if (kinds[i] == 0) {
            fprintf(stderr, "missing codec vector kind %u\n", i);
            failures++;
        }
    }
    printf("codec_diff (%s): %u records checked, %u failures\n", exr_zlib_backend_name(), checked, failures);
    free(buf);
    return failures ? 1 : 0;
}
