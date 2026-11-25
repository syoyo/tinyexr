/*
 * texcomp - emit stored / fixed-Huffman DEFLATE vectors for the Lean gate.
 * The streams are built independently here and decoded with the real
 * `exr_inflate_zlib`; the Lean model must reproduce those bytes.
 * Format: <stream-hex> <expected-output-hex>
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "exr_internal.h"

static uint8_t out[4096];
static int ofs, bits, buf;

static void putbits(int v, int n) {
    buf |= v << bits;
    bits += n;
    while (bits >= 8) { out[ofs++] = (uint8_t)buf; buf >>= 8; bits -= 8; }
}
static int revbits(int v, int n) {
    int r = 0;
    for (int i = 0; i < n; ++i) r = (r << 1) | ((v >> i) & 1);
    return r;
}
static void putcode(int code, int len) { putbits(revbits(code, len), len); }
static void align(void) { while (bits) putbits(0, 1); }

static int fixed_len(int s) {
    if (s < 144) return 8;
    if (s < 256) return 9;
    if (s < 280) return 7;
    return 8;
}
static int fixed_code(int s) {
    if (s < 144) return 0x30 + s;
    if (s < 256) return 0x190 + (s - 144);
    if (s < 280) return s - 256;
    return 0xc0 + (s - 280);
}
static uint32_t adler(const uint8_t *p, size_t n) {
    uint32_t a = 1, b = 0;
    for (size_t i = 0; i < n; ++i) { a = (a + p[i]) % 65521; b = (b + a) % 65521; }
    return (b << 16) | a;
}
static void emit(const uint8_t *src, const uint8_t *raw, size_t n) {
    uint8_t dec[4096];
    size_t decsz = sizeof(dec);
    uint32_t a = adler(raw, n);
    if (ofs + 4 > (int)sizeof(out)) return;
    out[ofs++] = (uint8_t)(a >> 24); out[ofs++] = (uint8_t)(a >> 16);
    out[ofs++] = (uint8_t)(a >> 8); out[ofs++] = (uint8_t)a;
    if (exr_inflate_zlib(src, (size_t)ofs, dec, sizeof(dec), &decsz) != EXR_SUCCESS) return;
    for (int i = 0; i < ofs; ++i) printf("%02x", src[i]);
    putchar(' ');
    for (size_t i = 0; i < decsz; ++i) printf("%02x", dec[i]);
    putchar('\n');
}
static void begin(void) {
    ofs = 0; bits = 0; buf = 0;
    out[ofs++] = 0x78; out[ofs++] = 0x01;
}

int main(void) {
    /* stored blocks */
    {
        const uint8_t r1[] = "hello stored block";
        const uint8_t r2[] = {0, 1, 2, 3, 255, 128, 64, 0};
        const uint8_t *cases[2] = {r1, r2};
        size_t ns[2] = {sizeof(r1) - 1, sizeof(r2)};
        for (int k = 0; k < 2; ++k) {
            begin();
            putbits(1, 1); putbits(0, 2); /* BFINAL=1, BTYPE=00 */
            align();
            putbits((int)ns[k], 16);
            putbits((int)(~ns[k] & 0xffff), 16);
            for (size_t i = 0; i < ns[k]; ++i) putbits(cases[k][i], 8);
            align();
            emit(out, cases[k], ns[k]);
        }
    }
    /* fixed-Huffman literal-only block */
    {
        const uint8_t raw[] = "The quick brown fox jumps over the lazy dog";
        begin();
        putbits(1, 1); putbits(1, 2); /* BFINAL=1, BTYPE=01 */
        for (size_t i = 0; i < sizeof(raw) - 1; ++i) {
            int s = raw[i];
            putcode(fixed_code(s), fixed_len(s));
        }
        putcode(fixed_code(256), fixed_len(256));
        align();
        emit(out, raw, sizeof(raw) - 1);
    }
    /* fixed literals exercising the 9-bit symbol range (144..255) */
    {
        uint8_t raw[48];
        begin();
        putbits(1, 1); putbits(1, 2);
        for (int i = 0; i < 48; ++i) {
            raw[i] = (uint8_t)(144 + (i * 7) % 112);
            int sym = raw[i];
            putcode(fixed_code(sym), fixed_len(sym));
        }
        putcode(fixed_code(256), fixed_len(256));
        align();
        emit(out, raw, sizeof(raw));
    }
    /* two blocks: non-final stored, then final fixed */
    {
        const uint8_t r1[] = "PART1:";
        const uint8_t r2[] = "PART2!";
        uint8_t raw[12];
        memcpy(raw, r1, 6); memcpy(raw + 6, r2, 6);
        begin();
        putbits(0, 1); putbits(0, 2); /* BFINAL=0, stored */
        align();
        putbits(6, 16); putbits((int)(~6 & 0xffff), 16);
        for (int i = 0; i < 6; ++i) putbits(r1[i], 8);
        /* next block starts at current bit position (byte aligned after 6 bytes) */
        putbits(1, 1); putbits(1, 2);
        for (int i = 0; i < 6; ++i) {
            int sym = r2[i];
            putcode(fixed_code(sym), fixed_len(sym));
        }
        putcode(fixed_code(256), fixed_len(256));
        align();
        emit(out, raw, sizeof(raw));
    }
    /* fixed-Huffman block with an LZ77 match (length 21, distance 3) */
    {
        uint8_t raw[24];
        for (int i = 0; i < 24; ++i) raw[i] = (uint8_t)("abc"[i % 3]);
        begin();
        putbits(1, 1); putbits(1, 2);
        for (int i = 0; i < 3; ++i) putcode(fixed_code(raw[i]), fixed_len(raw[i]));
        putcode(fixed_code(269), fixed_len(269)); /* base 19 + 2 extra bits */
        putbits(2, 2);
        putcode(2, 5); /* distance code 2: base 3 */
        putcode(fixed_code(256), fixed_len(256));
        align();
        emit(out, raw, sizeof(raw));
    }
    /* dynamic-Huffman blocks produced by the real in-tree encoder */
    {
        static const char *texts[] = {
            "The quick brown fox jumps over the lazy dog, again and again",
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabcdefghijk",
            "0123456789012345678901234567890123456789abcdefghijklmnopqrstuvwxyz"
        };
        const exr_allocator *a = exr_default_allocator();
        for (int k = 0; k < 3; ++k) {
            const uint8_t *raw = (const uint8_t *)texts[k];
            size_t n = strlen(texts[k]);
            uint8_t *comp = NULL;
            size_t cs = 0;
            if (exr_deflate_zlib(a, raw, n, &comp, &cs) != EXR_SUCCESS || cs < 3) continue;
            if (((comp[2] >> 1) & 3) != 2) { free(comp); continue; } /* need BTYPE=2 */
            for (size_t i = 0; i < cs; ++i) printf("%02x", comp[i]);
            putchar(' ');
            for (size_t i = 0; i < n; ++i) printf("%02x", raw[i]);
            putchar('\n');
            free(comp);
        }
    }
    return 0;
}
