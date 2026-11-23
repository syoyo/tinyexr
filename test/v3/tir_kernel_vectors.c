/*
 * tir - emit scalar-kernel vectors for the Lean differential gate.
 *
 * Each line is a self-contained kernel call: inputs as f32 bit patterns (or
 * integer/half values) followed by the C kernel's output bit patterns.
 * The Lean checker replays `Tir.Kernels` and compares bits exactly.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "tir_internal.h"

static uint32_t st = 0x9e3779b9u;
static uint32_t rnd(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return st;
}
static float finite_f32(void) {
    uint32_t b = rnd() & 0xffffffu; /* keep exponent away from all-ones */
    float f;
    memcpy(&f, &b, 4);
    return f;
}
static void pf(float f) { uint32_t b; memcpy(&b, &f, 4); printf("%08x ", b); }

int main(void) {
    int i, k;
    for (i = 0; i < 256; ++i) {
        /* hdot with 1..4 channels and a nonzero start offset */
        float src[64], w[8], out[4];
        int32_t start, count;
        int wc = 1 + (int)(rnd() % 4), nblk, t, c;
        count = 1 + (int)(rnd() % 5);
        start = (int)(rnd() % 4);
        nblk = (count + 3) & ~3;
        for (t = 0; t < (start + nblk + 2) * wc; ++t) src[t] = finite_f32();
        for (t = 0; t < 8; ++t) w[t] = (t < count) ? finite_f32() : 0.0f;
        memset(out, 0, sizeof(out));
        if (wc == 1) tir__h_dot1_sc(out, src, &start, &count, w, 8, 0, 1);
        if (wc == 2) tir__h_dot2_sc(out, src, &start, &count, w, 8, 0, 1);
        if (wc == 3) tir__h_dot3_sc(out, src, &start, &count, w, 8, 0, 1);
        if (wc == 4) tir__h_dot4_sc(out, src, &start, &count, w, 8, 0, 1);
        printf("hdot %d %d %d ", wc, start, count);
        for (t = 0; t < (start + nblk + 2) * wc; ++t) pf(src[t]);
        for (t = 0; t < 8; ++t) pf(w[t]);
        for (c = 0; c < wc; ++c) pf(out[c]);
        putchar('\n');

        /* sequential weighted sum (vertical pass) */
        {
            float wv[8], rows[16], o = 0.0f;
            int n = 1 + (int)(rnd() % 6), cc = (int)(rnd() % 3);
            for (k = 0; k < n; ++k) wv[k] = finite_f32();
            for (k = 0; k < n + cc + 2; ++k) rows[k] = finite_f32();
            for (k = 0; k < n; ++k) o += wv[k] * rows[k + cc];
            printf("vweighted %d %d ", n, cc);
            for (k = 0; k < n; ++k) pf(wv[k]);
            for (k = 0; k < n + cc + 2; ++k) pf(rows[k]);
            pf(o); putchar('\n');
        }

        /* min/max scan (1 channel) */
        {
            float src[8], mn, mx;
            int32_t start = (int)(rnd() % 3), count = 1 + (int)(rnd() % 5);
            for (k = 0; k < count + 2; ++k) src[k] = finite_f32();
            tir__h_minmax_sc(&mn, &mx, src, &start, &count, 0, 1, 1);
            printf("minmax %d %d ", start, count);
            for (k = 0; k < count + 2; ++k) pf(src[k]);
            pf(mn); pf(mx); putchar('\n');
        }

        /* anti-ring / clamp */
        {
            float v = finite_f32(), mn = finite_f32(), mx = finite_f32();
            float s = (float)(rnd() % 1001) / 1000.0f, o;
            if (mn > mx) { float t = mn; mn = mx; mx = t; }
            o = v;
            tir__antiring_apply_sc(&o, &mn, &mx, s, 1);
            printf("anti "); pf(v); pf(mn); pf(mx); pf(s); pf(o); putchar('\n');
            { float lo = finite_f32(), hi = finite_f32(), oc;
              if (lo > hi) { float t = lo; lo = hi; hi = t; }
              oc = v;
              tir__clamp_range_sc(&oc, lo, hi, 1);
              printf("clamp "); pf(v); pf(lo); pf(hi); pf(oc); putchar('\n'); }
        }

        /* normal renormalisation */
        {
            float xyz[3], in[3];
            for (k = 0; k < 3; ++k) xyz[k] = in[k] = finite_f32();
            tir__normalize3_sc(xyz, NULL, 1);
            printf("norm3 ");
            for (k = 0; k < 3; ++k) pf(in[k]);
            for (k = 0; k < 3; ++k) pf(xyz[k]);
            putchar('\n');
        }

        /* premultiply / unpremultiply */
        {
            float a[4], o[4];
            for (k = 0; k < 4; ++k) a[k] = finite_f32();
            memcpy(o, a, sizeof(o)); tir__premult4_sc(o, 1);
            printf("premul "); for (k = 0; k < 4; ++k) pf(a[k]);
            for (k = 0; k < 4; ++k) pf(o[k]);
            putchar('\n');
            memcpy(o, a, sizeof(o)); tir__unpremult4_sc(o, 1);
            printf("unpremul "); for (k = 0; k < 4; ++k) pf(a[k]);
            for (k = 0; k < 4; ++k) pf(o[k]);
            putchar('\n');
        }

        /* highlight range compress / expand */
        {
            float x = finite_f32(), o;
            o = tir__rangecompress(x);
            printf("rc "); pf(x); pf(o); putchar('\n');
            o = tir__rangeexpand(x);
            printf("re "); pf(x); pf(o); putchar('\n');
        }

        /* pixel conversions */
        {
            uint16_t h = (uint16_t)rnd(), oh;
            float f;
            tir__f16_to_f32_sc(&f, &h, 1);
            printf("f16to32 %04x ", h); pf(f); putchar('\n');
            f = finite_f32();
            tir__f32_to_f16_sc(&oh, &f, 1);
            printf("f32to16 "); pf(f); printf("%04x\n", oh);
        }
        {
            uint8_t u = (uint8_t)rnd(), ou8;
            uint16_t ou16;
            float f;
            tir__u8_to_f32_sc(&f, &u, 1);
            printf("u8to32 %u ", u); pf(f); putchar('\n');
            f = finite_f32();
            tir__f32_to_u8_sc(&ou8, &f, 1);
            printf("f32tou8 "); pf(f); printf("%u\n", ou8);
            { uint16_t v = (uint16_t)rnd();
              tir__u16_to_f32_sc(&f, &v, 1);
              printf("u16to32 %u ", v); pf(f); putchar('\n'); }
            f = finite_f32();
            tir__f32_to_u16_sc(&ou16, &f, 1);
            printf("f32tou16 "); pf(f); printf("%u\n", ou16);
        }
    }
    return 0;
}
