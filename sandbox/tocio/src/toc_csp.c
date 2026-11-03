/*
 * tocio - Cinespace / Rising Sun Research CSP LUT loader (.csp, "CSPLUTV100").
 *
 * Follows OpenColorIO's FileFormatCSP reader:
 *
 *   CSPLUTV100
 *   1D | 3D
 *   [BEGIN METADATA ... END METADATA]
 *   <R prelut: count, then `count` input values, then `count` output values>
 *   <G prelut>  <B prelut>          (count < 2 = identity channel)
 *   1D: <n> then n lines "r g b"
 *   3D: <n n n> then n^3 lines "r g b", red fastest
 *
 * Blank lines are ignored. A non-identity prelut becomes, as in OCIO, a
 * per-channel scale/offset mapping [first input, last input] to [0,1] (no
 * clamp) followed by a 65536-entry linear LUT1D sampled from the prelut's
 * cubic spline (the Rising Sun interpolator, ported below).
 *
 * Reimplemented from the OpenColorIO CSP file format (BSD-3-Clause).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "toc_internal.h"

#define CSP_PRELUT_SAMPLES 65536 /* OCIO NUM_PRELUT_SAMPLES */
#define CSP_MAX_1D (1 << 20)     /* OCIO Max1DLUTLength */
#define CSP_MAX_3D 129           /* OCIO Max3DLUTLength */
#define CSP_MAX_PRELUT 65536

/* ---- line reader ---------------------------------------------------------- */

typedef struct {
    const char *p, *end;
} csp_cur;

static int csp_ws(char c) { return c == ' ' || c == '\t' || c == '\r'; }

/* Next non-blank line, trimmed: [*ls, *le). Returns 0 at end of input. */
static int csp_line(csp_cur *c, const char **ls, const char **le) {
    while (c->p < c->end) {
        const char *s = c->p, *e;
        while (c->p < c->end && *c->p != '\n') ++c->p;
        e = c->p;
        if (c->p < c->end) ++c->p; /* newline */
        while (s < e && (csp_ws(*s) || *s == '\v' || *s == '\f')) ++s;
        while (e > s && (csp_ws(e[-1]) || e[-1] == '\v' || e[-1] == '\f')) --e;
        if (s < e) { *ls = s; *le = e; return 1; }
    }
    return 0;
}

/* Case-insensitive prefix test on a trimmed line. */
static int csp_starts(const char *s, const char *e, const char *pre) {
    for (; *pre; ++pre, ++s) {
        char a, b = *pre;
        if (s >= e) return 0;
        a = *s;
        if (a >= 'a' && a <= 'z') a = (char)(a - 32);
        if (a != b) return 0;
    }
    return 1;
}

/* Parse exactly `want` numbers from [s,e) (whole line, nothing left over). */
static int csp_floats(const char *s, const char *e, float *out, int want) {
    int n = 0;
    while (n < want) {
        if (!toc_parse_float(&s, e, &out[n])) return 0;
        ++n;
    }
    while (s < e && csp_ws(*s)) ++s;
    return s == e;
}

static int csp_ints(const char *s, const char *e, long *out, int want) {
    int n = 0;
    while (n < want) {
        if (!toc_parse_int(&s, e, &out[n])) return 0;
        ++n;
    }
    while (s < e && csp_ws(*s)) ++s;
    return s == e;
}

/* ---- Rising Sun cubic prelut interpolator (OCIO rsr_Interpolator1D) ------- */

typedef struct {
    int n;
    const float *stims;
    float *params; /* 5*(n-1): 1/delta, a, b, c, d */
    float minv, maxv;
} csp_spline;

static int csp_spline_build(csp_spline *sp, const float *st, const float *va,
                            int n, float *params) {
    int i;
    sp->n = n;
    sp->stims = st;
    sp->params = params;
    sp->minv = va[0];
    sp->maxv = va[n - 1];
    for (i = 0; i + 1 < n; ++i)
        if (!(st[i + 1] > st[i])) return 0; /* inputs must strictly increase */
    if (n == 2) {
        params[0] = 1.0f / (st[1] - st[0]);
        params[1] = va[0];
        params[2] = va[1] - va[0];
        params[3] = 0.0f;
        params[4] = 0.0f;
        return 1;
    }
    for (i = 0; i < n - 1; ++i) {
        float f0 = va[i], f1 = va[i + 1], *p = params + 5 * i;
        float delta = st[i + 1] - st[i];
        p[0] = 1.0f / delta;
        if (i == 0) {
            float delta2 = (st[i + 2] - st[i + 1]) / delta;
            float dfdx1 = (va[i + 2] - f0) / (1.0f + delta2);
            p[1] = f0;
            p[2] = -2.0f * f0 + 2.0f * f1 - dfdx1;
            p[3] = f0 - f1 + dfdx1;
            p[4] = 0.0f;
        } else if (i == n - 2) {
            float delta1 = (st[i] - st[i - 1]) / delta;
            float dfdx0 = (f1 - va[i - 1]) / (1.0f + delta1);
            p[1] = f0;
            p[2] = dfdx0;
            p[3] = -f0 + f1 - dfdx0;
            p[4] = 0.0f;
        } else {
            float delta1 = (st[i] - st[i - 1]) / delta;
            float delta2 = (st[i + 2] - st[i + 1]) / delta;
            float dfdx0 = (f1 - va[i - 1]) / (1.0f + delta1);
            float dfdx1 = (va[i + 2] - f0) / (1.0f + delta2);
            p[1] = f0;
            p[2] = dfdx0;
            p[3] = -3.0f * f0 - 2.0f * dfdx0 + 3.0f * f1 - dfdx1;
            p[4] = 2.0f * f0 + dfdx0 - 2.0f * f1 + dfdx1;
        }
    }
    return 1;
}

static float csp_spline_eval(const csp_spline *sp, float x) {
    int lo = 0, hi = sp->n - 1;
    const float *p;
    float z;
    if (x != x) return x;
    if (x < sp->stims[0]) return sp->minv;
    if (x > sp->stims[sp->n - 1]) return sp->maxv;
    while (hi - lo > 1) { /* segment containing x (iterative refineSegment) */
        int mid = (lo + hi) / 2;
        if (x < sp->stims[mid]) hi = mid; else lo = mid;
    }
    p = sp->params + 5 * lo;
    z = (x - sp->stims[lo]) * p[0];
    return p[1] + z * (p[2] + z * (p[3] + p[4] * z));
}

/* OCIO EqualWithRelError over the whole prelut. */
static int csp_identity(const float *in, const float *out, int n) {
    int i;
    for (i = 0; i < n; ++i) {
        float d = in[i] > out[i] ? in[i] - out[i] : out[i] - in[i];
        float m = in[i] > 0.0f ? in[i] : -in[i];
        if (!(d <= 1e-6f * m)) return 0;
    }
    return 1;
}

/* ---- loader --------------------------------------------------------------- */

toc_result toc_load_csp(toc_op_list *list, const char *data, size_t len) {
    csp_cur c;
    const char *ls = NULL, *le = NULL;
    float *pin[3] = {NULL, NULL, NULL}, *pout[3] = {NULL, NULL, NULL};
    int pn[3] = {0, 0, 0}, use_pre = 0, is3d, ch;
    float *lut = NULL, *pre = NULL, *params = NULL;
    long n1 = 0;
    toc_result rc = TOC_ERROR_PARSE;

    c.p = data;
    c.end = data + len;
    if (!csp_line(&c, &ls, &le) || !csp_starts(ls, le, "CSPLUTV100"))
        return TOC_ERROR_PARSE;
    if (!csp_line(&c, &ls, &le)) return TOC_ERROR_PARSE;
    if (csp_starts(ls, le, "3D")) is3d = 1;
    else if (csp_starts(ls, le, "1D")) is3d = 0;
    else return TOC_ERROR_UNSUPPORTED;

    if (!csp_line(&c, &ls, &le)) return TOC_ERROR_PARSE;
    if (csp_starts(ls, le, "BEGIN METADATA")) {
        do {
            if (!csp_line(&c, &ls, &le)) return TOC_ERROR_PARSE;
        } while (!csp_starts(ls, le, "END METADATA"));
        if (!csp_line(&c, &ls, &le)) return TOC_ERROR_PARSE;
    }

    /* preluts: the count line for channel 0 is already in [ls, le) */
    for (ch = 0; ch < 3; ++ch) {
        long cnt;
        if (ch > 0 && !csp_line(&c, &ls, &le)) goto fail;
        if (!csp_ints(ls, le, &cnt, 1) || cnt < 0 || cnt > CSP_MAX_PRELUT) goto fail;
        if (cnt >= 2) {
            const char *s2, *e2;
            if (!toc_values_fit((size_t)cnt * 2, ls, c.end)) goto fail;
            pin[ch] = (float *)toc_malloc(&list->alloc, (size_t)cnt * sizeof(float));
            pout[ch] = (float *)toc_malloc(&list->alloc, (size_t)cnt * sizeof(float));
            if (!pin[ch] || !pout[ch]) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
            if (!csp_line(&c, &s2, &e2) || !csp_floats(s2, e2, pin[ch], (int)cnt) ||
                !csp_line(&c, &s2, &e2) || !csp_floats(s2, e2, pout[ch], (int)cnt))
                goto fail;
            pn[ch] = (int)cnt;
            if (!csp_identity(pin[ch], pout[ch], pn[ch])) use_pre = 1;
        }
    }

    /* LUT body */
    if (!csp_line(&c, &ls, &le)) goto fail;
    if (is3d) {
        long dims[3];
        size_t n3, i;
        if (!csp_ints(ls, le, dims, 3) || dims[0] != dims[1] || dims[0] != dims[2] ||
            dims[0] < 2 || dims[0] > CSP_MAX_3D)
            goto fail;
        n1 = dims[0];
        n3 = (size_t)n1 * (size_t)n1 * (size_t)n1;
        if (!toc_values_fit(n3 * 3, c.p, c.end)) goto fail;
        lut = (float *)toc_malloc(&list->alloc, n3 * 3 * sizeof(float));
        if (!lut) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        /* CSP is red fastest, which is tocio's LUT3D layout ((b*N+g)*N+r) */
        for (i = 0; i < n3; ++i)
            if (!csp_line(&c, &ls, &le) || !csp_floats(ls, le, lut + i * 3, 3)) goto fail;
    } else {
        long i;
        if (!csp_ints(ls, le, &n1, 1) || n1 < 2 || n1 > CSP_MAX_1D) goto fail;
        if (!toc_values_fit((size_t)n1 * 3, c.p, c.end)) goto fail;
        lut = (float *)toc_malloc(&list->alloc, (size_t)n1 * 3 * sizeof(float));
        if (!lut) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        for (i = 0; i < n1; ++i)
            if (!csp_line(&c, &ls, &le) || !csp_floats(ls, le, lut + (size_t)i * 3, 3))
                goto fail;
    }

    /* prelut: [min,max] -> [0,1] scale/offset, then a resampled LUT1D */
    if (use_pre) {
        float lo[3], hi[3];
        toc_op *op;
        int i;
        pre = (float *)toc_malloc(&list->alloc,
                                  (size_t)CSP_PRELUT_SAMPLES * 3 * sizeof(float));
        params = (float *)toc_malloc(&list->alloc,
                                     (size_t)5 * CSP_MAX_PRELUT * sizeof(float));
        if (!pre || !params) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        for (ch = 0; ch < 3; ++ch) {
            static const float ident[2] = {0.0f, 1.0f};
            const float *st = pn[ch] ? pin[ch] : ident;
            const float *va = pn[ch] ? pout[ch] : ident;
            int n = pn[ch] ? pn[ch] : 2;
            csp_spline sp;
            if (!csp_spline_build(&sp, st, va, n, params)) goto fail;
            lo[ch] = st[0];
            hi[ch] = st[n - 1];
            for (i = 0; i < CSP_PRELUT_SAMPLES; ++i) {
                float t = (float)i / (float)(CSP_PRELUT_SAMPLES - 1);
                pre[(size_t)i * 3 + ch] = csp_spline_eval(&sp, (hi[ch] - lo[ch]) * t + lo[ch]);
            }
        }
        toc_free(&list->alloc, params);
        params = NULL;
        op = toc_op_list_push(list, TOC_OP_MATRIX);
        if (!op) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        memset(op->u.matrix.m, 0, sizeof(op->u.matrix.m));
        memset(op->u.matrix.off, 0, sizeof(op->u.matrix.off));
        for (ch = 0; ch < 3; ++ch) {
            float s = 1.0f / (hi[ch] - lo[ch]);
            op->u.matrix.m[ch * 4 + ch] = s;
            op->u.matrix.off[ch] = -lo[ch] * s;
        }
        op->u.matrix.m[15] = 1.0f;
        if (!toc_op_list_own(list, pre)) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        op = toc_op_list_push(list, TOC_OP_LUT1D);
        if (!op) { pre = NULL; rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        op->u.lut1d.length = CSP_PRELUT_SAMPLES;
        op->u.lut1d.channels = 3;
        op->u.lut1d.domain_min = 0.0f;
        op->u.lut1d.domain_max = 1.0f;
        op->u.lut1d.data = pre;
        op->u.lut1d.interp = TOC_INTERP_LINEAR;
        pre = NULL; /* owned by the list */
    }

    if (!toc_op_list_own(list, lut)) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
    {
        float *owned = lut;
        toc_op *op = toc_op_list_push(list, is3d ? TOC_OP_LUT3D : TOC_OP_LUT1D);
        lut = NULL; /* owned by the list */
        if (!op) { rc = TOC_ERROR_OUT_OF_MEMORY; goto fail; }
        if (is3d) {
            op->u.lut3d.size = (int)n1;
            op->u.lut3d.domain_min[0] = op->u.lut3d.domain_min[1] =
                op->u.lut3d.domain_min[2] = 0.0f;
            op->u.lut3d.domain_max[0] = op->u.lut3d.domain_max[1] =
                op->u.lut3d.domain_max[2] = 1.0f;
            op->u.lut3d.data = owned;
            op->u.lut3d.interp = TOC_INTERP_TRILINEAR; /* OCIO default */
        } else {
            op->u.lut1d.length = (int)n1;
            op->u.lut1d.channels = 3;
            op->u.lut1d.domain_min = 0.0f;
            op->u.lut1d.domain_max = 1.0f;
            op->u.lut1d.data = owned;
            op->u.lut1d.interp = TOC_INTERP_LINEAR;
        }
    }
    rc = TOC_SUCCESS;

fail:
    for (ch = 0; ch < 3; ++ch) {
        toc_free(&list->alloc, pin[ch]);
        toc_free(&list->alloc, pout[ch]);
    }
    toc_free(&list->alloc, params);
    toc_free(&list->alloc, pre);
    toc_free(&list->alloc, lut);
    return rc;
}
