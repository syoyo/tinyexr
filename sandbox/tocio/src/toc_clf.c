/*
 * tocio - CLF (Common LUT Format) loader: ACES-standard XML LUT format.
 *
 * Parses the XML-based Common LUT Format (SMPTE ST 2065-4 / Academy standard)
 * into a flat op list.  Supports Matrix, Range, Exponent, Log, LUT1D, LUT3D,
 * and Reference process nodes.  Does NOT build a DOM tree — single-pass
 * streaming parser using a minimal XML subset reader.
 *
 * Reimplemented from the Academy CLF reference (BSD-3-Clause compatible).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "toc_internal.h"

/* ============================================================================
 * Minimal XML subset reader
 *
 * Flat cursor-based parser — no tree.  CLF nesting never exceeds 2 levels so
 * this is sufficient.  Supports: <tag>, key="val", <!-- comment -->, <?xml?>,
 * self-close, </close>.
 * ========================================================================== */

typedef struct {
    const char *p, *end;
} xr;

/* skip whitespace + XML comments + processing instructions */
static void xs(xr *r) {
    for (;;) {
        while (r->p < r->end && (unsigned char)*r->p <= 0x20) ++r->p;
        /* <!-- ... --> */
        if (r->p + 3 < r->end && r->p[0] == '<' && r->p[1] == '!' &&
            r->p[2] == '-' && r->p[3] == '-') {
            r->p += 4;
            while (r->p + 2 < r->end &&
                   !(r->p[0] == '-' && r->p[1] == '-' && r->p[2] == '>'))
                ++r->p;
            if (r->p + 2 < r->end) r->p += 3;
            continue;
        }
        /* <? ... ?> */
        if (r->p + 1 < r->end && r->p[0] == '<' && r->p[1] == '?') {
            r->p += 2;
            /* bounded pair test: data need not be NUL-terminated */
            while (r->p + 1 < r->end && !(r->p[0] == '?' && r->p[1] == '>'))
                ++r->p;
            r->p = (r->p + 1 < r->end) ? r->p + 2 : r->end;
            continue;
        }
        break;
    }
}

/* peek: is next char '<' after skipping? */
static int xat(xr *r) {
    xs(r);
    return r->p < r->end && *r->p == '<';
}

/* read tag name at current position (just after '<').  returns 1 for opening
 * tag, 0 for closing tag or no tag.  On success, buf gets the name and r->p
 * points just past the name (before attrs).  On closing tag, buf="/" and
 * r->p points at the name chars (after '/'). */
static int xtag(xr *r, char *buf, int sz) {
    int n = 0;
    /* Character data between elements (descriptions, stray text) carries
     * no op meaning here; value text is always read via xt() first. */
    xs(r);
    while (r->p < r->end && *r->p != '<') ++r->p;
    buf[0] = 0;
    if (!xat(r)) return 0;
    ++r->p; /* skip '<' */
    if (r->p >= r->end) return 0;
    if (*r->p == '/') {
        /* closing tag: consume '/' and read name into buf but return 0 */
        ++r->p;
        while (r->p < r->end && (unsigned char)*r->p > 0x20 && *r->p != '>' && n < sz - 1)
            buf[n++] = *r->p++;
        buf[n] = 0;
        return 0;
    }
    while (r->p < r->end && (unsigned char)*r->p > 0x20 && *r->p != '>' && *r->p != '/' &&
           n < sz - 1)
        buf[n++] = *r->p++;
    buf[n] = 0;
    return n > 0;
}

/* read next attribute key="val".  returns 1 if found, 0 before '>'/'/>'. */
static int xa(xr *r, char *key, int ksz, char *val, int vsz) {
    int n = 0;
    /* val is only filled for a quoted value: always leave it terminated so
     * callers never read an unset buffer (e.g. dim= with no quotes) */
    val[0] = 0;
    key[0] = 0;
    xs(r);
    if (r->p >= r->end || *r->p == '>' || *r->p == '/') return 0;
    /* compare as unsigned: high (non-ASCII) bytes are name characters, and a
     * signed char would stop the scan without consuming anything */
    while (r->p < r->end && *r->p != '=' && (unsigned char)*r->p > 0x20 &&
           n < ksz - 1)
        key[n++] = *r->p++;
    key[n] = 0;
    if (r->p < r->end && *r->p == '=') ++r->p;
    else if (n == 0) ++r->p; /* always make progress: callers loop on xa() */
    xs(r);
    if (r->p < r->end && (*r->p == '"' || *r->p == '\'')) {
        char q = *r->p++;
        n = 0;
        while (r->p < r->end && *r->p != q && n < vsz - 1) val[n++] = *r->p++;
        val[n] = 0;
        if (r->p < r->end) ++r->p;
    }
    return 1;
}

/* skip attributes and consume '>' (or '/>').  returns 1 if self-closing. */
static int xc(xr *r) {
    int selfc = 0;
    xs(r);
    while (r->p < r->end && *r->p != '>') {
        if (*r->p == '/') selfc = 1;
        ++r->p;
    }
    if (r->p < r->end) ++r->p; /* consume '>' */
    return selfc;
}

/* read text content (up to next '<').  sets *start / *end to span within source.
 * returns 1 if non-empty content exists. */
static int xt(xr *r, const char **start, const char **end) {
    xs(r);
    *start = r->p;
    while (r->p < r->end && *r->p != '<') ++r->p;
    *end = r->p;
    return *start < *end;
}

/* skip forward past the closing tag that follows (the `<` was already consumed
 * by xtag, positioning r->p at the name chars after `/`).  Returns 1 on
 * success, 0 if '>' was not found (truncated). */
static int xskip_close(xr *r) {
    while (r->p < r->end && *r->p != '>') ++r->p;
    if (r->p >= r->end) return 0;
    ++r->p;
    return 1;
}

/* Prefix test (the freestanding string shim has no n-limited compare). */
static int clf_prefix(const char *s, const char *pre) {
    while (*pre)
        if (*s++ != *pre++) return 0;
    return 1;
}

/* Skip the rest of an element whose opening tag name xtag just read: its
 * attributes, any text and child elements, and the matching close tag.
 * Without this an unknown child with text content (e.g. <Description>)
 * ended the parent's child loop early and the op was silently dropped. */
static void xskip_elem(xr *r, const char *tag) {
    size_t tl = strlen(tag);
    if (xc(r)) return; /* self-closing */
    while (r->p < r->end) {
        if (*r->p == '<' && r->p + 1 < r->end && r->p[1] == '/' &&
            (size_t)(r->end - r->p) >= tl + 2 && memcmp(r->p + 2, tag, tl) == 0 &&
            (r->p + 2 + tl == r->end || r->p[2 + tl] == '>' ||
             (unsigned char)r->p[2 + tl] <= 0x20)) {
            r->p += 2 + tl;
            xskip_close(r);
            return;
        }
        ++r->p;
    }
}

/* Largest code value of a CLF bit depth ("8i" .. "16i"; float depths are 1).
 * OCIO normalizes array values by these so the op works on [0,1] floats. */
static float clf_depth_scale(const char *v) {
    if (strcmp(v, "8i") == 0) return 255.0f;
    if (strcmp(v, "10i") == 0) return 1023.0f;
    if (strcmp(v, "12i") == 0) return 4095.0f;
    if (strcmp(v, "16i") == 0) return 65535.0f;
    return 1.0f; /* 16f, 32f, absent */
}

/* read space-separated floats from text content into arr; returns count. */
static int xfloats(xr *r, float *arr, int max) {
    const char *s, *e;
    int n = 0;
    /* values may be interrupted by XML comments; xt() skips them */
    while (n < max && xt(r, &s, &e)) {
        while (s < e && n < max) {
            float v;
            if (!toc_parse_float(&s, e, &v)) break; /* end of segment */
            arr[n++] = v;
        }
        while (s < e && (unsigned char)*s <= 0x20) ++s;
        if (s < e) return n; /* non-numeric text: stop (caller checks count) */
        if (!(r->p + 3 < r->end && r->p[0] == '<' && r->p[1] == '!' &&
              r->p[2] == '-' && r->p[3] == '-'))
            break;
    }
    return n;
}

/* ============================================================================
 * CLF process-node handlers.
 * Each is called with position just after > of the opening <tag> (attributes
 * consumed).  The handler reads children, creates an op, and returns with
 * r->p past the closing </tag>.
 * ========================================================================== */

/* Parse a dim="a b c d" attribute value into dims[] (at most 4). */
static int clf_dims(const char *val, int dims[4]) {
    const char *vp = val;
    int nd = 0;
    while (*vp && nd < 4) {
        long d;
        const char *before = vp;
        if (toc_parse_int(&vp, vp + strlen(vp), &d) && d > 0 && d <= (1L << 20))
            dims[nd++] = (int)d;
        while (*vp == ' ' || *vp == '\t' || *vp == '\n' || *vp == '\r') ++vp;
        if (vp == before) break; /* unparsable: no progress */
    }
    return nd;
}

/* --- <Matrix> ------------------------------------------------------------- */
static toc_result clf_matrix(toc_op_list *list, xr *r, float in_s, float out_s) {
    float m[16] = {1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1};
    float off[4] = {0,0,0,0};
    char tag[64];
    while (xtag(r, tag, sizeof(tag))) {
        if (strcmp(tag, "Array") == 0) {
            char key[64], val[64];
            int dims[4] = {0, 0, 0, 0}, nd = 0, rows = 0, cols = 0;
            while (xa(r, key, sizeof(key), val, sizeof(val)))
                if (strcmp(key, "dim") == 0) nd = clf_dims(val, dims);
            xc(r); /* consume > */
            /* Shapes OpenColorIO accepts: CLF v3 "R C" with 3x3, 3x4, 4x4,
             * 4x5 (last column = offset); legacy "3 3 3" and "4 4 3" (3x4). */
            if (nd == 2) { rows = dims[0]; cols = dims[1]; }
            else if (nd == 3 && dims[2] == 3 && dims[0] == dims[1]) {
                rows = 3; cols = dims[0];
            }
            if (!((rows == 3 && (cols == 3 || cols == 4)) ||
                  (rows == 4 && (cols == 4 || cols == 5))))
                return TOC_ERROR_UNSUPPORTED;
            {
                float buf[20];
                int nf = xfloats(r, buf, rows * cols), i, j;
                if (nf != rows * cols) return TOC_ERROR_PARSE;
                /* Array is row-major; tocio stores m column-major m[c*4+r]. */
                /* bit depths: out = M*in in code values, so normalize by
                 * in/out maxima (offsets by the out maximum), as OCIO does */
                for (i = 0; i < rows; ++i) {
                    for (j = 0; j < rows; ++j)
                        m[j * 4 + i] = buf[i * cols + j] * in_s / out_s;
                    if (cols > rows) off[i] = buf[i * cols + rows] / out_s;
                }
            }
            /* skip </Array> */
            if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/') xskip_close(r); }
        } else if (strcmp(tag, "Offset") == 0) {
            xc(r);
            xfloats(r, off, 4);
            if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/') xskip_close(r); }
        } else {
            xskip_elem(r, tag);
        }
    }
    /* consume </Matrix> (xtag already saw '<' + '/' + "Matrix") */
    if (!xskip_close(r)) return TOC_ERROR_PARSE;
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_MATRIX);
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        memcpy(op->u.matrix.m, m, sizeof(m));
        memcpy(op->u.matrix.off, off, sizeof(off));
    }
    return TOC_SUCCESS;
}

/* --- <Range> --------------------------------------------------------------- */
/* OCIO RangeOpData semantics on RGB (alpha untouched):
 *   both pairs : out = (in - minIn) * (maxOut-minOut)/(maxIn-minIn) + minOut,
 *                clamped to [minOut, maxOut] unless style="noClamp";
 *   min only   : out = max(in + (minOut - minIn), minOut);
 *   max only   : out = min(in + (maxOut - maxIn), maxOut). */
static toc_result clf_range(toc_op_list *list, xr *r, float in_s, float out_s,
                            int noclamp) {
    float min_in = 0.0f, max_in = 0.0f, min_out = 0.0f, max_out = 0.0f;
    int has_min_in = 0, has_max_in = 0, has_min_out = 0, has_max_out = 0;
    char tag[64];
    while (xtag(r, tag, sizeof(tag))) {
        float v = 0.0f;
        int got = 0;
        if (strcmp(tag, "minInValue") != 0 && strcmp(tag, "maxInValue") != 0 &&
            strcmp(tag, "minOutValue") != 0 && strcmp(tag, "maxOutValue") != 0) {
            xskip_elem(r, tag);
            continue;
        }
        if (xc(r)) return TOC_ERROR_PARSE;
        {
            const char *s, *e;
            if (xt(r, &s, &e)) got = toc_parse_float(&s, e, &v);
        }
        if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/') xskip_close(r); }
        if (!got) return TOC_ERROR_PARSE;
        if (tag[3] == 'I') v /= in_s; else v /= out_s; /* bit-depth normalize */
        if (strcmp(tag, "minInValue") == 0) { min_in = v; has_min_in = 1; }
        else if (strcmp(tag, "maxInValue") == 0) { max_in = v; has_max_in = 1; }
        else if (strcmp(tag, "minOutValue") == 0) { min_out = v; has_min_out = 1; }
        else { max_out = v; has_max_out = 1; }
    }
    if (!xskip_close(r)) return TOC_ERROR_PARSE;
    /* each pair is all-or-nothing, and at least one pair is required */
    if (has_min_in != has_min_out || has_max_in != has_max_out ||
        (!has_min_in && !has_max_in))
        return TOC_ERROR_PARSE;
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_RANGE);
        float scale = 1.0f, offset;
        int i;
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        if (has_min_in && has_max_in) {
            if (!(max_in > min_in)) return TOC_ERROR_PARSE;
            scale = (max_out - min_out) / (max_in - min_in);
            offset = min_out - min_in * scale;
        } else if (has_min_in) {
            offset = min_out - min_in;
        } else {
            offset = max_out - max_in;
        }
        for (i = 0; i < 3; ++i) {
            op->u.range.scale[i] = scale;
            op->u.range.offset[i] = offset;
            op->u.range.min[i] = has_min_out ? min_out : -3.4e38f;
            op->u.range.max[i] = has_max_out ? max_out : 3.4e38f;
        }
        op->u.range.scale[3] = 1.0f; /* alpha passes through */
        op->u.range.offset[3] = 0.0f;
        op->u.range.min[3] = -3.4e38f;
        op->u.range.max[3] = 3.4e38f;
        /* noClamp only applies when both pairs define a full mapping */
        op->u.range.clamp_lo = !(noclamp && has_min_in && has_max_in);
        op->u.range.clamp_hi = op->u.range.clamp_lo;
    }
    return TOC_SUCCESS;
}

/* Per-channel parameter element (<ExponentParams>/<LogParams>): attributes
 * name="value", optional channel="R|G|B" (absent = all three channels). */
typedef struct {
    const char *name;
    float v[3];
    int set;
} clf_param;

static void clf_read_params(xr *r, const char *tag, clf_param *p, int np) {
    char key[64], val[64];
    float tmp[16];
    int has[16], i, ch = -1;
    for (i = 0; i < np && i < 16; ++i) has[i] = 0;
    while (xa(r, key, sizeof(key), val, sizeof(val))) {
        if (strcmp(key, "channel") == 0) {
            ch = val[0] == 'R' ? 0 : val[0] == 'G' ? 1 : val[0] == 'B' ? 2 : -2;
            continue;
        }
        for (i = 0; i < np && i < 16; ++i)
            if (strcmp(key, p[i].name) == 0) {
                const char *vp = val;
                has[i] = toc_parse_float(&vp, vp + strlen(vp), &tmp[i]);
            }
    }
    xskip_elem(r, tag);
    if (ch == -2) return; /* e.g. channel="A": not an RGB parameter */
    for (i = 0; i < np && i < 16; ++i) {
        int c;
        if (!has[i]) continue;
        for (c = 0; c < 3; ++c)
            if (ch < 0 || ch == c) p[i].v[c] = tmp[i];
        p[i].set = 1;
    }
}

/* --- <Exponent> ------------------------------------------------------------ */
/* CLF v3 / OCIO GammaOpData styles: basic{,Mirror}{Fwd,Rev} and
 * monCurve{,Mirror}{Fwd,Rev}. basicPassThru* has no tocio op: UNSUPPORTED. */
static toc_result clf_exponent(toc_op_list *list, xr *r, const char *style) {
    clf_param p[2] = {{"exponent", {1, 1, 1}, 0}, {"offset", {0, 0, 0}, 0}};
    int mon = 0, mirror = 0, rev = 0, i;
    char tag[64];
    if (clf_prefix(style, "monCurve")) { mon = 1; style += 8; }
    else if (clf_prefix(style, "basic")) style += 5;
    else return TOC_ERROR_UNSUPPORTED;
    if (clf_prefix(style, "Mirror")) { mirror = 1; style += 6; }
    if (strcmp(style, "Rev") == 0) rev = 1;
    else if (strcmp(style, "Fwd") != 0) return TOC_ERROR_UNSUPPORTED;
    while (xtag(r, tag, sizeof(tag))) {
        if (strcmp(tag, "ExponentParams") == 0) clf_read_params(r, tag, p, 2);
        else xskip_elem(r, tag);
    }
    if (!xskip_close(r)) return TOC_ERROR_PARSE;
    if (!p[0].set) return TOC_ERROR_PARSE;
    if (mon) {
        float g[4], o[4];
        for (i = 0; i < 3; ++i) { g[i] = p[0].v[i]; o[i] = p[1].v[i]; }
        g[3] = 1.0f; o[3] = 0.0f;
        if (!p[1].set) return TOC_ERROR_PARSE; /* monCurve needs an offset */
        return toc_push_exp_linear(list, g, o, rev, mirror);
    }
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_EXPONENT);
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        for (i = 0; i < 3; ++i) {
            float e = p[0].v[i];
            op->u.exponent.e[i] = rev ? (e != 0.0f ? 1.0f / e : 1.0f) : e;
        }
        op->u.exponent.e[3] = 1.0f; /* alpha untouched */
        op->u.exponent.mirror = mirror;
    }
    return TOC_SUCCESS;
}

/* --- <Log> ----------------------------------------------------------------- */
/* CLF v3 styles: log10, log2, antiLog10, antiLog2, linToLog, logToLin,
 * cameraLinToLog, cameraLogToLin (LogParams attributes). */
static toc_result clf_log(toc_op_list *list, xr *r, const char *style,
                          int empty) {
    clf_param p[7] = {{"base", {2, 2, 2}, 0},          {"logSideSlope", {1, 1, 1}, 0},
                      {"logSideOffset", {0, 0, 0}, 0}, {"linSideSlope", {1, 1, 1}, 0},
                      {"linSideOffset", {0, 0, 0}, 0}, {"linSideBreak", {0, 0, 0}, 0},
                      {"linearSlope", {0, 0, 0}, 0}};
    int inverse = 0, camera = 0, simple = 0, i;
    float base = 2.0f;
    char tag[64];
    if (strcmp(style, "log10") == 0) { simple = 1; base = 10.0f; }
    else if (strcmp(style, "log2") == 0) { simple = 1; }
    else if (strcmp(style, "antiLog10") == 0) { simple = 1; base = 10.0f; inverse = 1; }
    else if (strcmp(style, "antiLog2") == 0) { simple = 1; inverse = 1; }
    else if (strcmp(style, "linToLog") == 0) { }
    else if (strcmp(style, "logToLin") == 0) { inverse = 1; }
    else if (strcmp(style, "cameraLinToLog") == 0) { camera = 1; }
    else if (strcmp(style, "cameraLogToLin") == 0) { camera = 1; inverse = 1; }
    else return TOC_ERROR_UNSUPPORTED;
    if (!empty) { /* <Log style="log10"/> needs no LogParams */
        while (xtag(r, tag, sizeof(tag))) {
            if (strcmp(tag, "LogParams") == 0) clf_read_params(r, tag, p, 7);
            else xskip_elem(r, tag);
        }
        if (!xskip_close(r)) return TOC_ERROR_PARSE;
    }
    if (!simple) {
        /* one base for all channels (OCIO stores a single base) */
        base = p[0].v[0];
        if (!(base > 0.0f) || base == 1.0f) return TOC_ERROR_PARSE;
    }
    if (camera) {
        if (!p[5].set) return TOC_ERROR_PARSE; /* linSideBreak required */
        return toc_push_logcam(list, base, p[1].v, p[2].v, p[3].v, p[4].v, p[5].v,
                               p[6].set ? p[6].v : NULL, inverse);
    }
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_LOG);
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        op->u.log.base = base;
        op->u.log.inverse = inverse;
        for (i = 0; i < 3; ++i) {
            op->u.log.log_slope[i] = simple ? 1.0f : p[1].v[i];
            op->u.log.log_offset[i] = simple ? 0.0f : p[2].v[i];
            op->u.log.lin_slope[i] = simple ? 1.0f : p[3].v[i];
            op->u.log.lin_offset[i] = simple ? 0.0f : p[4].v[i];
        }
    }
    return TOC_SUCCESS;
}

/* --- <ASC_CDL> ------------------------------------------------------------- */
/* style Fwd (default) | Rev | FwdNoClamp | RevNoClamp; SOPNode Slope/Offset/
 * Power and SatNode Saturation, each optional with identity defaults. */
static toc_result clf_cdl(toc_op_list *list, xr *r, const char *style) {
    float sl[3] = {1, 1, 1}, of[3] = {0, 0, 0}, pw[3] = {1, 1, 1}, sat = 1.0f;
    int inverse, clamp_val;
    char tag[64];
    if (!style[0] || strcmp(style, "Fwd") == 0) { inverse = 0; clamp_val = 1; }
    else if (strcmp(style, "Rev") == 0) { inverse = 1; clamp_val = 1; }
    else if (strcmp(style, "FwdNoClamp") == 0) { inverse = 0; clamp_val = 0; }
    else if (strcmp(style, "RevNoClamp") == 0) { inverse = 1; clamp_val = 0; }
    else return TOC_ERROR_UNSUPPORTED;
    while (xtag(r, tag, sizeof(tag))) {
        if (strcmp(tag, "SOPNode") == 0 || strcmp(tag, "SatNode") == 0) {
            char t2[64];
            if (xc(r)) continue;
            while (xtag(r, t2, sizeof(t2))) {
                float *dst = strcmp(t2, "Slope") == 0 ? sl
                           : strcmp(t2, "Offset") == 0 ? of
                           : strcmp(t2, "Power") == 0 ? pw
                           : strcmp(t2, "Saturation") == 0 ? &sat : NULL;
                int want = dst == &sat ? 1 : 3;
                if (!dst) { xskip_elem(r, t2); continue; }
                if (xc(r)) return TOC_ERROR_PARSE;
                if (xfloats(r, dst, want) != want) return TOC_ERROR_PARSE;
                if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/') xskip_close(r); }
            }
            xskip_close(r); /* </SOPNode> / </SatNode> */
        } else {
            xskip_elem(r, tag);
        }
    }
    if (!xskip_close(r)) return TOC_ERROR_PARSE;
    return toc_push_cdl(list, sl, of, pw, sat, clamp_val, inverse);
}

/* --- <LUT1D> --------------------------------------------------------------- */
static toc_result clf_lut1d(toc_op_list *list, xr *r, float out_s) {
    int length = 0, channels = 3;
    float *data = NULL;
    char tag[64];
    while (xtag(r, tag, sizeof(tag))) {
        if (strcmp(tag, "Array") == 0) {
            char key[64], val[64];
            int dims[4] = {0,0,0,0}, nd = 0;
            while (xa(r, key, sizeof(key), val, sizeof(val)))
                if (strcmp(key, "dim") == 0) nd = clf_dims(val, dims);
            xc(r);
            if (data) goto parse_fail; /* one Array per LUT1D */
            /* CLF: dim="length components", components 1 or 3 (as OCIO). */
            if (nd != 2) return TOC_ERROR_UNSUPPORTED;
            length = dims[0];
            channels = dims[1];
            if ((channels != 1 && channels != 3) || length < 2 || length > (1 << 20))
                return TOC_ERROR_PARSE;
            if (length < 2 ||
                !toc_values_fit((size_t)length * (size_t)channels, r->p, r->end))
                return TOC_ERROR_PARSE;
            data = (float *)toc_malloc(&list->alloc,
                                       (size_t)length * 3 * sizeof(float));
            if (!data) return TOC_ERROR_OUT_OF_MEMORY;
            {
                float *tmp = (float *)toc_malloc(
                    &list->alloc, (size_t)length * channels * sizeof(float));
                int n;
                if (!tmp) { toc_free(&list->alloc, data); return TOC_ERROR_OUT_OF_MEMORY; }
                n = xfloats(r, tmp, length * channels);
                /* every channel of every entry must be present: the copy
                 * below reads all length*channels values */
                if (n != length * channels) {
                    toc_free(&list->alloc, tmp);
                    toc_free(&list->alloc, data);
                    return TOC_ERROR_PARSE;
                }
                /* LUT values are out-bit-depth code values */
                for (int i = 0; i < length; ++i) {
                    for (int c = 0; c < 3; ++c)
                        data[i * 3 + c] =
                            ((c < channels) ? tmp[i * channels + c]
                                            : tmp[i * channels + channels - 1]) / out_s;
                }
                toc_free(&list->alloc, tmp);
            }
            if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/')
                xskip_close(r); } /* </Array> */
        } else {
            xskip_elem(r, tag);
        }
    }
    if (!xskip_close(r)) goto parse_fail; /* </LUT1D> */
    if (!data) return TOC_ERROR_PARSE;
    if (!toc_op_list_own(list, data)) { toc_free(&list->alloc, data); return TOC_ERROR_OUT_OF_MEMORY; }
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_LUT1D);
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        op->u.lut1d.length = length;
        op->u.lut1d.channels = 3;
        op->u.lut1d.domain_min = 0.0f;
        op->u.lut1d.domain_max = 1.0f;
        op->u.lut1d.data = data;
        op->u.lut1d.interp = TOC_INTERP_LINEAR;
    }
    return TOC_SUCCESS;
parse_fail:
    toc_free(&list->alloc, data);
    return TOC_ERROR_PARSE;
}

/* --- <LUT3D> --------------------------------------------------------------- */
static toc_result clf_lut3d(toc_op_list *list, xr *r, int interp, float out_s) {
    int size = 0;
    float *data = NULL;
    char tag[64];
    while (xtag(r, tag, sizeof(tag))) {
        if (strcmp(tag, "Array") == 0) {
            char key[64], val[64];
            int dims[4] = {0,0,0,0}, nd = 0;
            while (xa(r, key, sizeof(key), val, sizeof(val)))
                if (strcmp(key, "dim") == 0) nd = clf_dims(val, dims);
            xc(r);
            if (data) goto parse_fail; /* one Array per LUT3D */
            /* CLF (SMPTE ST 2136-1 / Academy CLF v3): dim="N N N 3", as
             * OpenColorIO's CTF reader requires. */
            if (nd != 4 || dims[3] != 3) return TOC_ERROR_UNSUPPORTED;
            size = dims[0];
            if (dims[1] != size || dims[2] != size || size < 2 || size > 256 ||
                !toc_values_fit((size_t)size * size * size * 3, r->p, r->end))
                return TOC_ERROR_PARSE;
            {
                size_t n3 = (size_t)size * size * size, N = (size_t)size;
                size_t ir, ig, ib;
                int need = (int)(n3 * 3), got;
                /* CLF stores entries blue-fastest (red slowest); tocio's LUT3D
                 * layout is red-fastest ((b*N+g)*N+r), so transpose. */
                float *file = (float *)toc_malloc(&list->alloc, n3 * 3 * sizeof(float));
                if (!file) return TOC_ERROR_OUT_OF_MEMORY;
                got = xfloats(r, file, need);
                if (got != need) { toc_free(&list->alloc, file); return TOC_ERROR_PARSE; }
                data = (float *)toc_malloc(&list->alloc, n3 * 3 * sizeof(float));
                if (!data) { toc_free(&list->alloc, file); return TOC_ERROR_OUT_OF_MEMORY; }
                for (ir = 0; ir < N; ++ir)
                    for (ig = 0; ig < N; ++ig)
                        for (ib = 0; ib < N; ++ib) {
                            const float *src = file + ((ir * N + ig) * N + ib) * 3;
                            float *dst = data + ((ib * N + ig) * N + ir) * 3;
                            dst[0] = src[0] / out_s; dst[1] = src[1] / out_s;
                            dst[2] = src[2] / out_s;
                        }
                toc_free(&list->alloc, file);
            }
            if (xat(r)) { ++r->p; if (r->p < r->end && *r->p == '/')
                xskip_close(r); }
        } else {
            xskip_elem(r, tag);
        }
    }
    if (!xskip_close(r)) goto parse_fail; /* </LUT3D> */
    if (!data) return TOC_ERROR_PARSE;
    if (!toc_op_list_own(list, data)) { toc_free(&list->alloc, data); return TOC_ERROR_OUT_OF_MEMORY; }
    {
        toc_op *op = toc_op_list_push(list, TOC_OP_LUT3D);
        if (!op) return TOC_ERROR_OUT_OF_MEMORY;
        op->u.lut3d.size = size;
        op->u.lut3d.domain_min[0] = op->u.lut3d.domain_min[1] =
            op->u.lut3d.domain_min[2] = 0.0f;
        op->u.lut3d.domain_max[0] = op->u.lut3d.domain_max[1] =
            op->u.lut3d.domain_max[2] = 1.0f;
        op->u.lut3d.data = data;
        op->u.lut3d.interp = interp;
    }
    return TOC_SUCCESS;
parse_fail:
    toc_free(&list->alloc, data);
    return TOC_ERROR_PARSE;
}

/* ============================================================================
 * Top-level CLF entry point
 * ========================================================================== */

toc_result toc_load_clf(toc_op_list *list, const char *data, size_t len) {
    xr r;
    char tag[64], key[64], val[64];
    r.p = data;
    r.end = data + len;
    /* find <ProcessList> */
    while (xtag(&r, tag, sizeof(tag))) {
        if (strcmp(tag, "ProcessList") == 0) break;
        xc(&r); /* skip unknown top-level tags */
    }
    if (strcmp(tag, "ProcessList") != 0) return TOC_ERROR_PARSE;
    /* consume ProcessList attributes */
    while (xa(&r, key, sizeof(key), val, sizeof(val))) {}
    xc(&r); /* consume > */
    /* iterate process nodes */
    {
        size_t _maxit = len + 1;
        while (xtag(&r, tag, sizeof(tag)) && _maxit--) {
            toc_result rc = TOC_SUCCESS;
            if (strcmp(tag, "InputDescriptor") == 0 ||
                strcmp(tag, "OutputDescriptor") == 0 ||
                strcmp(tag, "Description") == 0) {
                xskip_elem(&r, tag);
                continue;
            }
            if (strcmp(tag, "ExposureContrast") == 0 ||
                strcmp(tag, "FixedFunction") == 0 ||
                clf_prefix(tag, "Grading") || strcmp(tag, "Function") == 0 ||
                strcmp(tag, "InverseLUT1D") == 0 || strcmp(tag, "InverseLUT3D") == 0 ||
                strcmp(tag, "Reference") == 0 || strcmp(tag, "Gamma") == 0) {
                /* real process nodes tocio does not implement: fail loudly
                 * rather than silently dropping a transform step */
                return TOC_ERROR_UNSUPPORTED;
            }
            if (strcmp(tag, "Matrix") == 0 || strcmp(tag, "Range") == 0 ||
                strcmp(tag, "Exponent") == 0 || strcmp(tag, "Log") == 0 ||
                strcmp(tag, "LUT1D") == 0 || strcmp(tag, "LUT3D") == 0 ||
                strcmp(tag, "ASC_CDL") == 0) {
                /* Op attributes: bit depths for Matrix/Range/LUT value
                 * normalization; LUT3D interpolation "trilinear" (default)
                 * or "tetrahedral". */
                float in_s = 1.0f, out_s = 1.0f;
                int interp = TOC_INTERP_TRILINEAR, noclamp = 0, halfdom = 0;
                char style[64];
                style[0] = 0;
                while (xa(&r, key, sizeof(key), val, sizeof(val))) {
                    if (strcmp(key, "style") == 0) {
                        size_t vl = strlen(val);
                        if (vl >= sizeof(style)) vl = sizeof(style) - 1;
                        memcpy(style, val, vl);
                        style[vl] = 0;
                        if (strcmp(val, "noClamp") == 0) noclamp = 1;
                    }
                    /* halfDomain/rawHalfs LUT1D index by half-float bit
                     * pattern: no tocio kernel, so fail loudly */
                    if ((strcmp(key, "halfDomain") == 0 || strcmp(key, "rawHalfs") == 0) &&
                        strcmp(val, "true") == 0)
                        halfdom = 1;
                    if (strcmp(key, "inBitDepth") == 0) in_s = clf_depth_scale(val);
                    else if (strcmp(key, "outBitDepth") == 0) out_s = clf_depth_scale(val);
                    else if (strcmp(key, "interpolation") == 0 &&
                             strcmp(val, "tetrahedral") == 0)
                        interp = TOC_INTERP_TETRAHEDRAL;
                }
                int empty = xc(&r);
                if (halfdom && tag[0] == 'L' && tag[3] == '1') {
                    rc = TOC_ERROR_UNSUPPORTED;
                } else if (empty && tag[1] == 'o') {
                    rc = clf_log(list, &r, style, 1);
                } else if (empty) {
                    rc = TOC_ERROR_PARSE; /* other ops need content */
                } else if (tag[0] == 'M') rc = clf_matrix(list, &r, in_s, out_s);
                else if (tag[0] == 'R') rc = clf_range(list, &r, in_s, out_s, noclamp);
                else if (tag[0] == 'E') rc = clf_exponent(list, &r, style);
                else if (tag[1] == 'o') rc = clf_log(list, &r, style, 0);
                else if (tag[0] == 'A') rc = clf_cdl(list, &r, style);
                else if (tag[3] == '1') rc = clf_lut1d(list, &r, out_s);
                else rc = clf_lut3d(list, &r, interp, out_s);
            }
            else {
                /* unknown node: skip entire element (content + closing tag) */
                char skip_tag[64];
                size_t stn = strlen(tag);
                if (stn >= sizeof(skip_tag)) stn = sizeof(skip_tag) - 1;
                memcpy(skip_tag, tag, stn);
                skip_tag[stn] = 0;
                int sc = xc(&r);
                if (!sc) {
                    size_t _maxit2 = (size_t)(r.end - r.p) + 1;
                    while (r.p < r.end) {
                        if (!_maxit2--) return TOC_ERROR_PARSE;
                        char ct[64];
                        if (xtag(&r, ct, sizeof(ct))) {
                            xc(&r);
                        } else {
                            if (strcmp(ct, skip_tag) == 0) {
                                if (r.p < r.end) ++r.p;
                                break;
                            }
                            if (r.p < r.end) ++r.p;
                        }
                    }
                }
            }
            if (!TOC_OK(rc)) return rc;
        }
    }
    return TOC_SUCCESS;
}
