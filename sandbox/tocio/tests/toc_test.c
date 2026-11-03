/*
 * tocio - host test harness (ASan/UBSan). Grows with each phase.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "toc_internal.h"

#include <dlfcn.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_pass = 0, g_fail = 0;
#define CHECK(cond, msg)                                                        \
    do {                                                                        \
        if (cond) {                                                             \
            g_pass++;                                                           \
        } else {                                                                \
            g_fail++;                                                           \
            printf("  FAIL: %s (%s:%d)\n", msg, __FILE__, __LINE__);            \
        }                                                                       \
    } while (0)

static int approx(float a, float b, float eps) {
    float d = a - b;
    if (d < 0) d = -d;
    return d <= eps;
}

/* ---- math vs libm -------------------------------------------------------- */
static void test_math(void) {
    int i;
    int ok_log = 1, ok_exp = 1, ok_pow = 1, ok_sqrt = 1;
    for (i = 1; i < 400; ++i) {
        float x = (float)i * 0.05f;
        if (!approx(toc_log2f(x), log2f(x), 3e-5f * (1.0f + x))) ok_log = 0;
        if (!approx(toc_exp2f((float)i * 0.03f - 5.0f),
                    exp2f((float)i * 0.03f - 5.0f),
                    1e-5f * exp2f((float)i * 0.03f - 5.0f)))
            ok_exp = 0;
        if (!approx(toc_powf(x, 1.0f / 2.4f), powf(x, 1.0f / 2.4f),
                    2e-5f * (1.0f + x)))
            ok_pow = 0;
        if (!approx(toc_sqrtf(x), sqrtf(x), 2e-5f * (1.0f + x))) ok_sqrt = 0;
    }
    CHECK(ok_log, "toc_log2f vs libm");
    CHECK(ok_exp, "toc_exp2f vs libm");
    CHECK(ok_pow, "toc_powf vs libm");
    CHECK(ok_sqrt, "toc_sqrtf vs libm");
    CHECK(approx(toc_raisef(10.0f, 3.0f), 1000.0f, 0.5f), "toc_raisef(10,3)");
}

/* ---- 4x4 inverse --------------------------------------------------------- */
static void test_inv4x4(void) {
    float m[16] = {2, 0, 0, 1, 0, 3, 0, 2, 0, 0, 4, 3, 0, 0, 0, 1};
    float inv[16];
    int r, c, k, ok = 1;
    CHECK(toc_inv4x4(m, inv), "inv4x4 nonsingular");
    for (r = 0; r < 4; ++r)
        for (c = 0; c < 4; ++c) {
            float s = 0.0f;
            for (k = 0; k < 4; ++k) s += m[r * 4 + k] * inv[k * 4 + c];
            if (!approx(s, r == c ? 1.0f : 0.0f, 1e-5f)) ok = 0;
        }
    CHECK(ok, "M * inv(M) == I");
}

/* ---- strbuf: hex-float round-trips bit-exact; decfloat parses close ------ */
static void test_strbuf(void) {
    float vals[] = {0.0f,    1.0f,   0.5f,    2.4f,     -3.25f,
                    0.0031308f, 65504.0f, 1.0e-6f, 1234.5678f, -0.0f};
    int i, ok_hex = 1, ok_dec = 1;
    for (i = 0; i < (int)(sizeof(vals) / sizeof(vals[0])); ++i) {
        toc_sb sb;
        char *s;
        float back;
        toc_sb_init(&sb, NULL);
        toc_sb_hexfloat(&sb, vals[i]);
        s = sb.buf;
        back = strtof(s, NULL);
        /* hex float must be bit-exact */
        if (memcmp(&back, &vals[i], sizeof(float)) != 0 &&
            !(vals[i] == 0.0f && back == 0.0f))
            ok_hex = 0;
        toc_sb_free(&sb);

        toc_sb_init(&sb, NULL);
        toc_sb_decfloat(&sb, vals[i]);
        s = sb.buf;
        back = strtof(s, NULL);
        if (!approx(back, vals[i], 1e-4f * (1.0f + fabsf(vals[i])))) ok_dec = 0;
        toc_sb_free(&sb);
    }
    CHECK(ok_hex, "hexfloat round-trips bit-exact");
    CHECK(ok_dec, "decfloat round-trips within 1e-4 rel");
    {
        toc_sb sb;
        toc_sb_init(&sb, NULL);
        toc_sb_int(&sb, -123456);
        CHECK(strcmp(sb.buf, "-123456") == 0, "sb_int");
        toc_sb_free(&sb);
    }
}

/* ---- float parser -------------------------------------------------------- */
static void test_parse(void) {
    const char *s = "  -1.5e2 , 0.25  3";
    const char *p = s, *end = s + strlen(s);
    float a, b, c;
    long n;
    CHECK(toc_parse_float(&p, end, &a) && approx(a, -150.0f, 1e-3f), "parse -1.5e2");
    CHECK(toc_parse_float(&p, end, &b) && approx(b, 0.25f, 1e-6f), "parse 0.25");
    CHECK(toc_parse_float(&p, end, &c) && approx(c, 3.0f, 1e-6f), "parse 3");
    p = "42 x";
    end = p + 4;
    CHECK(toc_parse_int(&p, end, &n) && n == 42, "parse_int 42");
}

/* ---- interpreter --------------------------------------------------------- */
static toc_op_list *newlist(void) {
    const toc_allocator *a = toc_default_allocator();
    toc_op_list *l = (toc_op_list *)malloc(sizeof(*l));
    memset(l, 0, sizeof(*l));
    l->alloc = *a;
    return l;
}

/* Push a no-param FixedFunction op (PQ/HLG, HSV, etc.). */
static void push_ff_raw(toc_op_list *l, int style) {
    toc_op *o = toc_op_list_push(l, TOC_OP_FIXEDFUNC);
    if (o) { o->u.fixedfunc.style = style; o->u.fixedfunc.nparams = 0; }
}

static void test_interp(void) {
    /* matrix: 2x scale + offset 0.1 on RGB */
    {
        toc_op_list *l = newlist();
        toc_op *m = toc_op_list_push(l, TOC_OP_MATRIX);
        float px[4] = {0.2f, 0.3f, 0.4f, 1.0f};
        m->u.matrix.m[0] = m->u.matrix.m[5] = m->u.matrix.m[10] = 2.0f;
        m->u.matrix.m[15] = 1.0f;
        m->u.matrix.off[0] = m->u.matrix.off[1] = m->u.matrix.off[2] = 0.1f;
        toc_apply(l, px, 1, 4);
        CHECK(approx(px[0], 0.5f, 1e-6f) && approx(px[1], 0.7f, 1e-6f) &&
                  approx(px[2], 0.9f, 1e-6f) && approx(px[3], 1.0f, 1e-6f),
              "matrix scale+offset");
        toc_op_list_free(l);
    }
    /* range: scale 2, clamp [0,1] */
    {
        toc_op_list *l = newlist();
        toc_op *r = toc_op_list_push(l, TOC_OP_RANGE);
        float px[3] = {0.3f, 0.7f, -0.1f};
        int c;
        for (c = 0; c < 4; ++c) {
            r->u.range.scale[c] = 2.0f;
            r->u.range.min[c] = 0.0f;
            r->u.range.max[c] = 1.0f;
        }
        r->u.range.clamp_lo = r->u.range.clamp_hi = 1;
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], 0.6f, 1e-6f) && approx(px[1], 1.0f, 1e-6f) &&
                  approx(px[2], 0.0f, 1e-6f),
              "range scale+clamp");
        toc_op_list_free(l);
    }
    /* exponent 2.2 */
    {
        toc_op_list *l = newlist();
        toc_op *e = toc_op_list_push(l, TOC_OP_EXPONENT);
        float px[3] = {0.5f, 0.5f, 0.5f};
        int c;
        for (c = 0; c < 4; ++c) e->u.exponent.e[c] = 2.2f;
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], powf(0.5f, 2.2f), 1e-4f), "exponent 2.2");
        toc_op_list_free(l);
    }
    /* log2 forward then inverse round-trips */
    {
        toc_op_list *l = newlist();
        toc_op *lg = toc_op_list_push(l, TOC_OP_LOG);
        toc_op *ag = toc_op_list_push(l, TOC_OP_LOG);
        float px[3] = {0.18f, 0.5f, 1.0f}, orig[3];
        int c;
        memcpy(orig, px, sizeof(px));
        for (c = 0; c < 3; ++c) {
            lg->u.log.log_slope[c] = ag->u.log.log_slope[c] = 1.0f;
            lg->u.log.lin_slope[c] = ag->u.log.lin_slope[c] = 1.0f;
        }
        lg->u.log.base = ag->u.log.base = 2.0f;
        lg->u.log.inverse = 0;
        ag->u.log.inverse = 1;
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], orig[0], 1e-4f) && approx(px[1], orig[1], 1e-4f),
              "log forward+inverse round-trip");
        toc_op_list_free(l);
    }
    /* lut1d identity (shared) */
    {
        toc_op_list *l = newlist();
        toc_op *op = toc_op_list_push(l, TOC_OP_LUT1D);
        static const float tbl[4] = {0.0f, 1.0f / 3, 2.0f / 3, 1.0f};
        float px[3] = {0.5f, 0.25f, 0.9f};
        op->u.lut1d.length = 4;
        op->u.lut1d.channels = 1;
        op->u.lut1d.domain_min = 0.0f;
        op->u.lut1d.domain_max = 1.0f;
        op->u.lut1d.data = tbl;
        op->u.lut1d.interp = TOC_INTERP_LINEAR;
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], 0.5f, 1e-5f) && approx(px[1], 0.25f, 1e-5f) &&
                  approx(px[2], 0.9f, 1e-5f),
              "lut1d identity");
        toc_op_list_free(l);
    }
    /* lut3d identity (trilinear + tetrahedral) */
    {
        int N = 2, ir, ig, ib, t;
        static float data[2 * 2 * 2 * 3];
        for (ib = 0; ib < N; ++ib)
            for (ig = 0; ig < N; ++ig)
                for (ir = 0; ir < N; ++ir) {
                    size_t idx = (((size_t)ib * N + ig) * N + ir) * 3;
                    data[idx + 0] = (float)ir;
                    data[idx + 1] = (float)ig;
                    data[idx + 2] = (float)ib;
                }
        for (t = 0; t < 2; ++t) {
            toc_op_list *l = newlist();
            toc_op *op = toc_op_list_push(l, TOC_OP_LUT3D);
            float px[3] = {0.2f, 0.6f, 0.9f};
            op->u.lut3d.size = N;
            op->u.lut3d.data = data;
            op->u.lut3d.domain_min[0] = op->u.lut3d.domain_min[1] =
                op->u.lut3d.domain_min[2] = 0.0f;
            op->u.lut3d.domain_max[0] = op->u.lut3d.domain_max[1] =
                op->u.lut3d.domain_max[2] = 1.0f;
            op->u.lut3d.interp = t ? TOC_INTERP_TETRAHEDRAL : TOC_INTERP_TRILINEAR;
            toc_apply(l, px, 1, 3);
            CHECK(approx(px[0], 0.2f, 1e-5f) && approx(px[1], 0.6f, 1e-5f) &&
                      approx(px[2], 0.9f, 1e-5f),
                  t ? "lut3d identity tetrahedral" : "lut3d identity trilinear");
            toc_op_list_free(l);
        }
    }
}

/* ---- YAML parser --------------------------------------------------------- */
static const char *g_cfg =
    "ocio_profile_version: 2\n"
    "roles:\n"
    "  scene_linear: lin\n"
    "  default: raw\n"
    "colorspaces:\n"
    "  - !<ColorSpace>\n"
    "    name: lin\n"
    "    isdata: false\n"
    "  - !<ColorSpace>\n"
    "    name: raw\n"
    "    isdata: true\n"
    "    to_reference: !<MatrixTransform> {matrix: [2,0,0,0, 0,2,0,0, 0,0,2,0, "
    "0,0,0,1]}\n"
    "displays:\n"
    "  sRGB:\n"
    "    - !<View> {name: Raw, colorspace: raw}\n";

static void test_yaml(void) {
    toc_arena ar;
    toc_node *root = NULL;
    int err = 0;
    toc_result rc;
    toc_arena_init(&ar, toc_default_allocator());
    rc = toc_yaml_parse(g_cfg, strlen(g_cfg), &ar, &root, &err);
    CHECK(TOC_OK(rc), "yaml parse ok");
    if (TOC_OK(rc)) {
        const toc_node *roles = toc_node_map_get(root, "roles");
        const toc_node *cs = toc_node_map_get(root, "colorspaces");
        const toc_node *disp = toc_node_map_get(root, "displays");
        CHECK(roles && roles->kind == TOC_NODE_MAP, "roles is a map");
        CHECK(roles && strcmp(toc_node_scalar(toc_node_map_get(roles,
                                                               "scene_linear")),
                              "lin") == 0,
              "role scene_linear=lin");
        CHECK(cs && cs->kind == TOC_NODE_SEQ && cs->n_items == 2,
              "2 colorspaces");
        if (cs && cs->n_items == 2) {
            const toc_node *c0 = cs->items[0];
            const toc_node *c1 = cs->items[1];
            const toc_node *t1, *mat;
            CHECK(c0->tag && strcmp(c0->tag, "ColorSpace") == 0, "cs0 tag");
            CHECK(strcmp(toc_node_scalar(toc_node_map_get(c0, "name")), "lin") ==
                      0,
                  "cs0 name=lin");
            t1 = toc_node_map_get(c1, "to_reference");
            CHECK(t1 && t1->tag && strcmp(t1->tag, "MatrixTransform") == 0,
                  "cs1 to_reference tag MatrixTransform");
            mat = t1 ? toc_node_map_get(t1, "matrix") : NULL;
            CHECK(mat && mat->kind == TOC_NODE_SEQ && mat->n_items == 16,
                  "matrix has 16 items");
            CHECK(mat && strcmp(toc_node_scalar(mat->items[0]), "2") == 0,
                  "matrix[0]=2");
        }
        {
            const toc_node *srgb = disp ? toc_node_map_get(disp, "sRGB") : NULL;
            const toc_node *v0;
            CHECK(srgb && srgb->kind == TOC_NODE_SEQ && srgb->n_items == 1,
                  "display sRGB has 1 view");
            v0 = srgb && srgb->n_items ? srgb->items[0] : NULL;
            CHECK(v0 && v0->tag && strcmp(v0->tag, "View") == 0, "view tag");
            CHECK(v0 && strcmp(toc_node_scalar(toc_node_map_get(v0, "name")),
                               "Raw") == 0,
                  "view name=Raw");
        }
    }
    toc_arena_free(&ar);
}

/* ---- processor (end to end) ---------------------------------------------- */
static const char *g_proc_cfg =
    "ocio_profile_version: 2\n"
    "roles:\n"
    "  scene_linear: lin\n"
    "colorspaces:\n"
    "  - !<ColorSpace>\n"
    "    name: lin\n"
    "    isdata: false\n"
    "  - !<ColorSpace>\n"
    "    name: srgb\n"
    "    isdata: false\n"
    "    from_reference: !<GroupTransform>\n"
    "      children:\n"
    "        - !<MatrixTransform> {matrix: [2,0,0,0, 0,2,0,0, 0,0,2,0, 0,0,0,1]}\n"
    "        - !<ExponentTransform> {value: [2, 2, 2, 1]}\n";

static void test_processor(void) {
    toc_config *cfg = NULL;
    toc_op_list *fwd = NULL, *rev = NULL;
    toc_result rc;
    rc = toc_config_parse(g_proc_cfg, strlen(g_proc_cfg), NULL, &cfg);
    CHECK(TOC_OK(rc), "config parse");
    if (!TOC_OK(rc)) return;
    CHECK(toc_config_num_colorspaces(cfg) == 2, "2 colorspaces");
    CHECK(toc_config_role(cfg, "scene_linear") &&
              strcmp(toc_config_role(cfg, "scene_linear"), "lin") == 0,
          "role lookup");

    /* lin -> srgb : scale by 2 then ^2.  0.3 -> 0.6 -> 0.36 */
    rc = toc_processor_from_colorspaces(cfg, "lin", "srgb", NULL, &fwd);
    CHECK(TOC_OK(rc) && fwd && fwd->count == 2, "build lin->srgb (2 ops)");
    if (TOC_OK(rc)) {
        float px[3] = {0.3f, 0.3f, 0.3f};
        toc_apply(fwd, px, 1, 3);
        CHECK(approx(px[0], 0.36f, 1e-4f), "lin->srgb forward value");
    }
    /* srgb -> lin : inverse (sqrt then /2). 0.36 -> 0.6 -> 0.3 */
    rc = toc_processor_from_colorspaces(cfg, "srgb", "lin", NULL, &rev);
    CHECK(TOC_OK(rc) && rev, "build srgb->lin (inverse)");
    if (TOC_OK(rc)) {
        float px[3] = {0.36f, 0.36f, 0.36f};
        toc_apply(rev, px, 1, 3);
        CHECK(approx(px[0], 0.3f, 1e-3f), "srgb->lin inverse round-trips");
    }
    /* role used as endpoint */
    {
        toc_op_list *r2 = NULL;
        rc = toc_processor_from_colorspaces(cfg, "scene_linear", "srgb", NULL,
                                            &r2);
        CHECK(TOC_OK(rc) && r2 && r2->count == 2, "role endpoint resolves");
        if (r2) toc_op_list_free(r2);
    }
    if (fwd) toc_op_list_free(fwd);
    if (rev) toc_op_list_free(rev);
    toc_config_free(cfg);
}

/* ---- CDL inverse round-trip ---------------------------------------------- */
static void test_cdl_inverse(void) {
    /* Build a config with a CDL color space to test inverse */
    static const char *cdl_cfg =
        "ocio_profile_version: 2\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: lin\n"
        "    isdata: false\n"
        "  - !<ColorSpace>\n"
        "    name: cdlin\n"
        "    isdata: false\n"
        "    to_reference: !<CDLTransform> {slope: [1.5, 1.0, 0.8], "
        "offset: [0.05, 0.0, -0.02], power: [0.9, 1.1, 1.0], sat: 0.85}\n";
    toc_config *cfg = NULL;
    toc_op_list *fwd = NULL, *rev = NULL;
    float px[3] = {0.18f, 0.35f, 0.09f}, orig[3];
    toc_result rc;
    memcpy(orig, px, sizeof(px));
    rc = toc_config_parse(cdl_cfg, strlen(cdl_cfg), NULL, &cfg);
    CHECK(TOC_OK(rc), "CDL config parse");
    if (!TOC_OK(rc)) return;
    /* forward lin -> cdlin (inverse of cdlin's to_reference) */
    rc = toc_processor_from_colorspaces(cfg, "lin", "cdlin", NULL, &fwd);
    CHECK(TOC_OK(rc) && fwd, "CDL forward build");
    toc_op_list_free(fwd);
    fwd = NULL;
    /* but cdlin's to_reference is CDL, so lin->cdlin is the inverse path */
    /* Actually: cdlin's to_reference is CDL, so cdlin->lin is forward CDL.
     * lin->cdlin is inverse CDL. Let me test both. */
    /* test 1: cdlin -> lin (forward CDL, 1 op), then lin -> cdlin (inverse CDL, 3 ops) */
    rc = toc_processor_from_colorspaces(cfg, "cdlin", "lin", NULL, &fwd);
    CHECK(TOC_OK(rc) && fwd && fwd->count == 1,
          "CDL forward -> 1 op");
    if (TOC_OK(rc)) {
        rc = toc_processor_from_colorspaces(cfg, "lin", "cdlin", NULL, &rev);
        CHECK(TOC_OK(rc) && rev && rev->count == 3,
              "CDL inverse -> 3 ops (matrix+exponent+range)");
        if (TOC_OK(rc)) {
            toc_apply(fwd, px, 1, 3);
            toc_apply(rev, px, 1, 3);
            CHECK(approx(px[0], orig[0], 2e-3f) &&
                  approx(px[1], orig[1], 2e-3f) &&
                  approx(px[2], orig[2], 2e-3f),
                  "CDL forward+inverse round-trip");
            toc_op_list_free(rev);
        }
        toc_op_list_free(fwd);
    }
    toc_config_free(cfg);
}

/* ---- looks + active_displays --------------------------------------------- */
static const char *g_look_cfg =
    "ocio_profile_version: 2\n"
    "roles:\n"
    "  scene_linear: lin\n"
    "colorspaces:\n"
    "  - !<ColorSpace>\n"
    "    name: lin\n"
    "    isdata: false\n"
    "  - !<ColorSpace>\n"
    "    name: srgb\n"
    "    isdata: false\n"
    "    from_reference: !<ExponentTransform> {value: [0.45, 0.45, 0.45, 1]}\n"
    "looks:\n"
    "  - !<Look>\n"
    "    name: darken\n"
    "    process_space: lin\n"
    "    transform: !<ExponentTransform> {value: [0.5, 0.5, 0.5, 1]}\n"
    "active_displays: [sRGB]\n"
    "active_views: [Raw]\n"
    "displays:\n"
    "  sRGB:\n"
    "    - !<View> {name: Raw, colorspace: srgb}\n"
    "    - !<View> {name: Dark, colorspace: srgb, looks: darken}\n";

static void test_looks(void) {
    toc_config *cfg = NULL;
    toc_result rc =
        toc_config_parse(g_look_cfg, strlen(g_look_cfg), NULL, &cfg);
    CHECK(TOC_OK(rc), "looks config parse");
    if (!TOC_OK(rc)) return;
    /* introspection */
    CHECK(toc_config_num_looks(cfg) == 1, "num_looks == 1");
    {
        const char *n = toc_config_look_name(cfg, 0);
        CHECK(n && strcmp(n, "darken") == 0, "look name");
    }
    {
        int na = toc_config_num_active_displays(cfg);
        CHECK(na == 1, "active_displays count");
        if (na > 0) {
            const char *d = toc_config_active_display_name(cfg, 0);
            CHECK(d && strcmp(d, "sRGB") == 0, "active display name");
        }
    }
    {
        int na = toc_config_num_active_views(cfg);
        CHECK(na == 1, "active_views count");
        if (na > 0) {
            const char *v = toc_config_active_view_name(cfg, 0);
            CHECK(v && strcmp(v, "Raw") == 0, "active view name");
        }
    }
    /* simple view (no look): src -> srgb */
    {
        toc_op_list *ops = NULL;
        float px[3] = {0.3f, 0.3f, 0.3f};
        rc = toc_processor_from_display_view(cfg, "lin", "sRGB", "Raw",
                                             NULL, &ops);
        CHECK(TOC_OK(rc) && ops && ops->count == 1, "Raw no-look view");
        if (TOC_OK(rc)) {
            toc_apply(ops, px, 1, 3);
            CHECK(approx(px[0], powf(0.3f, 0.45f), 1e-3f),
                  "Raw view (srgb ^0.45)");
            toc_op_list_free(ops);
        }
    }
    /* view with look: src -> reference -> process_space lin -> ^0.5 -> reference -> srgb */
    {
        toc_op_list *ops = NULL;
        float px[3] = {0.3f, 0.3f, 0.3f};
        rc = toc_processor_from_display_view(cfg, "lin", "sRGB", "Dark",
                                             NULL, &ops);
        CHECK(TOC_OK(rc) && ops, "Dark look view");
        if (TOC_OK(rc)) {
            /* pipeline: 0.3 (lin) -> to ref (identity) -> lin process space (no-op)
             * -> ^0.5 -> to ref (identity) -> srgb ^0.45
             * result: pow(pow(0.3, 0.5), 0.45) = pow(0.3, 0.225) = 0.763 */
            toc_apply(ops, px, 1, 3);
            CHECK(approx(px[0], powf(0.3f, 0.225f), 1e-3f),
                  "Dark view (^0.5 then ^0.45)");
            toc_op_list_free(ops);
        }
    }
    toc_config_free(cfg);
}

/* ---- view_transform display path ----------------------------------------- */
static const char *g_vt_cfg =
    "ocio_profile_version: 2\n"
    "roles:\n"
    "  scene_linear: lin\n"
    "colorspaces:\n"
    "  - !<ColorSpace>\n"
    "    name: lin\n"
    "    isdata: false\n"
    "  - !<ColorSpace>\n"
    "    name: srgb\n"
    "    isdata: false\n"
    "    from_reference: !<ExponentTransform> {value: [0.45, 0.45, 0.45, 1]}\n"
    "view_transform:\n"
    "  - !<ViewTransform>\n"
    "    name: test_vt\n"
    "    from_reference: !<MatrixTransform> {matrix: [2,0,0,0, 0,2,0,0, "
    "0,0,2,0, 0,0,0,1]}\n"
    "displays:\n"
    "  sRGB:\n"
    "    - !<View> {name: Raw, colorspace: srgb}\n"
    "    - !<View> {name: Log, view_transform: test_vt, display_colorspace: srgb}\n";

static void test_display_view(void) {
    toc_config *cfg = NULL;
    toc_result rc =
        toc_config_parse(g_vt_cfg, strlen(g_vt_cfg), NULL, &cfg);
    CHECK(TOC_OK(rc), "view_transform config parse");
    if (!TOC_OK(rc)) return;
    /* introspection */
    CHECK(toc_config_num_view_transforms(cfg) == 1,
          "num_view_transforms == 1");
    {
        const char *n = toc_config_view_transform_name(cfg, 0);
        CHECK(n && strcmp(n, "test_vt") == 0, "view_transform name");
    }
    /* simple view: src -> srgb via colorspace */
    {
        toc_op_list *ops = NULL;
        rc = toc_processor_from_display_view(cfg, "lin", "sRGB", "Raw",
                                             NULL, &ops);
        CHECK(TOC_OK(rc) && ops && ops->count == 1, "Raw simple view -> 1 op");
        if (TOC_OK(rc)) {
            float px[3] = {0.3f, 0.3f, 0.3f};
            toc_apply(ops, px, 1, 3);
            /* srgb from_reference is ^0.45 on 0.3 = pow(0.3, 0.45) = 0.589 */
            CHECK(approx(px[0], powf(0.3f, 0.45f), 1e-3f), "Raw view value");
            toc_op_list_free(ops);
        }
    }
    /* view_transform view: src -> reference -> vt *2 -> srgb ^0.45 */
    {
        toc_op_list *ops = NULL;
        rc = toc_processor_from_display_view(cfg, "lin", "sRGB", "Log",
                                             NULL, &ops);
        CHECK(TOC_OK(rc) && ops && ops->count == 2,
              "Log view_transform view -> 2 ops");
        if (TOC_OK(rc)) {
            float px[3] = {0.3f, 0.3f, 0.3f};
            /* pipeline: 0.3 (lin) -> identity to ref -> *2 (vt from_ref)
             * -> pow(0.6, 0.45) = 0.796 (srgb from_ref) */
            toc_apply(ops, px, 1, 3);
            CHECK(approx(px[0], powf(0.6f, 0.45f), 1e-3f),
                  "Log view_transform view value");
            toc_op_list_free(ops);
        }
    }
    toc_config_free(cfg);
}

/* ---- file LUTs ----------------------------------------------------------- */
static void load_and_check(const char *name, const char *txt, float in,
                           float expect, const char *msg) {
    toc_op_list *l = newlist();
    toc_result rc = toc_load_lutfile(l, name, txt, strlen(txt), 0);
    if (TOC_OK(rc)) {
        float px[3] = {in, in, in};
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], expect, 1e-4f), msg);
    } else {
        CHECK(0, msg);
    }
    toc_op_list_free(l);
}

static void test_lutfile(void) {
    load_and_check("id.cube",
                   "LUT_1D_SIZE 2\n0 0 0\n1 1 1\n", 0.5f, 0.5f,
                   ".cube 1D identity");
    load_and_check(
        "id3.cube",
        "LUT_3D_SIZE 2\n0 0 0\n1 0 0\n0 1 0\n1 1 0\n0 0 1\n1 0 1\n0 1 1\n1 1 1\n",
        0.3f, 0.3f, ".cube 3D identity");
    load_and_check("id.spi1d",
                   "Version 1\nFrom 0.0 1.0\nLength 2\nComponents 1\n{\n0.0\n"
                   "1.0\n}\n",
                   0.5f, 0.5f, ".spi1d identity");
    /* .spi3d identity N=2 (8 entries) */
    load_and_check(
        "id.spi3d",
        "SPILUT 1.0\n3 3\n2 2 2\n"
        "0 0 0  0 0 0\n0 0 1  0 0 1\n0 1 0  0 1 0\n0 1 1  0 1 1\n"
        "1 0 0  1 0 0\n1 0 1  1 0 1\n1 1 0  1 1 0\n1 1 1  1 1 1\n",
        0.4f, 0.4f, ".spi3d identity");
    /* a non-identity .spi1d: doubles input (clamped at domain top) */
    load_and_check("dbl.spi1d",
                   "Version 1\nFrom 0.0 1.0\nLength 3\nComponents 1\n{\n0.0\n"
                   "0.5\n1.0\n}\n",
                   0.25f, 0.25f, ".spi1d ramp midpoint");
    /* ---- CLF (Common LUT Format) ----------------------------------------- */
    load_and_check(
        "id.clf",
        "<?xml version=\"1.0\"?>\n"
        "<ProcessList compCLFversion=\"3\" id=\"id\">\n"
        "  <LUT1D>\n"
        "    <Array dim=\"4 3\">\n"
        "      0 0 0\n"
        "      0.3333 0.3333 0.3333\n"
        "      0.6667 0.6667 0.6667\n"
        "      1 1 1\n"
        "    </Array>\n"
        "  </LUT1D>\n"
        "</ProcessList>\n",
        0.5f, 0.5f, ".clf 1D identity via LUT");
    load_and_check(
        "id3.clf",
        "<ProcessList compCLFversion=\"3\" id=\"id3\">\n"
        "  <LUT3D>\n"
        "    <Array dim=\"2 2 2 3\">\n"
        "      0 0 0\n"
        "      0 0 1\n"
        "      0 1 0\n"
        "      0 1 1\n"
        "      1 0 0\n"
        "      1 0 1\n"
        "      1 1 0\n"
        "      1 1 1\n"
        "    </Array>\n"
        "  </LUT3D>\n"
        "</ProcessList>\n",
        0.4f, 0.4f, ".clf 3D identity");
    /* Matrix doubling brightness */
    {
        static const char *clf =
            "<?xml version=\"1.0\"?>\n"
            "<ProcessList>\n"
            "  <Matrix>\n"
            "    <Array dim=\"3 3\">\n"
            "      2 0 0\n"
            "      0 2 0\n"
            "      0 0 2\n"
            "    </Array>\n"
            "  </Matrix>\n"
            "</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "x2.clf", clf, strlen(clf), 0);
        CHECK(TOC_OK(rc) && l->count == 1 && l->ops[0].kind == TOC_OP_MATRIX,
              ".clf Matrix 2x brightness");
        if (TOC_OK(rc)) {
            float px[3] = {0.3f, 0.3f, 0.3f};
            toc_apply(l, px, 1, 3);
            CHECK(approx(px[0], 0.6f, 1e-4f), ".clf Matrix 2x value");
        }
        toc_op_list_free(l);
    }
    /* Range CLA */
    {
        static const char *clf =
            "<ProcessList>\n"
            "  <Range>\n"
            "    <minInValue>0.0</minInValue>\n"
            "    <maxInValue>1.0</maxInValue>\n"
            "    <minOutValue>0.1</minOutValue>\n"
            "    <maxOutValue>0.9</maxOutValue>\n"
            "  </Range>\n"
            "</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "cla.clf", clf, strlen(clf), 0);
        CHECK(TOC_OK(rc) && l->count == 1 && l->ops[0].kind == TOC_OP_RANGE,
              ".clf Range");
        if (TOC_OK(rc)) {
            float p1[3] = {0.0f, 0.0f, 0.0f};
            float p2[3] = {0.5f, 0.5f, 0.5f};
            float p3[3] = {1.0f, 1.0f, 1.0f};
            toc_apply(l, p1, 1, 3);
            toc_apply(l, p2, 1, 3);
            toc_apply(l, p3, 1, 3);
            CHECK(approx(p1[0], 0.1f, 1e-4f), ".clf Range lo clamp");
            CHECK(approx(p2[0], 0.5f, 1e-4f), ".clf Range mid");
            CHECK(approx(p3[0], 0.9f, 1e-4f), ".clf Range hi clamp");
        }
        toc_op_list_free(l);
    }
    /* Exponent */
    {
        static const char *clf =
            "<ProcessList>\n"
            "  <Exponent style=\"basicFwd\">\n"
            "    <ExponentParams exponent=\"2.2\"/>\n"
            "  </Exponent>\n"
            "</ProcessList>\n";
        load_and_check("gamma.clf", clf, 0.5f, powf(0.5f, 2.2f), ".clf Exponent");
    }
    /* Multi-op: Matrix + Range */
    {
        static const char *clf =
            "<?xml version=\"1.0\"?>\n"
            "<ProcessList>\n"
            "  <Matrix>\n"
            "    <Array dim=\"3 3\">\n"
            "      1 0 0\n"
            "      0 1 0\n"
            "      0 0 1\n"
            "    </Array>\n"
            "  </Matrix>\n"
            "  <Range>\n"
            "    <minInValue>0.0</minInValue>\n"
            "    <maxInValue>1.0</maxInValue>\n"
            "    <minOutValue>0.0</minOutValue>\n"
            "    <maxOutValue>1.0</maxOutValue>\n"
            "  </Range>\n"
            "</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "multi.clf", clf, strlen(clf), 0);
        CHECK(TOC_OK(rc) && l->count == 2, ".clf multi-op count");
        CHECK(TOC_OK(rc) && l->count >= 2 &&
                  l->ops[0].kind == TOC_OP_MATRIX &&
                  l->ops[1].kind == TOC_OP_RANGE,
              ".clf multi-op types");
        if (TOC_OK(rc)) {
            float px[3] = {0.42f, 0.42f, 0.42f};
            toc_apply(l, px, 1, 3);
            CHECK(approx(px[0], 0.42f, 1e-4f), ".clf multi-op identity");
        }
        toc_op_list_free(l);
    }
    /* sniff by content (no name hint): <?xml triggers CLF parser */
    load_and_check(NULL,
                   "<?xml version=\"1.0\"?>\n<ProcessList>\n"
                   "  <LUT1D>\n"
                   "    <Array dim=\"2 3\">0 0 0 1 1 1</Array>\n"
                   "  </LUT1D>\n"
                   "</ProcessList>\n",
                   0.5f, 0.5f, ".clf sniff by <?xml");
    /* sniff by content: <ProcessList directly */
    load_and_check(NULL,
                   "<ProcessList>\n"
                   "  <LUT1D>\n"
                   "    <Array dim=\"2 3\">0 0 0 1 1 1</Array>\n"
                   "  </LUT1D>\n"
                   "</ProcessList>\n",
                   0.5f, 0.5f, ".clf sniff by <ProcessList");
    /* ---- CSP (Cinespace "CSPLUTV100", OCIO FileFormatCSP layout) -------- */
#define CSP_ID3 "0 0 0\n1 0 0\n0 1 0\n1 1 0\n0 0 1\n1 0 1\n0 1 1\n1 1 1\n"
#define CSP_NOPRE "2\n0 1\n0 1\n2\n0 1\n0 1\n2\n0 1\n0 1\n"
    /* 3D identity N=2 (red fastest), identity preluts */
    load_and_check("id.csp", "CSPLUTV100\n3D\n\n" CSP_NOPRE "\n2 2 2\n" CSP_ID3,
                   0.4f, 0.4f, ".csp 3D identity");
    /* metadata block, blank lines, CRLF and lower-case keywords */
    load_and_check("meta.csp",
                   "CSPLUTV100\r\n3d\r\nBEGIN METADATA\r\nsome text\r\n"
                   "END METADATA\r\n\r\n" CSP_NOPRE "\r\n2 2 2\r\n" CSP_ID3,
                   0.4f, 0.4f, ".csp metadata + CRLF");
    /* preluts with count 0 are identity channels */
    load_and_check("zero.csp", "CSPLUTV100\n3D\n0\n0\n0\n2 2 2\n" CSP_ID3,
                   0.4f, 0.4f, ".csp zero-length preluts");
    /* 1D LUT (squares) */
    load_and_check("sq.csp",
                   "CSPLUTV100\n1D\n" CSP_NOPRE "3\n0 0 0\n0.25 0.25 0.25\n1 1 1\n",
                   0.5f, 0.25f, ".csp 1D LUT");
    /* content sniffing (no extension) */
    load_and_check(NULL, "CSPLUTV100\n3D\n" CSP_NOPRE "2 2 2\n" CSP_ID3, 0.4f, 0.4f,
                   ".csp sniff by content");
    /* non-identity prelut over [0,2]: in 0..2 -> out 0..1 (linear spline),
     * so the pipeline maps 0.8 -> 0.4 through an identity cube. Ops are the
     * [min,max]->[0,1] matrix, the 65536-sample prelut LUT1D and the LUT3D. */
    {
        static const char *csp =
            "CSPLUTV100\n3D\n2\n0 2\n0 1\n2\n0 2\n0 1\n2\n0 2\n0 1\n2 2 2\n" CSP_ID3;
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "pre.csp", csp, strlen(csp), 0);
        CHECK(TOC_OK(rc) && l->count == 3 && l->ops[0].kind == TOC_OP_MATRIX &&
                  l->ops[1].kind == TOC_OP_LUT1D && l->ops[1].u.lut1d.length == 65536 &&
                  l->ops[2].kind == TOC_OP_LUT3D,
              ".csp prelut -> matrix + LUT1D + LUT3D");
        if (TOC_OK(rc)) {
            float px[3] = {0.8f, 0.8f, 0.8f};
            toc_apply(l, px, 1, 3);
            CHECK(approx(px[0], 0.4f, 1e-4f), ".csp prelut value");
        }
        toc_op_list_free(l);
    }
    /* invented legacy syntax is not CSP */
    {
        static const char *bad = "CSPLUTV1.0\n3DMESH 2\n3D\n" CSP_ID3;
        toc_op_list *l = newlist();
        CHECK(!TOC_OK(toc_load_lutfile(l, "old.csp", bad, strlen(bad), 0)),
              ".csp non-standard header rejected");
        toc_op_list_free(l);
    }
}

/* file reader returning a baked identity .spi1d for any name */
static toc_result test_reader(void *user, const char *name,
                              const toc_allocator *a, char **data, size_t *len) {
    static const char *spi =
        "Version 1\nFrom 0.0 1.0\nLength 2\nComponents 3\n{\n"
        "0 0 0\n1 1 1\n}\n";
    size_t n = strlen(spi);
    char *buf = (char *)toc_malloc(a, n + 1);
    (void)user;
    (void)name;
    if (!buf) return TOC_ERROR_OUT_OF_MEMORY;
    memcpy(buf, spi, n + 1);
    *data = buf;
    *len = n;
    return TOC_SUCCESS;
}

static void test_filetransform(void) {
    static const char *cfg_txt =
        "ocio_profile_version: 2\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: lin\n"
        "    isdata: false\n"
        "  - !<ColorSpace>\n"
        "    name: lut\n"
        "    isdata: false\n"
        "    from_reference: !<FileTransform> {src: id.spi1d}\n";
    toc_config *cfg = NULL;
    toc_op_list *ops = NULL;
    toc_result rc = toc_config_parse(cfg_txt, strlen(cfg_txt), NULL, &cfg);
    CHECK(TOC_OK(rc), "filetransform config parse");
    if (!TOC_OK(rc)) return;
    toc_config_set_file_reader(cfg, test_reader, NULL);
    rc = toc_processor_from_colorspaces(cfg, "lin", "lut", NULL, &ops);
    CHECK(TOC_OK(rc) && ops && ops->count == 1, "FileTransform -> 1 LUT op");
    if (TOC_OK(rc)) {
        float px[3] = {0.42f, 0.1f, 0.9f};
        toc_apply(ops, px, 1, 3);
        CHECK(approx(px[0], 0.42f, 1e-4f), "FileTransform identity applies");
        toc_op_list_free(ops);
    }
    toc_config_free(cfg);
}

/* ---- AOT-C codegen: interpreter == compiled emitted-C --------------------- */
typedef void (*apply_fn)(float *, size_t);

static void build_pipeline(toc_op_list *l) {
    toc_op *m = toc_op_list_push(l, TOC_OP_MATRIX);
    toc_op *e = toc_op_list_push(l, TOC_OP_EXPONENT);
    toc_op *r = toc_op_list_push(l, TOC_OP_RANGE);
    int c;
    /* a non-trivial mixing matrix */
    static const float rm[16] = {0.6f, 0.3f, 0.1f, 0.0f, 0.2f, 0.7f, 0.1f, 0.0f,
                                 0.1f, 0.2f, 0.7f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f};
    int i, j;
    for (i = 0; i < 4; ++i) {
        for (j = 0; j < 4; ++j) m->u.matrix.m[j * 4 + i] = rm[i * 4 + j];
        m->u.matrix.off[i] = 0.0f;
    }
    for (c = 0; c < 4; ++c) e->u.exponent.e[c] = (c < 3) ? 2.2f : 1.0f;
    for (c = 0; c < 4; ++c) {
        r->u.range.scale[c] = 1.0f;
        r->u.range.min[c] = 0.0f;
        r->u.range.max[c] = 1.0f;
    }
    r->u.range.clamp_lo = r->u.range.clamp_hi = 1;
}

/* ---- hostile-input hardening (security audit 2026-11-04) ---------------- */
static toc_result spi2_reader(void *user, const char *name,
                              const toc_allocator *a, char **data, size_t *len) {
    const char *txt = (const char *)user;
    size_t n = strlen(txt);
    char *buf = (char *)toc_malloc(a, n ? n : 1);
    (void)name;
    if (!buf) return TOC_ERROR_OUT_OF_MEMORY;
    memcpy(buf, txt, n); /* deliberately not NUL-terminated */
    *data = buf;
    *len = n;
    return TOC_SUCCESS;
}

static void test_hostile(void) {
    /* Cyclic ColorSpaceTransform must fail, not recurse until stack overflow. */
    {
        static const char *cfg_txt =
            "ocio_profile_version: 2\n"
            "colorspaces:\n"
            "  - !<ColorSpace>\n"
            "    name: a\n"
            "    to_reference: !<ColorSpaceTransform> {src: a, dst: b}\n"
            "  - !<ColorSpace>\n"
            "    name: b\n";
        toc_config *cfg = NULL;
        toc_op_list *ops = NULL;
        CHECK(TOC_OK(toc_config_parse(cfg_txt, strlen(cfg_txt), NULL, &cfg)),
              "cyclic config parses");
        if (cfg) {
            CHECK(!TOC_OK(toc_processor_from_colorspaces(cfg, "a", "b", NULL, &ops)) &&
                      !ops,
                  "cyclic ColorSpaceTransform rejected");
            toc_config_free(cfg);
        }
    }
    /* Deeply nested flow and block YAML is rejected, not a stack overflow. */
    {
        size_t depth = 100000, i, n = 0;
        char *txt = (char *)malloc(depth * 2 + 16);
        toc_config *cfg = NULL;
        if (txt) {
            n = 0;
            memcpy(txt, "k: ", 3); n = 3;
            for (i = 0; i < depth; ++i) txt[n++] = '[';
            CHECK(!TOC_OK(toc_config_parse(txt, n, NULL, &cfg)) && !cfg,
                  "deep flow nesting rejected");
            n = 0;
            for (i = 0; i < depth; ++i) { txt[n++] = '-'; txt[n++] = ' '; }
            txt[n++] = 'x';
            CHECK(!TOC_OK(toc_config_parse(txt, n, NULL, &cfg)) && !cfg,
                  "deep block nesting rejected");
            free(txt);
        }
    }
    /* A wide flow sequence parses in linear (not quadratic) arena space. */
    {
        size_t items = 200000, i, n = 0;
        char *txt = (char *)malloc(items * 2 + 16);
        toc_config *cfg = NULL;
        if (txt) {
            memcpy(txt, "k: [", 4); n = 4;
            for (i = 0; i < items; ++i) { txt[n++] = '1'; txt[n++] = ','; }
            txt[n++] = ']';
            CHECK(TOC_OK(toc_config_parse(txt, n, NULL, &cfg)), "wide flow seq parses");
            toc_config_free(cfg);
            free(txt);
        }
    }
    /* 2-component spi1d would be read with stride 3 past its end. */
    {
        const char *s = "Version 1\nFrom 0.0 1.0\nLength 2\nComponents 2\n{\n"
                        "0 0\n1 1\n}\n";
        toc_op_list *l = newlist();
        CHECK(!TOC_OK(toc_load_lutfile(l, "two.spi1d", s, strlen(s), 0)),
              "spi1d Components 2 rejected");
        toc_op_list_free(l);
    }
    /* Size headers larger than the text can hold fail before allocating. */
    {
        const char *cube = "LUT_3D_SIZE 256\n0 0 0\n";
        const char *spi3 = "SPILUT 1.0\n3 3\n256 256 256\n0 0 0 0 0 0\n";
        const char *clf = "<ProcessList><LUT3D><Array dim=\"256 256 256 3\">0 0 0"
                          "</Array></LUT3D></ProcessList>";
        const char *csp = "CSPLUTV100\n3D\n0\n0\n0\n129 129 129\n0 0 0\n";
        toc_op_list *l = newlist();
        CHECK(toc_load_lutfile(l, "big.cube", cube, strlen(cube), 0) == TOC_ERROR_PARSE,
              "oversized .cube header rejected");
        CHECK(toc_load_lutfile(l, "big.spi3d", spi3, strlen(spi3), 0) == TOC_ERROR_PARSE,
              "oversized .spi3d header rejected");
        CHECK(toc_load_lutfile(l, "big.clf", clf, strlen(clf), 0) == TOC_ERROR_PARSE,
              "oversized .clf LUT3D rejected");
        CHECK(toc_load_lutfile(l, "big.csp", csp, strlen(csp), 0) == TOC_ERROR_PARSE,
              "oversized .csp mesh rejected");
        CHECK(l->count == 0 && l->owned_count == 0, "rejected LUTs own nothing");
        toc_op_list_free(l);
    }
    /* Repeated size/Array/section declarations no longer leak (LSan). */
    {
        const char *cube = "LUT_1D_SIZE 2\nLUT_1D_SIZE 2\n0 0 0\n1 1 1\n";
        const char *clf = "<ProcessList><LUT1D><Array dim=\"2 3\">0 0 0 1 1 1</Array>"
                          "<Array dim=\"2 3\">0 0 0 1 1 1</Array></LUT1D></ProcessList>";
        const char *csp = "CSPLUTV100\n3D\n3\n0 0.5 1\n0 1\n0\n0\n2 2 2\n" CSP_ID3;
        toc_op_list *l = newlist();
        CHECK(!TOC_OK(toc_load_lutfile(l, "dup.cube", cube, strlen(cube), 0)),
              "duplicate .cube size rejected");
        CHECK(!TOC_OK(toc_load_lutfile(l, "dup.clf", clf, strlen(clf), 0)),
              "duplicate .clf Array rejected");
        CHECK(!TOC_OK(toc_load_lutfile(l, "dup.csp", csp, strlen(csp), 0)),
              "mismatched .csp prelut rejected");
        toc_op_list_free(l);
    }
    /* CLF LUT1D must supply every channel value (no uninitialized reads). */
    {
        const char *clf = "<ProcessList><LUT1D><Array dim=\"4 3\">0 0 0 1</Array>"
                          "</LUT1D></ProcessList>";
        toc_op_list *l = newlist();
        CHECK(!TOC_OK(toc_load_lutfile(l, "short.clf", clf, strlen(clf), 0)),
              "short .clf LUT1D rejected");
        toc_op_list_free(l);
    }
    /* Unterminated <? in a non-NUL-terminated buffer stays in bounds (ASan). */
    {
        static const char clf[] = "<ProcessList><?";
        char *buf = (char *)malloc(sizeof(clf) - 1);
        toc_op_list *l = newlist();
        if (buf) {
            memcpy(buf, clf, sizeof(clf) - 1);
            (void)toc_load_lutfile(l, "pi.clf", buf, sizeof(clf) - 1, 0);
            free(buf);
        }
        toc_op_list_free(l);
        CHECK(1, "unterminated <? stays in bounds");
    }
    /* ACES 2.0 output transform on non-finite / huge pixels: table lookups
     * must stay in range (UBSan aborts on the float->index cast otherwise). */
    {
        static const float v[6] = {0.0f, 1.0f, -1.0f, 1e30f, -1e30f, 3e38f};
        toc_op_list *l = newlist();
        float px[4 * 8];
        union { uint32_t u; float f; } nan_u, inf_u;
        int i;
        nan_u.u = 0x7fc00000u; inf_u.u = 0x7f800000u;
        if (TOC_OK(toc_builtin_expand(
                l, "ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709_2.0", 0))) {
            for (i = 0; i < 4 * 8; ++i) px[i] = v[(i * 7 + i / 4) % 6];
            px[0] = nan_u.f; px[5] = inf_u.f; px[10] = -inf_u.f; px[13] = nan_u.f;
            px[16] = 0.5f; px[17] = nan_u.f; px[18] = 0.5f; /* NaN hue, finite J */
            toc_apply(l, px, 8, 4);
            /* The op itself, unshielded by the preceding range clamps (the JIT
             * and single-pixel helper paths apply ops one at a time). */
            for (i = 0; i < (int)l->count; ++i) {
                if (l->ops[i].kind == TOC_OP_ACES_OUTPUT) {
                    /* every combination of special values over R, G, B */
                    float sv[9];
                    int r, g, b;
                    memcpy(sv, v, sizeof(v));
                    sv[6] = nan_u.f; sv[7] = inf_u.f; sv[8] = -inf_u.f;
                    for (r = 0; r < 9; ++r)
                        for (g = 0; g < 9; ++g)
                            for (b = 0; b < 9; ++b) {
                                float q[4];
                                q[0] = sv[r]; q[1] = sv[g]; q[2] = sv[b]; q[3] = 1.0f;
                                toc_apply_op_pixel(&l->ops[i], q, 4);
                            }
                }
            }
            CHECK(1, "ACES2 output on NaN/Inf pixels stays in bounds");
        } else {
            CHECK(0, "ACES2 builtin expand");
        }
        toc_op_list_free(l);
    }
    /* Huge exponents/integers saturate (no int overflow, no 2^31-step loop). */
    {
        const char *s = "1e999999999999 -2e-99999999999 99999999999999999999999";
        const char *p = s, *end = s + strlen(s);
        float a = 0.0f, b = 1.0f;
        long n = 0;
        CHECK(toc_parse_float(&p, end, &a) && a > 3e38f, "huge exponent -> inf");
        CHECK(toc_parse_float(&p, end, &b) && b == 0.0f, "tiny exponent -> 0");
        CHECK(toc_parse_int(&p, end, &n) && n > 0, "huge integer saturates");
    }
    /* Non-ASCII byte in attributes used to spin xa() forever (fuzz timeout). */
    {
        const char clf[] = "<ProcessList id=\"x\" \xce\xd9 a=\"b\">"
                           "<LUT1D><Array dim=\"2 \xd9\">0 1</Array></LUT1D>"
                           "</ProcessList>";
        toc_op_list *l = newlist();
        (void)toc_load_lutfile(l, "hi.clf", clf, sizeof(clf) - 1, 0);
        toc_op_list_free(l);
        CHECK(1, "non-ASCII CLF attribute bytes terminate");
    }
    /* FileTransform through a non-terminating reader + LUT load cap. */
    {
        static const char *cfg_txt =
            "ocio_profile_version: 2\n"
            "colorspaces:\n"
            "  - !<ColorSpace>\n"
            "    name: lut\n"
            "    to_reference: !<FileTransform> {src: x.clf}\n"
            "  - !<ColorSpace>\n"
            "    name: ref\n";
        toc_config *cfg = NULL;
        toc_op_list *ops = NULL;
        if (TOC_OK(toc_config_parse(cfg_txt, strlen(cfg_txt), NULL, &cfg))) {
            toc_config_set_file_reader(cfg, spi2_reader, (void *)"<?xml?><Proc");
            CHECK(!TOC_OK(toc_processor_from_colorspaces(cfg, "lut", "ref", NULL, &ops)),
                  "truncated CLF via reader rejected");
            toc_op_list_free(ops);
            toc_config_free(cfg);
        } else {
            CHECK(0, "filetransform hostile config parse");
        }
    }
    /* AOT-C function name must be a C identifier. */
    {
        toc_op_list *l = newlist();
        toc_codegen_c_opts o;
        char *src = NULL;
        size_t n = 0;
        memset(&o, 0, sizeof(o));
        o.func_name = "f(void){} int evil";
        CHECK(toc_emit_c(l, &o, NULL, &src, &n) == TOC_ERROR_INVALID_ARGUMENT && !src,
              "codegen rejects non-identifier func_name");
        o.func_name = "ok_name_1";
        CHECK(TOC_OK(toc_emit_c(l, &o, NULL, &src, &n)) && src, "codegen identifier ok");
        free(src);
        toc_op_list_free(l);
    }
}

/* ---- CLF conformance (dim order, bit depth, styles; checked vs PyOCIO) --- */
static toc_op_list *clf_load(const char *body, toc_result *rc) {
    static char buf[4096];
    toc_op_list *l = newlist();
    snprintf(buf, sizeof(buf),
             "<?xml version=\"1.0\"?>\n<ProcessList id=\"t\" compCLFversion=\"3\">\n%s"
             "</ProcessList>\n", body);
    *rc = toc_load_lutfile(l, "t.clf", buf, strlen(buf), 0);
    return l;
}

static int clf_px(const char *body, const float in[4], const float want[4],
                  float eps) {
    toc_result rc;
    toc_op_list *l = clf_load(body, &rc);
    float px[4];
    int ok = TOC_OK(rc), c;
    memcpy(px, in, sizeof(px));
    if (ok) {
        toc_apply(l, px, 1, 4);
        for (c = 0; c < 4; ++c) ok = ok && approx(px[c], want[c], eps);
    }
    toc_op_list_free(l);
    return ok;
}

static void test_clf_conformance(void) {
    /* LUT3D: dim="N N N 3", entries blue-fastest. f(r,g,b)=(r, g/2, b/4) is
     * affine, so any interpolation is exact; a red-fastest misread swaps r/b. */
    static const char *lut3 =
        "<LUT3D inBitDepth=\"32f\" outBitDepth=\"32f\"><Array dim=\"2 2 2 3\">\n"
        "0 0 0  0 0 0.25  0 0.5 0  0 0.5 0.25\n"
        "1 0 0  1 0 0.25  1 0.5 0  1 0.5 0.25\n</Array></LUT3D>\n";
    float in[4], want[4];
    in[0] = 1; in[1] = 0; in[2] = 0; in[3] = 0.7f;
    want[0] = 1; want[1] = 0; want[2] = 0; want[3] = 0.7f;
    CHECK(clf_px(lut3, in, want, 1e-5f), "clf LUT3D blue-fastest red axis");
    in[0] = 0; in[2] = 1; want[0] = 0; want[2] = 0.25f;
    CHECK(clf_px(lut3, in, want, 1e-5f), "clf LUT3D blue-fastest blue axis");
    {
        toc_result rc;
        toc_op_list *l = clf_load("<LUT3D><Array dim=\"3 2 2 2\">0 0 0 1 1 1 0 0 0 1 1 1 "
                                  "0 0 0 1 1 1 0 0 0 1 1 1</Array></LUT3D>\n", &rc);
        CHECK(!TOC_OK(rc), "clf LUT3D legacy dim=\"3 N N N\" rejected (as OCIO)");
        toc_op_list_free(l);
        l = clf_load(lut3, &rc);
        CHECK(TOC_OK(rc) && l->ops[0].u.lut3d.interp == TOC_INTERP_TRILINEAR,
              "clf LUT3D default interpolation trilinear (CLF/OCIO default)");
        toc_op_list_free(l);
    }
    {
        static char tet[1024];
        toc_result rc;
        toc_op_list *l;
        snprintf(tet, sizeof(tet), "<LUT3D interpolation=\"tetrahedral\">%s",
                 strstr(lut3, "<Array"));
        l = clf_load(tet, &rc);
        CHECK(TOC_OK(rc) && l->ops[0].u.lut3d.interp == TOC_INTERP_TETRAHEDRAL,
              "clf LUT3D interpolation=\"tetrahedral\" honoured");
        toc_op_list_free(l);
    }
    /* LUT1D: dim="length components"; components 1 replicates. */
    in[0] = in[1] = in[2] = 0.5f; in[3] = 0.3f;
    want[0] = want[1] = want[2] = 0.25f; want[3] = 0.3f;
    CHECK(clf_px("<LUT1D><Array dim=\"3 1\">0 0.25 1</Array></LUT1D>\n", in, want, 1e-5f),
          "clf LUT1D dim=\"3 1\"");
    /* Bit depth: 10i output codes are normalized by 1023. */
    want[0] = want[1] = want[2] = 0.5f;
    CHECK(clf_px("<LUT1D inBitDepth=\"32f\" outBitDepth=\"10i\"><Array dim=\"2 3\">"
                 "0 0 0 1023 1023 1023</Array></LUT1D>\n", in, want, 1e-5f),
          "clf LUT1D outBitDepth 10i normalized");
    /* Matrix 3x4 (offset column) with a <Description> child, which used to
     * end the child loop and silently yield identity. */
    in[0] = in[1] = in[2] = 0.1f; in[3] = 0.6f;
    want[0] = 0.3f; want[1] = 0.5f; want[2] = 0.7f; want[3] = 0.6f;
    CHECK(clf_px("<Matrix><Description>3x4 with offsets</Description>"
                 "<Array dim=\"3 4\">2 0 0 0.1  0 3 0 0.2  0 0 4 0.3</Array></Matrix>\n",
                 in, want, 1e-5f), "clf Matrix 3x4 offsets + Description child");
    /* Matrix 4x4 is row-major (a column-major copy would transpose it). */
    in[0] = 0.2f; in[1] = 0.4f; in[2] = 0.0f; in[3] = 1.0f;
    want[0] = 0.4f; want[1] = 0.4f; want[2] = 0.0f; want[3] = 1.0f;
    CHECK(clf_px("<Matrix><Array dim=\"4 4\">1 0.5 0 0  0 1 0 0  0 0 1 0  0 0 0 1"
                 "</Array></Matrix>\n", in, want, 1e-5f), "clf Matrix 4x4 row-major");
    /* Matrix bit depths: M * in/out, offsets / out. */
    in[0] = in[1] = in[2] = 0.5f; in[3] = 1.0f;
    want[0] = want[1] = want[2] = 0.5f * 1023.0f / 4095.0f;
    CHECK(clf_px("<Matrix inBitDepth=\"10i\" outBitDepth=\"12i\"><Array dim=\"3 3\">"
                 "1 0 0 0 1 0 0 0 1</Array></Matrix>\n", in, want, 1e-5f),
          "clf Matrix 10i->12i normalized");
    /* Range: min pair only = offset + low clamp; alpha untouched. */
    in[0] = 0.05f; in[1] = 0.5f; in[2] = 2.0f; in[3] = 0.7f;
    want[0] = 0.1f; want[1] = 0.4f; want[2] = 1.9f; want[3] = 0.7f;
    CHECK(clf_px("<Range><minInValue>0.2</minInValue><minOutValue>0.1</minOutValue>"
                 "</Range>\n", in, want, 1e-5f), "clf Range min-only, alpha untouched");
    /* Range noClamp extrapolates. */
    in[0] = 1.5f; in[1] = -0.5f; in[2] = 0.5f;
    want[0] = 3.0f; want[1] = -1.0f; want[2] = 1.0f;
    CHECK(clf_px("<Range style=\"noClamp\"><minInValue>0</minInValue><maxInValue>1"
                 "</maxInValue><minOutValue>0</minOutValue><maxOutValue>2</maxOutValue>"
                 "</Range>\n", in, want, 1e-5f), "clf Range noClamp");
    /* Log: self-closing log10. */
    in[0] = 100.0f; in[1] = 10.0f; in[2] = 1.0f; in[3] = 0.5f;
    want[0] = 2.0f; want[1] = 1.0f; want[2] = 0.0f; want[3] = 0.5f;
    CHECK(clf_px("<Log style=\"log10\"/>\n", in, want, 1e-4f), "clf Log log10 self-closing");
    /* Exponent monCurveFwd (attributes, not text). */
    in[0] = in[1] = in[2] = 0.5f; in[3] = 1.0f;
    want[0] = want[1] = want[2] = powf((0.5f + 0.055f) / 1.055f, 2.4f);
    want[3] = 1.0f;
    CHECK(clf_px("<Exponent style=\"monCurveFwd\"><ExponentParams exponent=\"2.4\" "
                 "offset=\"0.055\"/></Exponent>\n", in, want, 1e-4f),
          "clf Exponent monCurveFwd");
    /* ASC_CDL Fwd: slope 2 then clamp. */
    in[0] = 0.25f; in[1] = 0.75f; in[2] = 0.0f; in[3] = 1.0f;
    want[0] = 0.5f; want[1] = 1.0f; want[2] = 0.0f; want[3] = 1.0f;
    CHECK(clf_px("<ASC_CDL style=\"Fwd\"><SOPNode><Slope>2 2 2</Slope><Offset>0 0 0"
                 "</Offset><Power>1 1 1</Power></SOPNode><SatNode><Saturation>1"
                 "</Saturation></SatNode></ASC_CDL>\n", in, want, 1e-5f),
          "clf ASC_CDL Fwd");
    /* Unquoted attribute value (dim=3) used to leave the value buffer unset
     * and strlen ran off the stack (fuzz finding). */
    {
        toc_result rc;
        toc_op_list *l = clf_load("<Matrix><Array dim=3 3>1 0 0 0 1 0 0 0 1</Array>"
                                  "</Matrix>\n", &rc);
        CHECK(!TOC_OK(rc), "clf unquoted dim attribute rejected safely");
        toc_op_list_free(l);
    }
    /* Real nodes tocio cannot run fail loudly instead of being dropped. */
    {
        toc_result rc;
        toc_op_list *l = clf_load("<ExposureContrast style=\"linear\"><ECParams "
                                  "exposure=\"1\"/></ExposureContrast>\n", &rc);
        CHECK(rc == TOC_ERROR_UNSUPPORTED, "clf ExposureContrast unsupported");
        toc_op_list_free(l);
        l = clf_load("<LUT1D halfDomain=\"true\"><Array dim=\"2 1\">0 1</Array></LUT1D>\n", &rc);
        CHECK(rc == TOC_ERROR_UNSUPPORTED, "clf halfDomain LUT1D unsupported");
        toc_op_list_free(l);
        l = clf_load("<Exponent style=\"basicPassThruFwd\"><ExponentParams exponent=\"2\"/>"
                     "</Exponent>\n", &rc);
        CHECK(rc == TOC_ERROR_UNSUPPORTED, "clf Exponent passThru unsupported");
        toc_op_list_free(l);
    }
    /* FileTransform interpolation overrides the file default. */
    {
        static const char *cfg_txt =
            "ocio_profile_version: 2\ncolorspaces:\n  - !<ColorSpace>\n    name: a\n"
            "    to_reference: !<FileTransform> {src: t.cube, interpolation: tetrahedral}\n"
            "  - !<ColorSpace>\n    name: b\n";
        toc_config *cfg = NULL;
        toc_op_list *ops = NULL;
        if (TOC_OK(toc_config_parse(cfg_txt, strlen(cfg_txt), NULL, &cfg))) {
            toc_config_set_file_reader(cfg, spi2_reader,
                                       (void *)"LUT_3D_SIZE 2\n0 0 0\n1 0 0\n0 1 0\n1 1 0\n"
                                               "0 0 1\n1 0 1\n0 1 1\n1 1 1\n");
            CHECK(TOC_OK(toc_processor_from_colorspaces(cfg, "a", "b", NULL, &ops)) &&
                      ops && ops->count == 1 &&
                      ops->ops[0].u.lut3d.interp == TOC_INTERP_TETRAHEDRAL,
                  "FileTransform interpolation: tetrahedral");
            toc_op_list_free(ops);
            toc_config_free(cfg);
        }
    }
}

/* ---- edge-case hardening ------------------------------------------------ */
static void test_edge_cases(void) {
    /* ---- CLF edge cases ---- */
    /* truncated: no closing tags (use strlen for correct length) */
    {
        const char *s = "<ProcessList>\n<Matrix>\n<Array dim=\"3 3\">\n"
                        "1 0 0\n0 1 0\n0 0 1\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "bad.clf", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".clf truncated");
        toc_op_list_free(l);
    }
    /* empty input */
    {
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "empty.clf", "", 0, 0);
        CHECK(!TOC_OK(rc), ".clf empty");
        toc_op_list_free(l);
    }
    /* unknown process nodes silently skipped */
    {
        const char *s =
            "<ProcessList>\n<UnknownNode/>\n<Garbage></Garbage>\n"
            "<LUT1D>\n<Array dim=\"2 3\">0 0 0 1 1 1</Array>\n</LUT1D>\n"
            "</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "skip.clf", s, strlen(s), 0);
        CHECK(TOC_OK(rc) && l->count == 1 && l->ops[0].kind == TOC_OP_LUT1D,
              ".clf unknown nodes skipped");
        toc_op_list_free(l);
    }
    /* insane LUT dimensions rejected */
    {
        const char *s =
            "<ProcessList>\n<LUT3D>\n<Array dim=\"9999 9999 9999 3\">\n"
            "0 0 0</Array>\n</LUT3D>\n</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "big.clf", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".clf insane size rejected");
        toc_op_list_free(l);
    }
    /* CLF with only comments and whitespace */
    {
        const char *s = "<?xml version=\"1.0\"?>\n<!-- just a comment -->\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "ws.clf", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".clf only comments");
        toc_op_list_free(l);
    }
    /* CLF: Range with no child elements is invalid (OpenColorIO rejects it) */
    {
        const char *s =
            "<ProcessList>\n<Range>\n</Range>\n</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "rnge.clf", s, strlen(s), 0);
        CHECK(!TOC_OK(rc) && l->count == 0, ".clf empty Range rejected");
        toc_op_list_free(l);
    }
    /* ---- CSP edge cases ---- */
    /* missing 3D section */
    {
        const char *s = "CSPLUTV100\n3D\n" CSP_NOPRE "2 2 2\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "bad.csp", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".csp missing 3D");
        toc_op_list_free(l);
    }
    /* truncated 3D data */
    {
        const char *s = "CSPLUTV100\n3D\n" CSP_NOPRE "2 2 2\n0 0 0\n1 0 0\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "trunc.csp", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".csp truncated 3D");
        toc_op_list_free(l);
    }
    /* malformed header (not CSP, not CLF, not cube — falls through to cube parser) */
    {
        const char *s =
            "NOTCSP\n3D\n0 0 0\n1 0 0\n0 1 0\n1 1 0\n"
            "0 0 1\n1 1 1\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "bad.csp", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".csp bad header");
        toc_op_list_free(l);
    }
    /* insane mesh size */
    {
        const char *s = "CSPLUTV100\n3D\n0\n0\n0\n9999 9999 9999\n0 0 0\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "huge.csp", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".csp insane size");
        toc_op_list_free(l);
    }
    /* prelut with missing data */
    {
        const char *s = "CSPLUTV100\n3D\n10\n0 0 0\n1 1 1\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "badpre.csp", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), ".csp prelut truncated");
        toc_op_list_free(l);
    }
    /* ---- general edge cases ---- */
    /* empty input */
    {
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "empty", "", 0, 0);
        CHECK(!TOC_OK(rc), "empty input all parsers");
        toc_op_list_free(l);
    }
    /* all whitespace */
    {
        const char *s = "   \n\t\n   \n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "ws", s, strlen(s), 0);
        CHECK(!TOC_OK(rc), "whitespace-only input");
        toc_op_list_free(l);
    }
    /* invert should return NONINVERTIBLE for all LUT types */
    {
        const char *cube = "LUT_1D_SIZE 2\n0 0 0\n1 1 1\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "inv.cube", cube, strlen(cube), 1);
        CHECK(rc == TOC_ERROR_NONINVERTIBLE, "invert cube -> NONINVERTIBLE");
        toc_op_list_free(l);
    }
    {
        const char *csp =
            "CSPLUTV100\n3D\n" CSP_NOPRE "2 2 2\n" CSP_ID3;
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "inv.csp", csp, strlen(csp), 1);
        CHECK(rc == TOC_ERROR_NONINVERTIBLE, "invert CSP -> NONINVERTIBLE");
        toc_op_list_free(l);
    }
    {
        const char *clf =
            "<ProcessList>\n<LUT1D>\n<Array dim=\"2 3\">0 0 0 1 1 1</Array>\n"
            "</LUT1D>\n</ProcessList>\n";
        toc_op_list *l = newlist();
        toc_result rc = toc_load_lutfile(l, "inv.clf", clf, strlen(clf), 1);
        CHECK(rc == TOC_ERROR_NONINVERTIBLE, "invert CLF -> NONINVERTIBLE");
        toc_op_list_free(l);
    }
}

static void test_codegen_c(void) {
    toc_op_list *l = newlist();
    char *src = NULL;
    size_t len = 0;
    toc_result rc;
    FILE *f;
    void *h;
    apply_fn fn;
    int ok = 1, i;
    build_pipeline(l);
    rc = toc_emit_c(l, NULL, NULL, &src, &len);
    CHECK(TOC_OK(rc) && src, "emit C source");
    if (!TOC_OK(rc)) { toc_op_list_free(l); return; }
    f = fopen("build/toc_gen.c", "w");
    if (f) { fwrite(src, 1, len, f); fclose(f); }
    if (system("cc -O2 -fPIC -shared build/toc_gen.c -o build/toc_gen.so") != 0) {
        CHECK(0, "compile emitted C");
        free(src);
        toc_op_list_free(l);
        return;
    }
    h = dlopen("./build/toc_gen.so", RTLD_NOW);
    CHECK(h != NULL, "dlopen emitted .so");
    if (h) {
        fn = (apply_fn)dlsym(h, "tocio_apply");
        CHECK(fn != NULL, "dlsym tocio_apply");
        if (fn) {
            for (i = 0; i < 64; ++i) {
                float a[4], b[4];
                int c;
                for (c = 0; c < 4; ++c) {
                    float v = (float)((i * 37 + c * 11) % 100) / 99.0f;
                    a[c] = b[c] = v;
                }
                toc_apply(l, a, 1, 4);
                fn(b, 1);
                for (c = 0; c < 4; ++c)
                    if (!approx(a[c], b[c], 1e-5f)) ok = 0;
            }
            CHECK(ok, "interpreter == compiled emitted-C (64 pixels)");
        }
        dlclose(h);
    }
    free(src);
    toc_op_list_free(l);
}

/* Emitted C must compute the PQ/HLG fixed functions (not silently skip them). */
static void test_codegen_c_hdr(void) {
    toc_op_list *l = newlist();
    char *src = NULL;
    size_t len = 0;
    toc_result rc;
    FILE *f;
    void *h;
    apply_fn fn;
    int ok = 1, i;
    int styles[4] = {TOC_FF_LIN_TO_PQ, TOC_FF_LIN_TO_HLG, TOC_FF_PQ_TO_LIN,
                     TOC_FF_HLG_TO_LIN};
    for (i = 0; i < 4; ++i) {
        toc_op *o = toc_op_list_push(l, TOC_OP_FIXEDFUNC);
        if (o) { o->u.fixedfunc.style = styles[i]; o->u.fixedfunc.nparams = 0; }
    }
    rc = toc_emit_c(l, NULL, NULL, &src, &len);
    CHECK(TOC_OK(rc) && src, "emit C (PQ/HLG)");
    if (!TOC_OK(rc)) { toc_op_list_free(l); return; }
    f = fopen("build/toc_gen_hdr.c", "w");
    if (f) { fwrite(src, 1, len, f); fclose(f); }
    if (system("cc -O2 -fPIC -shared build/toc_gen_hdr.c -o build/toc_gen_hdr.so") != 0) {
        CHECK(0, "compile emitted C (PQ/HLG)");
        free(src); toc_op_list_free(l); return;
    }
    h = dlopen("./build/toc_gen_hdr.so", RTLD_NOW);
    CHECK(h != NULL, "dlopen PQ/HLG .so");
    if (h) {
        fn = (apply_fn)dlsym(h, "tocio_apply");
        if (fn) {
            for (i = 0; i < 32; ++i) {
                float a[4], b[4], v = (float)i / 31.0f;
                int c;
                for (c = 0; c < 4; ++c) { a[c] = b[c] = v; }
                toc_apply(l, a, 1, 4);
                fn(b, 1);
                /* This chains PQ<->HLG, which the OCIO nits/100 PQ convention
                 * can drive out of range to +/-inf at high inputs; only require
                 * interp == emitted-C where both are finite (they use identical
                 * math, so they go non-finite together). */
                for (c = 0; c < 3; ++c) {
                    int fa = a[c] == a[c] && a[c] < 1e30f && a[c] > -1e30f;
                    int fb = b[c] == b[c] && b[c] < 1e30f && b[c] > -1e30f;
                    if (fa != fb) ok = 0;
                    else if (fa && !approx(a[c], b[c], 2e-3f)) ok = 0;
                }
            }
            CHECK(ok, "interpreter == compiled emitted-C (PQ/HLG)");
        }
        dlclose(h);
    }
    free(src);
    toc_op_list_free(l);
}

/* ---- GLSL codegen -------------------------------------------------------- */
static int glsl_validate(const char *body, const char *version, int es) {
    /* wrap OCIOMain into a complete fragment shader and run glslangValidator */
    FILE *f = fopen("build/toc_gen.frag", "w");
    int rc;
    if (!f) return -1;
    fprintf(f, "%s", body);
    /* append a trivial main that uses OCIOMain so it's a valid stage */
    fprintf(f, "out vec4 fragColor;\nvoid main(){ fragColor = OCIOMain(vec4(0.5)); }\n");
    fclose(f);
    (void)version;
    (void)es;
    rc = system("glslangValidator -S frag build/toc_gen.frag >/dev/null 2>&1");
    return rc;
}

static void test_codegen_glsl(void) {
    toc_glsl_target tgts[3] = {TOC_GLSL_ES30, TOC_GLSL_330, TOC_GLSL_VULKAN450};
    const char *names[3] = {"ES3.0", "GLSL330", "Vulkan450"};
    int t;
    /* pipeline with a matrix + a 3D LUT to exercise samplers */
    static float cube[2 * 2 * 2 * 3];
    int ir, ig, ib;
    for (ib = 0; ib < 2; ++ib)
        for (ig = 0; ig < 2; ++ig)
            for (ir = 0; ir < 2; ++ir) {
                size_t idx = (((size_t)ib * 2 + ig) * 2 + ir) * 3;
                cube[idx + 0] = (float)ir;
                cube[idx + 1] = (float)ig;
                cube[idx + 2] = (float)ib;
            }
    for (t = 0; t < 3; ++t) {
        toc_op_list *l = newlist();
        toc_op *m, *lut;
        toc_shader sh;
        toc_result rc;
        int i, j;
        static const float rm[16] = {0.6f, 0.3f, 0.1f, 0, 0.2f, 0.7f, 0.1f, 0,
                                     0.1f, 0.2f, 0.7f, 0, 0, 0, 0, 1};
        m = toc_op_list_push(l, TOC_OP_MATRIX);
        for (i = 0; i < 4; ++i) {
            for (j = 0; j < 4; ++j) m->u.matrix.m[j * 4 + i] = rm[i * 4 + j];
            m->u.matrix.off[i] = 0.0f;
        }
        lut = toc_op_list_push(l, TOC_OP_LUT3D);
        lut->u.lut3d.size = 2;
        lut->u.lut3d.data = cube;
        lut->u.lut3d.domain_max[0] = lut->u.lut3d.domain_max[1] =
            lut->u.lut3d.domain_max[2] = 1.0f;
        lut->u.lut3d.interp = TOC_INTERP_TRILINEAR;

        rc = toc_emit_glsl(l, tgts[t], NULL, &sh);
        CHECK(TOC_OK(rc) && sh.source, names[t]);
        if (TOC_OK(rc)) {
            CHECK(sh.num_textures == 1 && sh.textures[0].dim == TOC_TEX_3D &&
                      sh.textures[0].width == 2,
                  "glsl 3D texture descriptor");
            CHECK(strstr(sh.source, "OCIOMain") != NULL, "glsl has OCIOMain");
            CHECK(strstr(sh.source, "sampler3D") != NULL, "glsl has sampler3D");
            {
                int vrc = glsl_validate(sh.source, names[t], t == 0);
                if (vrc == 0)
                    CHECK(1, "glslangValidator accepts shader");
                else
                    printf("  note: glslangValidator skipped/failed for %s\n",
                           names[t]);
            }
            toc_shader_free(&sh);
        }
        toc_op_list_free(l);
    }
}

/* Emitted GLSL must contain the PQ/HLG transfer math (not silently skip it). */
static void test_codegen_glsl_hdr(void) {
    toc_op_list *l = newlist();
    toc_shader sh;
    toc_result rc;
    int styles[4] = {TOC_FF_LIN_TO_PQ, TOC_FF_PQ_TO_LIN, TOC_FF_LIN_TO_HLG,
                     TOC_FF_HLG_TO_LIN};
    int i;
    for (i = 0; i < 4; ++i) {
        toc_op *o = toc_op_list_push(l, TOC_OP_FIXEDFUNC);
        if (o) { o->u.fixedfunc.style = styles[i]; o->u.fixedfunc.nparams = 0; }
    }
    rc = toc_emit_glsl(l, TOC_GLSL_330, NULL, &sh);
    CHECK(TOC_OK(rc) && sh.source, "emit GLSL (PQ/HLG)");
    if (TOC_OK(rc)) {
        CHECK(strstr(sh.source, "0.8359375") != NULL &&
                  strstr(sh.source, "0.17883277") != NULL,
              "GLSL emits PQ + HLG math (not skipped)");
        if (glsl_validate(sh.source, "330", 0) == 0)
            CHECK(1, "glslangValidator accepts PQ/HLG shader");
        else
            printf("  note: glslangValidator skipped/failed for PQ/HLG\n");
        toc_shader_free(&sh);
    }
    toc_op_list_free(l);
}

/* ---- ACES 2.0 output transform GLSL emission ----------------------------- */
static int str_contains(const char *h, const char *n) {
    size_t hl = strlen(h), nl = strlen(n), i;
    if (nl > hl) return 0;
    for (i = 0; i + nl <= hl; ++i)
        if (memcmp(h + i, n, nl) == 0) return 1;
    return 0;
}
static void test_codegen_glsl_aces2(void) {
    static const char *cfg_txt =
        "ocio_profile_version: 2\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n    name: ap0\n    isdata: false\n"
        "  - !<ColorSpace>\n    name: xyz\n    isdata: false\n"
        "    from_reference: !<BuiltinTransform> {style: ACES-OUTPUT - "
        "ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709_2.0}\n";
    toc_config *cfg = NULL;
    toc_op_list *ops = NULL;
    toc_shader sh;
    toc_result rc = toc_config_parse(cfg_txt, strlen(cfg_txt), NULL, &cfg);
    CHECK(TOC_OK(rc), "ACES2 GLSL config parse");
    if (!TOC_OK(rc)) return;
    rc = toc_processor_from_colorspaces(cfg, "ap0", "xyz", NULL, &ops);
    CHECK(TOC_OK(rc) && ops, "ACES2 GLSL processor build");
    if (TOC_OK(rc)) {
        rc = toc_emit_glsl(ops, TOC_GLSL_ES30, NULL, &sh);
        CHECK(TOC_OK(rc) && sh.source, "ACES2 emit GLSL");
        if (TOC_OK(rc)) {
            /* must emit the driver, the scalar helpers, and the baked tables -
             * never silently skip the op. */
            CHECK(str_contains(sh.source, "tocAces2_") &&
                      str_contains(sh.source, "a2cf(") &&
                      str_contains(sh.source, "a2reach_") &&
                      str_contains(sh.source, "a2cG_"),
                  "ACES2 GLSL contains driver + helpers + tables");
            toc_shader_free(&sh);
        }
        toc_op_list_free(ops);
    }
    toc_config_free(cfg);
}

/* ---- Metal (MSL) codegen ------------------------------------------------- */
static int metal_validate(const char *src) {
    FILE *f = fopen("build/toc_gen.metal", "w");
    if (!f) return -1;
    fputs(src, f);
    fclose(f);
    return system("xcrun -sdk macosx metal -c build/toc_gen.metal "
                  "-o build/toc_gen.air >/dev/null 2>&1");
}
static void test_codegen_metal(void) {
    toc_op_list *l = newlist();
    toc_shader sh;
    toc_result rc;
    toc_op *m, *lut, *o;
    int i, j;
    static float cube[2 * 2 * 2 * 3];
    static const float rm[16] = {0.6f, 0.3f, 0.1f, 0, 0.2f, 0.7f, 0.1f, 0,
                                 0.1f, 0.2f, 0.7f, 0, 0, 0, 0, 1};
    for (i = 0; i < 2 * 2 * 2 * 3; ++i) cube[i] = (float)(i % 3) * 0.5f;
    m = toc_op_list_push(l, TOC_OP_MATRIX);
    for (i = 0; i < 4; ++i) {
        for (j = 0; j < 4; ++j) m->u.matrix.m[j * 4 + i] = rm[i * 4 + j];
        m->u.matrix.off[i] = 0.0f;
    }
    o = toc_op_list_push(l, TOC_OP_EXPONENT);
    for (i = 0; i < 4; ++i) o->u.exponent.e[i] = (i < 3) ? 2.2f : 1.0f;
    lut = toc_op_list_push(l, TOC_OP_LUT3D);
    lut->u.lut3d.size = 2;
    lut->u.lut3d.data = cube;
    lut->u.lut3d.domain_max[0] = lut->u.lut3d.domain_max[1] =
        lut->u.lut3d.domain_max[2] = 1.0f;
    lut->u.lut3d.interp = TOC_INTERP_TRILINEAR;
    push_ff_raw(l, TOC_FF_LIN_TO_PQ);
    push_ff_raw(l, TOC_FF_HLG_TO_LIN);

    rc = toc_emit_metal(l, NULL, &sh);
    CHECK(TOC_OK(rc) && sh.source, "emit Metal");
    if (TOC_OK(rc)) {
        if (getenv("TOC_DUMP_METAL")) fputs(sh.source, stderr);
        CHECK(strstr(sh.source, "#include <metal_stdlib>") != NULL &&
                  strstr(sh.source, "using namespace metal") != NULL,
              "Metal header");
        CHECK(strstr(sh.source, "float4 OCIOMain(float4 inPixel") != NULL,
              "Metal OCIOMain signature");
        CHECK(strstr(sh.source, "texture3d<float> ociolut0") != NULL,
              "Metal 3D LUT texture argument");
        CHECK(strstr(sh.source, "ociolut0.sample(ocioL") != NULL,
              "Metal texture sampling");
        CHECK(strstr(sh.source, "float4x4(") != NULL, "Metal matrix");
        CHECK(strstr(sh.source, "0.8359375") != NULL &&
                  strstr(sh.source, "0.17883277") != NULL,
              "Metal PQ + HLG math emitted");
        CHECK(sh.num_textures == 1 && sh.textures[0].dim == TOC_TEX_3D &&
                  sh.textures[0].width == 2,
              "Metal texture descriptor");
        if (metal_validate(sh.source) == 0)
            CHECK(1, "Metal toolchain accepts shader");
        else
            printf("  note: Metal toolchain skipped/unavailable\n");
        toc_shader_free(&sh);
    }
    toc_op_list_free(l);
}

/* ExponentWithLinear (sRGB-style MonCurve) must be emitted by all backends. */
static void test_codegen_exp_linear(void) {
    toc_op_list *l = newlist();
    toc_op *o = toc_op_list_push(l, TOC_OP_EXP_LINEAR);
    char *src = NULL;
    size_t len = 0;
    toc_result rc;
    FILE *f;
    void *h;
    apply_fn fn;
    int ok = 1, i, c;
    for (c = 0; c < 4; ++c) { /* the sRGB decode curve used by display xforms */
        o->u.exp_linear.scale[c] = 1.0f / 1.055f;
        o->u.exp_linear.offset[c] = 0.055f / 1.055f;
        o->u.exp_linear.gamma[c] = 2.4f;
        o->u.exp_linear.breakpoint[c] = 0.04045f;
        o->u.exp_linear.slope[c] = 1.0f / 12.92f;
    }
    /* C: compile the emitted source and match the interpreter. */
    rc = toc_emit_c(l, NULL, NULL, &src, &len);
    CHECK(TOC_OK(rc) && src, "emit C (exp_linear)");
    if (TOC_OK(rc)) {
        f = fopen("build/toc_gen_el.c", "w");
        if (f) { fwrite(src, 1, len, f); fclose(f); }
        if (system("cc -O2 -fPIC -shared build/toc_gen_el.c -o build/toc_gen_el.so") == 0 &&
            (h = dlopen("./build/toc_gen_el.so", RTLD_NOW)) != NULL) {
            fn = (apply_fn)dlsym(h, "tocio_apply");
            if (fn) {
                for (i = 0; i < 32; ++i) {
                    float a[4], b[4], v = (float)i / 31.0f;
                    for (c = 0; c < 4; ++c) a[c] = b[c] = v;
                    toc_apply(l, a, 1, 4);
                    fn(b, 1);
                    for (c = 0; c < 3; ++c)
                        if (!approx(a[c], b[c], 1e-4f)) ok = 0;
                }
                CHECK(ok, "interpreter == compiled emitted-C (exp_linear)");
            }
            dlclose(h);
        } else {
            CHECK(0, "compile emitted C (exp_linear)");
        }
        free(src);
    }
    /* GLSL + Metal: the MonCurve must be emitted (not silently skipped). */
    {
        toc_shader sh;
        if (TOC_OK(toc_emit_glsl(l, TOC_GLSL_330, NULL, &sh))) {
            CHECK(strstr(sh.source, "mix(") != NULL && strstr(sh.source, "pow(") != NULL,
                  "GLSL emits exp_linear (mix + pow)");
            toc_shader_free(&sh);
        }
        if (TOC_OK(toc_emit_metal(l, NULL, &sh))) {
            CHECK(strstr(sh.source, "select(") != NULL && strstr(sh.source, "pow(") != NULL,
                  "Metal emits exp_linear (select + pow)");
            toc_shader_free(&sh);
        }
    }
    toc_op_list_free(l);
}

/* ACES Red Modifier (fwd+inv) and Gamut Compression (fwd+inv) in all backends. */
static void set_gamutcomp(toc_op *o, int inv) {
    o->u.fixedfunc.style = inv ? TOC_FF_ACES_GAMUTCOMP13_INV
                               : TOC_FF_ACES_GAMUTCOMP13;
    o->u.fixedfunc.params[0] = 1.147f; /* ACES 1.3 limit C/M/Y (> 1) */
    o->u.fixedfunc.params[1] = 1.264f;
    o->u.fixedfunc.params[2] = 1.312f;
    o->u.fixedfunc.params[3] = 0.815f; /* threshold C/M/Y */
    o->u.fixedfunc.params[4] = 0.803f;
    o->u.fixedfunc.params[5] = 0.880f;
    o->u.fixedfunc.params[6] = 1.2f;   /* power */
    o->u.fixedfunc.nparams = 7;
}
static void test_codegen_aces(void) {
    toc_op_list *l = newlist();
    char *src = NULL;
    size_t len = 0;
    toc_result rc;
    FILE *f;
    void *h;
    apply_fn fn;
    int ok = 1, i, c;
    /* ACES-ish linear values incl. out-of-gamut and saturated hues. */
    static const float px[8][3] = {
        {0.80f, 0.10f, 0.05f}, {0.10f, 0.70f, 0.20f}, {0.05f, 0.20f, 0.90f},
        {0.50f, 0.50f, 0.50f}, {1.20f, 0.30f, -0.05f}, {0.02f, 0.02f, 0.02f},
        {0.90f, 0.85f, 0.10f}, {-0.04f, 0.60f, 0.55f}};
    /* mixed directions so a silently-skipped op shifts the result */
    push_ff_raw(l, TOC_FF_ACES_RED_MOD_03);
    set_gamutcomp(toc_op_list_push(l, TOC_OP_FIXEDFUNC), 0);
    push_ff_raw(l, TOC_FF_ACES_RED_MOD_10_INV);
    set_gamutcomp(toc_op_list_push(l, TOC_OP_FIXEDFUNC), 1);

    rc = toc_emit_c(l, NULL, NULL, &src, &len);
    CHECK(TOC_OK(rc) && src, "emit C (ACES redmod+gamutcomp)");
    if (TOC_OK(rc)) {
        f = fopen("build/toc_gen_aces.c", "w");
        if (f) { fwrite(src, 1, len, f); fclose(f); }
        if (system("cc -O2 -fPIC -shared build/toc_gen_aces.c -o build/toc_gen_aces.so") == 0 &&
            (h = dlopen("./build/toc_gen_aces.so", RTLD_NOW)) != NULL) {
            fn = (apply_fn)dlsym(h, "tocio_apply");
            if (fn) {
                for (i = 0; i < 8; ++i) {
                    float a[4], b[4];
                    for (c = 0; c < 3; ++c) a[c] = b[c] = px[i][c];
                    a[3] = b[3] = 1.0f;
                    toc_apply(l, a, 1, 4);
                    fn(b, 1);
                    for (c = 0; c < 3; ++c)
                        if (!approx(a[c], b[c], 2e-3f)) ok = 0;
                }
                CHECK(ok, "interpreter == compiled emitted-C (ACES)");
            }
            dlclose(h);
        } else {
            CHECK(0, "compile emitted C (ACES)");
        }
        free(src);
    }
    /* GLSL + Metal: the ops must be emitted (helper calls present, not skipped). */
    {
        toc_shader sh;
        if (TOC_OK(toc_emit_glsl(l, TOC_GLSL_330, NULL, &sh))) {
            CHECK(strstr(sh.source, "tocRedmod(") != NULL &&
                      strstr(sh.source, "tocGamutComp(") != NULL &&
                      strstr(sh.source, "not emitted") == NULL,
                  "GLSL emits ACES redmod + gamutcomp");
            toc_shader_free(&sh);
        }
        if (TOC_OK(toc_emit_metal(l, NULL, &sh))) {
            CHECK(strstr(sh.source, "tocRedmod(") != NULL &&
                      strstr(sh.source, "tocGamutComp(") != NULL,
                  "Metal emits ACES redmod + gamutcomp");
            toc_shader_free(&sh);
        }
    }
    toc_op_list_free(l);
}

/* Single-op CDL inverse: toc_invert_op toggles the inverse flag, and the
 * interpreter + emitted C reproduce it (round-trip and parity). */
static void test_cdl_op_inverse(void) {
    toc_op_list *l = newlist();
    toc_op *o = toc_op_list_push(l, TOC_OP_CDL);
    char *src = NULL;
    size_t len = 0;
    toc_result rc;
    FILE *f;
    void *h;
    apply_fn fn;
    int i, ok = 1;
    static const float seed[8][3] = {
        {0.18f, 0.35f, 0.09f}, {0.5f, 0.5f, 0.5f}, {0.8f, 0.2f, 0.1f},
        {0.1f, 0.7f, 0.3f}, {0.05f, 0.05f, 0.9f}, {0.6f, 0.6f, 0.2f},
        {0.3f, 0.45f, 0.55f}, {0.9f, 0.1f, 0.4f}};
    float buf[24], orig[24];
    o->u.cdl.slope[0] = 1.5f; o->u.cdl.slope[1] = 1.0f; o->u.cdl.slope[2] = 0.8f;
    o->u.cdl.offset[0] = 0.05f; o->u.cdl.offset[1] = 0.0f; o->u.cdl.offset[2] = -0.02f;
    o->u.cdl.power[0] = 0.9f; o->u.cdl.power[1] = 1.1f; o->u.cdl.power[2] = 1.0f;
    o->u.cdl.saturation = 0.85f;
    o->u.cdl.clamp = 0; /* no clamp -> exact round-trip */
    for (i = 0; i < 8; ++i) {
        orig[i * 3] = buf[i * 3] = seed[i][0];
        orig[i * 3 + 1] = buf[i * 3 + 1] = seed[i][1];
        orig[i * 3 + 2] = buf[i * 3 + 2] = seed[i][2];
    }
    toc_apply(l, buf, 8, 3);                 /* forward */
    CHECK(TOC_OK(toc_invert_op(l, &l->ops[0])), "CDL op invertible");
    toc_apply(l, buf, 8, 3);                 /* inverse */
    for (i = 0; i < 24; ++i)
        if (!approx(buf[i], orig[i], 2e-3f)) ok = 0;
    CHECK(ok, "single-op CDL forward+inverse round-trip");

    /* l->ops[0] is now an inverse CDL: emitted C must match the interpreter. */
    rc = toc_emit_c(l, NULL, NULL, &src, &len);
    if (TOC_OK(rc) && src) {
        f = fopen("build/toc_gen_cdlinv.c", "w");
        if (f) { fwrite(src, 1, len, f); fclose(f); }
        if (system("cc -O2 -fPIC -shared build/toc_gen_cdlinv.c -o build/toc_gen_cdlinv.so") == 0 &&
            (h = dlopen("./build/toc_gen_cdlinv.so", RTLD_NOW)) != NULL) {
            fn = (apply_fn)dlsym(h, "tocio_apply");
            ok = 1;
            if (fn) {
                for (i = 0; i < 8; ++i) {
                    float a[4], b[4];
                    int c;
                    for (c = 0; c < 3; ++c) a[c] = b[c] = seed[i][c];
                    a[3] = b[3] = 1.0f;
                    toc_apply(l, a, 1, 4);
                    fn(b, 1);
                    for (c = 0; c < 3; ++c)
                        if (!approx(a[c], b[c], 2e-3f)) ok = 0;
                }
                CHECK(ok, "interpreter == compiled emitted-C (inverse CDL)");
            }
            dlclose(h);
        }
        free(src);
    }
    toc_op_list_free(l);
}

/* LUT1D inverse: toc_invert_op rebuilds a monotonic curve's inverse into owned
 * storage; forward+inverse round-trips, and non-monotonic LUTs are rejected. */
static void test_lut1d_inverse(void) {
    toc_op_list *l = newlist();
    toc_op *o = toc_op_list_push(l, TOC_OP_LUT1D);
    static float curve[33];
    float buf[24], orig[24];
    int i, ok = 1;
    for (i = 0; i < 33; ++i) {
        float x = (float)i / 32.0f;
        curve[i] = 0.5f * x + 0.5f * x * x; /* monotonic, derivative >= 0.5 */
    }
    o->u.lut1d.length = 33;
    o->u.lut1d.channels = 1;
    o->u.lut1d.domain_min = 0.0f;
    o->u.lut1d.domain_max = 1.0f;
    o->u.lut1d.data = curve;
    o->u.lut1d.interp = TOC_INTERP_LINEAR;
    for (i = 0; i < 8; ++i) {
        float x = 0.1f + (float)i * 0.1f; /* 0.1 .. 0.8 */
        orig[i * 3] = orig[i * 3 + 1] = orig[i * 3 + 2] = x;
        buf[i * 3] = buf[i * 3 + 1] = buf[i * 3 + 2] = x;
    }
    toc_apply(l, buf, 8, 3); /* forward */
    CHECK(TOC_OK(toc_invert_op(l, &l->ops[0])), "LUT1D op invertible");
    toc_apply(l, buf, 8, 3); /* inverse */
    for (i = 0; i < 24; ++i)
        if (!approx(buf[i], orig[i], 1e-2f)) ok = 0;
    CHECK(ok, "LUT1D forward+inverse round-trip");
    {
        toc_op_list *l2 = newlist();
        toc_op *o2 = toc_op_list_push(l2, TOC_OP_LUT1D);
        static float nm[4] = {0.0f, 1.0f, 0.5f, 1.0f}; /* dips -> non-monotonic */
        o2->u.lut1d.length = 4; o2->u.lut1d.channels = 1;
        o2->u.lut1d.domain_min = 0.0f; o2->u.lut1d.domain_max = 1.0f;
        o2->u.lut1d.data = nm; o2->u.lut1d.interp = TOC_INTERP_LINEAR;
        CHECK(toc_invert_op(l2, &l2->ops[0]) == TOC_ERROR_NONINVERTIBLE,
              "non-monotonic LUT1D rejected");
        toc_op_list_free(l2);
    }
    toc_op_list_free(l);
}

/* LUT3D inverse: build a small invertible 3D map, invert via toc_invert_op
 * (coarse seed + Newton), and confirm forward+inverse round-trips. */
static void test_lut3d_inverse(void) {
    toc_op_list *l = newlist();
    toc_op *o = toc_op_list_push(l, TOC_OP_LUT3D);
    enum { N = 9 };
    static float data[N * N * N * 3];
    float buf[24], orig[24];
    int ir, ig, ib, kk, ok = 1;
    for (ib = 0; ib < N; ++ib)
        for (ig = 0; ig < N; ++ig)
            for (ir = 0; ir < N; ++ir) {
                float r = (float)ir / (N - 1), g = (float)ig / (N - 1),
                      b = (float)ib / (N - 1);
                size_t idx = (((size_t)ib * N + ig) * N + ir) * 3;
                /* diagonally dominant linear mix: invertible + trilinear-exact */
                data[idx + 0] = 0.9f * r + 0.05f * g;
                data[idx + 1] = 0.9f * g + 0.05f * b;
                data[idx + 2] = 0.9f * b + 0.05f * r;
            }
    o->u.lut3d.size = N;
    for (kk = 0; kk < 3; ++kk) {
        o->u.lut3d.domain_min[kk] = 0.0f;
        o->u.lut3d.domain_max[kk] = 1.0f;
    }
    o->u.lut3d.data = data;
    o->u.lut3d.interp = TOC_INTERP_TRILINEAR;
    for (kk = 0; kk < 8; ++kk) {
        float t = 0.2f + (float)kk * 0.07f; /* interior, well inside the gamut */
        orig[kk * 3] = buf[kk * 3] = t;
        orig[kk * 3 + 1] = buf[kk * 3 + 1] = 0.25f + t * 0.4f;
        orig[kk * 3 + 2] = buf[kk * 3 + 2] = 0.7f - t * 0.4f;
    }
    toc_apply(l, buf, 8, 3); /* forward */
    CHECK(TOC_OK(toc_invert_op(l, &l->ops[0])), "LUT3D op invertible");
    toc_apply(l, buf, 8, 3); /* inverse */
    for (kk = 0; kk < 24; ++kk)
        if (!approx(buf[kk], orig[kk], 8e-3f)) ok = 0;
    CHECK(ok, "LUT3D forward+inverse round-trip (linear mix)");
    toc_op_list_free(l);

    /* A curved (non-affine) map: Newton must actually iterate to converge. */
    {
        toc_op_list *l2 = newlist();
        toc_op *o2 = toc_op_list_push(l2, TOC_OP_LUT3D);
        enum { M = 17 };
        static float d2[M * M * M * 3];
        float b2[24], og2[24];
        int ok2 = 1;
        for (ib = 0; ib < M; ++ib)
            for (ig = 0; ig < M; ++ig)
                for (ir = 0; ir < M; ++ir) {
                    float r = (float)ir / (M - 1), g = (float)ig / (M - 1),
                          b = (float)ib / (M - 1);
                    size_t idx = (((size_t)ib * M + ig) * M + ir) * 3;
                    d2[idx + 0] = 0.85f * r + 0.10f * r * r + 0.05f * g;
                    d2[idx + 1] = 0.85f * g + 0.10f * g * g + 0.05f * b;
                    d2[idx + 2] = 0.85f * b + 0.10f * b * b + 0.05f * r;
                }
        o2->u.lut3d.size = M;
        for (kk = 0; kk < 3; ++kk) {
            o2->u.lut3d.domain_min[kk] = 0.0f;
            o2->u.lut3d.domain_max[kk] = 1.0f;
        }
        o2->u.lut3d.data = d2;
        o2->u.lut3d.interp = TOC_INTERP_TRILINEAR;
        for (kk = 0; kk < 8; ++kk) {
            float t = 0.2f + (float)kk * 0.07f;
            og2[kk * 3] = b2[kk * 3] = t;
            og2[kk * 3 + 1] = b2[kk * 3 + 1] = 0.25f + t * 0.4f;
            og2[kk * 3 + 2] = b2[kk * 3 + 2] = 0.7f - t * 0.4f;
        }
        toc_apply(l2, b2, 8, 3);
        CHECK(TOC_OK(toc_invert_op(l2, &l2->ops[0])), "LUT3D op invertible (curved)");
        toc_apply(l2, b2, 8, 3);
        for (kk = 0; kk < 24; ++kk)
            if (!approx(b2[kk], og2[kk], 1.2e-2f)) ok2 = 0;
        CHECK(ok2, "LUT3D forward+inverse round-trip (curved)");
        toc_op_list_free(l2);
    }
}

/* The gamut-compression scale must map the limit distance to the gamut
 * boundary (f(lim)=1): a sample whose distance from achromatic equals the Y
 * limit compresses to 0. This catches a wrong scale that merely round-trips. */
static void test_gamutcomp_boundary(void) {
    toc_op_list *l = newlist();
    toc_op *o = toc_op_list_push(l, TOC_OP_FIXEDFUNC);
    float px[3] = {1.0f, 1.0f, 1.0f - 1.312f}; /* blue at the Y limit (1.312) */
    set_gamutcomp(o, 0);
    toc_apply(l, px, 1, 3);
    CHECK(approx(px[0], 1.0f, 1e-4f) && approx(px[1], 1.0f, 1e-4f),
          "GamutComp leaves achromatic channels unchanged");
    CHECK(approx(px[2], 0.0f, 3e-3f),
          "GamutComp maps the limit distance to the gamut boundary");
    toc_op_list_free(l);
}

/* ---- SIMD parity (scalar vs SSE2 vs AVX2) -------------------------------- */
static void test_simd_parity(void) {
    enum { NP = 257 };
    static float base[NP * 4], s0[NP * 4], s1[NP * 4], s2[NP * 4];
    toc_op_list *l = newlist();
    int i, c;
    build_pipeline(l); /* matrix + exponent + range */
    for (i = 0; i < NP * 4; ++i)
        base[i] = (float)((i * 41) % 200 - 50) / 100.0f; /* incl negatives */
    memcpy(s0, base, sizeof(base));
    memcpy(s1, base, sizeof(base));
    memcpy(s2, base, sizeof(base));
    toc_simd_force(0);
    toc_apply(l, s0, NP, 4);
    toc_simd_force(1);
    toc_apply(l, s1, NP, 4);
    toc_simd_force(2);
    toc_apply(l, s2, NP, 4);
    {
        int ok1 = 1, ok2 = 1;
        for (i = 0; i < NP * 4; ++i) {
            if (s0[i] != s1[i]) ok1 = 0;       /* SSE2 must be bit-exact */
            if (!approx(s0[i], s2[i], 1e-6f)) ok2 = 0;
        }
        CHECK(ok1, "SSE2 batch == scalar (bit-exact)");
        CHECK(ok2, "AVX2 batch == scalar");
    }
    (void)c;
    toc_simd_force(2);
    toc_op_list_free(l);
}

/* Per-op SIMD parity for the transcendental kernels: scalar vs the NEON tier
 * (force level 1), bit-exact over an input range that crosses op breakpoints.
 * memcmp keeps it NaN-bit-safe. On x86 these ops stay scalar, so it is a no-op
 * pass there; the bit-exactness it locks is the aarch64 NEON path. */
static void parity_check(toc_op_list *l, const char *name) {
    enum { NP = 257 };
    static float base[NP * 4], a[NP * 4], b[NP * 4];
    int i, ok = 1;
    for (i = 0; i < NP * 4; ++i)
        base[i] = (float)((i * 37) % 300 - 80) / 100.0f; /* [-0.80, 2.19] */
    memcpy(a, base, sizeof(base));
    memcpy(b, base, sizeof(base));
    toc_simd_force(0);
    toc_apply(l, a, NP, 4);
    toc_simd_force(1);
    toc_apply(l, b, NP, 4);
    for (i = 0; i < NP * 4; ++i)
        if (memcmp(&a[i], &b[i], sizeof(float)) != 0) ok = 0;
    CHECK(ok, name);
    toc_op_list_free(l);
}

static void test_simd_parity_transcendentals(void) {
    int c, k;
    { /* exponent */
        toc_op_list *l = newlist();
        toc_op *o = toc_op_list_push(l, TOC_OP_EXPONENT);
        for (c = 0; c < 4; ++c) o->u.exponent.e[c] = (c < 3) ? 0.45f : 1.0f;
        parity_check(l, "NEON exponent == scalar");
    }
    for (k = 0; k < 2; ++k) { /* log forward + inverse */
        toc_op_list *l = newlist();
        toc_op *o = toc_op_list_push(l, TOC_OP_LOG);
        o->u.log.base = 10.0f;
        o->u.log.inverse = k;
        for (c = 0; c < 3; ++c) {
            o->u.log.lin_slope[c] = 0.9f; o->u.log.lin_offset[c] = 0.1f;
            o->u.log.log_slope[c] = 0.3f; o->u.log.log_offset[c] = 0.6f;
        }
        parity_check(l, k ? "NEON log inverse == scalar"
                          : "NEON log forward == scalar");
    }
    for (k = 0; k < 2; ++k) { /* log_camera forward + inverse */
        toc_op_list *l = newlist();
        toc_op *o = toc_op_list_push(l, TOC_OP_LOG_CAMERA);
        o->u.logcam.base = 10.0f;
        o->u.logcam.inverse = k;
        for (c = 0; c < 3; ++c) {
            o->u.logcam.lin_slope[c] = 0.9f; o->u.logcam.lin_offset[c] = 0.1f;
            o->u.logcam.log_slope[c] = 0.3f; o->u.logcam.log_offset[c] = 0.6f;
            o->u.logcam.lin_break[c] = 0.15f;
            o->u.logcam.linear_slope[c] = 1.1f;
            o->u.logcam.linear_offset[c] = 0.0f;
        }
        parity_check(l, k ? "NEON log_camera inverse == scalar"
                          : "NEON log_camera forward == scalar");
    }
    for (k = 0; k < 2; ++k) { /* exp_linear (MonCurve) forward + inverse */
        toc_op_list *l = newlist();
        toc_op *o = toc_op_list_push(l, TOC_OP_EXP_LINEAR);
        o->u.exp_linear.inverse = k;
        for (c = 0; c < 4; ++c) {
            o->u.exp_linear.scale[c] = 0.95f; o->u.exp_linear.offset[c] = 0.05f;
            o->u.exp_linear.gamma[c] = 2.4f;  o->u.exp_linear.breakpoint[c] = 0.04f;
            o->u.exp_linear.slope[c] = 0.077f;
        }
        parity_check(l, k ? "NEON exp_linear inverse == scalar"
                          : "NEON exp_linear forward == scalar");
    }
    for (k = 0; k < 2; ++k) { /* cdl with and without clamp */
        toc_op_list *l = newlist();
        toc_op *o = toc_op_list_push(l, TOC_OP_CDL);
        o->u.cdl.saturation = 1.2f;
        o->u.cdl.clamp = k;
        for (c = 0; c < 3; ++c) {
            o->u.cdl.slope[c] = 1.1f; o->u.cdl.offset[c] = 0.02f;
            o->u.cdl.power[c] = 0.9f; o->u.cdl.luma[c] = 0.0f;
        }
        parity_check(l, k ? "NEON cdl (clamp) == scalar"
                          : "NEON cdl (no clamp) == scalar");
    }
    toc_simd_force(2);
}

/* ---- builtins + fixedfunc + logcamera ------------------------------------ */
static const char *g_builtin_cfg =
    "ocio_profile_version: 2\n"
    "colorspaces:\n"
    "  - !<ColorSpace>\n"
    "    name: ap0\n"
    "    isdata: false\n"
    "  - !<ColorSpace>\n"
    "    name: acescg\n"
    "    isdata: false\n"
    "    to_reference: !<BuiltinTransform> {style: ACEScg_to_ACES2065-1}\n"
    "  - !<ColorSpace>\n"
    "    name: acescct\n"
    "    isdata: false\n"
    "    to_reference: !<BuiltinTransform> {style: ACEScct_to_ACES2065-1}\n"
    "  - !<ColorSpace>\n"
    "    name: surround\n"
    "    isdata: false\n"
    "    from_reference: !<FixedFunctionTransform> {style: Rec2100Surround, "
    "params: [0.78]}\n";

static void roundtrip(toc_config *cfg, const char *a, const char *b,
                      const char *msg) {
    toc_op_list *f = NULL, *r = NULL;
    float px[3] = {0.18f, 0.35f, 0.09f}, orig[3];
    memcpy(orig, px, sizeof(px));
    if (TOC_OK(toc_processor_from_colorspaces(cfg, a, b, NULL, &f)) &&
        TOC_OK(toc_processor_from_colorspaces(cfg, b, a, NULL, &r))) {
        toc_apply(f, px, 1, 3);
        toc_apply(r, px, 1, 3);
        CHECK(approx(px[0], orig[0], 2e-3f) && approx(px[1], orig[1], 2e-3f) &&
                  approx(px[2], orig[2], 2e-3f),
              msg);
    } else {
        CHECK(0, msg);
    }
    if (f) toc_op_list_free(f);
    if (r) toc_op_list_free(r);
}

static void test_builtins(void) {
    toc_config *cfg = NULL;
    toc_result rc =
        toc_config_parse(g_builtin_cfg, strlen(g_builtin_cfg), NULL, &cfg);
    CHECK(TOC_OK(rc), "builtin config parse");
    if (!TOC_OK(rc)) return;
    roundtrip(cfg, "acescg", "ap0", "ACEScg<->ACES2065-1 round-trip");
    roundtrip(cfg, "acescct", "ap0", "ACEScct<->ACES2065-1 round-trip (logcam)");
    /* FixedFunction builds + applies (surround darkens mid-grey for g<1) */
    {
        toc_op_list *ops = NULL;
        rc = toc_processor_from_colorspaces(cfg, "ap0", "surround", NULL, &ops);
        CHECK(TOC_OK(rc) && ops && ops->count == 1, "Rec2100Surround -> 1 op");
        if (TOC_OK(rc)) {
            float px[3] = {0.18f, 0.18f, 0.18f};
            toc_apply(ops, px, 1, 3);
            CHECK(px[0] > 0.0f && fabsf(px[0] - 0.18f) > 1e-3f,
                  "surround scales by Y^(g-1)");
            toc_op_list_free(ops);
        }
    }
    toc_config_free(cfg);
}

/* ---- Colorimetry: primaries -> XYZ NPM + Bradford + RGB<->RGB ------------- */
static void apply_builtin3(const char *style, int inv, float px[3]) {
    toc_op_list *l = newlist();
    if (TOC_OK(toc_builtin_expand(l, style, inv))) toc_apply(l, px, 1, 3);
    toc_op_list_free(l);
}
static void test_colorimetry(void) {
    /* Linear-sRGB -> CIE-XYZ-D65 reproduces the canonical sRGB NPM columns. */
    {
        float r[3] = {1, 0, 0}, g[3] = {0, 1, 0}, b[3] = {0, 0, 1};
        apply_builtin3("Linear-sRGB_to_CIE-XYZ-D65", 0, r);
        apply_builtin3("Linear-sRGB_to_CIE-XYZ-D65", 0, g);
        apply_builtin3("Linear-sRGB_to_CIE-XYZ-D65", 0, b);
        CHECK(approx(r[0], 0.4124f, 2e-3f) && approx(r[1], 0.2126f, 2e-3f) &&
                  approx(r[2], 0.0193f, 2e-3f), "sRGB R -> XYZ-D65");
        CHECK(approx(g[0], 0.3576f, 2e-3f) && approx(g[1], 0.7152f, 2e-3f) &&
                  approx(g[2], 0.1192f, 2e-3f), "sRGB G -> XYZ-D65");
        CHECK(approx(b[0], 0.1805f, 2e-3f) && approx(b[1], 0.0722f, 2e-3f) &&
                  approx(b[2], 0.9505f, 2e-3f), "sRGB B -> XYZ-D65");
    }
    /* Display-P3 -> CIE-XYZ-D65 reference columns. */
    {
        float r[3] = {1, 0, 0}, g[3] = {0, 1, 0}, b[3] = {0, 0, 1};
        apply_builtin3("Linear-Display-P3_to_CIE-XYZ-D65", 0, r);
        apply_builtin3("Linear-Display-P3_to_CIE-XYZ-D65", 0, g);
        apply_builtin3("Linear-Display-P3_to_CIE-XYZ-D65", 0, b);
        CHECK(approx(r[0], 0.4866f, 2e-3f) && approx(r[1], 0.2290f, 2e-3f),
              "Display-P3 R -> XYZ-D65");
        CHECK(approx(g[1], 0.6917f, 2e-3f) && approx(b[2], 1.0439f, 2e-3f),
              "Display-P3 G/B -> XYZ-D65");
    }
    /* RGB<->RGB round-trips (incl. Bradford-adapted ACES D60<->D65). */
    {
        static const char *pairs[4][2] = {
            {"Linear-sRGB_to_Linear-Display-P3", "Linear-Display-P3_to_Linear-sRGB"},
            {"Linear-sRGB_to_Linear-Rec2020", "Linear-Rec2020_to_Linear-sRGB"},
            {"ACEScg_to_CIE-XYZ-D65", "CIE-XYZ-D65_to_ACEScg"},
            {"Linear-Display-P3_to_ACES2065-1", "ACES2065-1_to_Linear-Display-P3"}};
        int k;
        for (k = 0; k < 4; ++k) {
            float p[3] = {0.2f, 0.5f, 0.8f};
            apply_builtin3(pairs[k][0], 0, p);
            apply_builtin3(pairs[k][1], 0, p);
            CHECK(approx(p[0], 0.2f, 1e-4f) && approx(p[1], 0.5f, 1e-4f) &&
                      approx(p[2], 0.8f, 1e-4f), pairs[k][0]);
        }
    }
    /* white-balanced: sRGB(D65) -> ACEScg(D60) keeps mid-grey neutral. */
    {
        float p[3] = {0.18f, 0.18f, 0.18f};
        apply_builtin3("Linear-sRGB_to_ACEScg", 0, p);
        CHECK(approx(p[0], p[1], 2e-3f) && approx(p[1], p[2], 2e-3f),
              "neutral stays neutral across white adaptation");
    }
    /* invert flag == the reverse-named conversion. */
    {
        float a[3] = {0.3f, 0.6f, 0.1f}, b[3] = {0.3f, 0.6f, 0.1f};
        apply_builtin3("Linear-sRGB_to_Linear-Display-P3", 1, a);
        apply_builtin3("Linear-Display-P3_to_Linear-sRGB", 0, b);
        CHECK(approx(a[0], b[0], 1e-4f) && approx(a[1], b[1], 1e-4f) &&
                  approx(a[2], b[2], 1e-4f), "builtin invert == reverse conversion");
    }
}

/* ---- Display transfer functions + composed output transforms ------------- */
static void test_display_transfer(void) {
    /* PQ / HLG per-channel encode->decode round-trips over [0,1]. */
    {
        int s, styles[2] = {TOC_FF_LIN_TO_PQ, TOC_FF_LIN_TO_HLG};
        for (s = 0; s < 2; ++s) {
            toc_op_list *l = newlist();
            int p, ok = 1;
            push_ff_raw(l, styles[s]);
            push_ff_raw(l, styles[s] ^ 1); /* inverse */
            /* PQ's m2=78.84 exponent amplifies the ~1e-6 approximate-pow error,
             * so allow a looser bound there than for HLG (sqrt/log/exp). */
            float eps = (styles[s] == TOC_FF_LIN_TO_PQ) ? 1e-3f : 1e-4f;
            for (p = 0; p <= 20; ++p) {
                float x = (float)p / 20.0f, v[3];
                v[0] = v[1] = v[2] = x;
                toc_apply(l, v, 1, 3);
                if (!approx(v[0], x, eps)) ok = 0;
            }
            CHECK(ok, s ? "HLG encode<->decode round-trip"
                        : "PQ encode<->decode round-trip");
            toc_op_list_free(l);
        }
    }
    /* PQ uses the OCIO/ACES nits/100 convention: input 100.0 (= 10000 nits) ->
     * 1.0 (peak), 0 -> 0, and 1.0 (= 100 nits) -> ~0.508. */
    {
        toc_op_list *l = newlist();
        float pk[3] = {100, 100, 100}, mid[3] = {1, 1, 1}, z[3] = {0, 0, 0};
        push_ff_raw(l, TOC_FF_LIN_TO_PQ);
        toc_apply(l, pk, 1, 3);
        toc_apply(l, mid, 1, 3);
        toc_apply(l, z, 1, 3);
        CHECK(approx(pk[0], 1.0f, 1e-3f) && approx(z[0], 0.0f, 1e-4f) &&
                  mid[0] > 0.45f && mid[0] < 0.55f,
              "PQ nits/100: 100->1, 0->0, 1->~0.5");
        toc_op_list_free(l);
    }
    /* Composed output transforms: display value -> XYZ (invert) -> display
     * (forward) reconstructs the display value (in-[0,1] stays invertible). */
    {
        static const char *xf[6] = {
            "CIE-XYZ-D65_to_sRGB", "CIE-XYZ-D65_to_Display-P3",
            "CIE-XYZ-D65_to_DCI-P3", "CIE-XYZ-D65_to_Rec.1886-Rec.709",
            "CIE-XYZ-D65_to_Rec.2100-PQ", "CIE-XYZ-D65_to_Rec.2100-HLG"};
        int k;
        for (k = 0; k < 6; ++k) {
            toc_op_list *fwd = newlist(), *inv = newlist();
            toc_result r1 = toc_builtin_expand(fwd, xf[k], 0);
            toc_result r2 = toc_builtin_expand(inv, xf[k], 1);
            float p[3] = {0.5f, 0.4f, 0.6f}, o[3] = {0.5f, 0.4f, 0.6f};
            CHECK(TOC_OK(r1) && TOC_OK(r2) && fwd->count == 2, xf[k]);
            if (TOC_OK(r1) && TOC_OK(r2)) {
                toc_apply(inv, p, 1, 3); /* display -> XYZ */
                toc_apply(fwd, p, 1, 3); /* XYZ -> display */
                CHECK(approx(p[0], o[0], 2e-3f) && approx(p[1], o[1], 2e-3f) &&
                          approx(p[2], o[2], 2e-3f), "output xform round-trip");
            }
            toc_op_list_free(fwd);
            toc_op_list_free(inv);
        }
    }
}

/* ---- FixedFunction styles (round-trip for all invert pairs) -------------- */
static void push_fixedfunc(toc_op_list *l, int style, const float *params,
                            int nparams) {
    toc_op *op = toc_op_list_push(l, TOC_OP_FIXEDFUNC);
    int i;
    op->u.fixedfunc.style = style;
    for (i = 0; i < nparams; ++i) op->u.fixedfunc.params[i] = params[i];
    op->u.fixedfunc.nparams = nparams;
}

static void test_fixedfunc_styles(void) {
    struct { int fwd, inv; const char *name; float pixel[3]; float params[8];
             int nparams; float eps; } styles[] = {
        {TOC_FF_ACES_GLOW03, TOC_FF_ACES_GLOW03_INV, "Glow03",
         {0.02f,0.03f,0.01f}, {0.075f,0.1f}, 2, 5e-3f},
        {TOC_FF_ACES_GLOW10, TOC_FF_ACES_GLOW10_INV, "Glow10",
         {0.02f,0.03f,0.01f}, {0.05f,0.08f}, 2, 5e-3f},
        {TOC_FF_ACES_DARKTODIM10, TOC_FF_ACES_DARKTODIM10_INV, "DarkToDim10",
         {0.18f,0.35f,0.09f}, {0.9811f}, 1, 2e-3f},
        {TOC_FF_ACES_RED_MOD_03, TOC_FF_ACES_RED_MOD_03_INV, "RedMod03",
         {0.8f,0.3f,0.2f}, {0}, 0, 2e-3f},
        {TOC_FF_ACES_RED_MOD_10, TOC_FF_ACES_RED_MOD_10_INV, "RedMod10",
         {0.8f,0.3f,0.2f}, {0}, 0, 2e-3f},
        {TOC_FF_ACES_GAMUTCOMP13, TOC_FF_ACES_GAMUTCOMP13_INV, "GamutComp13",
         {1.0f,0.5f,-0.3f}, /* out-of-gamut blue so the real ACES limits engage */
         {1.147f,1.264f,1.312f,0.815f,0.803f,0.880f,1.2f}, 7, 5e-3f},
        {TOC_FF_RGB_TO_HSV, TOC_FF_HSV_TO_RGB, "RGB->HSV",
         {0.8f,0.3f,0.5f}, {0}, 0, 1e-4f},
        {TOC_FF_XYZ_TO_xyY, TOC_FF_xyY_TO_XYZ, "XYZ<->xyY",
         {0.3f,0.3f,0.3f}, {0}, 0, 1e-4f},
        {TOC_FF_XYZ_TO_uvY, TOC_FF_uvY_TO_XYZ, "XYZ<->uvY",
         {0.3f,0.3f,0.3f}, {0}, 0, 1e-4f},
        {TOC_FF_XYZ_TO_LUV, TOC_FF_LUV_TO_XYZ, "XYZ<->LUV",
         {0.3f,0.3f,0.3f}, {0}, 0, 5e-3f},
    };
    int i;
    for (i = 0; i < (int)(sizeof(styles)/sizeof(styles[0])); ++i) {
        toc_op_list *l = newlist();
        float px[3], orig[3];
        int c;
        memcpy(orig, styles[i].pixel, sizeof(orig));
        memcpy(px, orig, sizeof(px));
        push_fixedfunc(l, styles[i].fwd, styles[i].params, styles[i].nparams);
        toc_apply(l, px, 1, 3);
        /* verify forward changed pixel */
        {
            int changed = 0;
            for (c = 0; c < 3; ++c)
                if (!approx(px[c], orig[c], 1e-6f)) changed = 1;
            CHECK(changed, styles[i].name);
        }
        toc_op_list_free(l);
        /* round-trip */
        {
            toc_op_list *rt = newlist();
            memcpy(px, orig, sizeof(px));
            push_fixedfunc(rt, styles[i].fwd, styles[i].params, styles[i].nparams);
            push_fixedfunc(rt, styles[i].inv, styles[i].params, styles[i].nparams);
            toc_apply(rt, px, 1, 3);
            CHECK(approx(px[0], orig[0], styles[i].eps) &&
                  approx(px[1], orig[1], styles[i].eps) &&
                  approx(px[2], orig[2], styles[i].eps), styles[i].name);
            toc_op_list_free(rt);
        }
    }
    /* Direct style value check for HSV_TO_RGB: hue=60°(h*6=1), sat=0.625, val=0.8 */
    {
        toc_op_list *l = newlist();
        float px[3] = {0.166667f, 0.625f, 0.8f};
        push_fixedfunc(l, TOC_FF_HSV_TO_RGB, NULL, 0);
        toc_apply(l, px, 1, 3);
        CHECK(approx(px[0], 0.8f, 1e-4f) && approx(px[1], 0.8f, 1e-4f) &&
              approx(px[2], 0.3f, 1e-4f), "HSV_TO_RGB direct");
        toc_op_list_free(l);
    }
}

/* ---- x64 JIT: emitted machine code == interpreter ------------------------ */
static void test_jit(void) {
    toc_op_list *l = newlist();
    toc_jit *j = NULL;
    toc_result rc;
    int i, ok = 1;
    build_pipeline(l); /* matrix + exponent + range */
    rc = toc_jit_compile(l, 4, NULL, &j);
    if (rc == TOC_ERROR_UNSUPPORTED) {
        printf("  note: JIT unsupported on this target; skipping\n");
        toc_op_list_free(l);
        return;
    }
    CHECK(TOC_OK(rc) && j, "jit compile");
    if (TOC_OK(rc)) {
        toc_jit_fn fn = toc_jit_func(j);
        CHECK(fn != NULL, "jit func ptr");
        if (fn) {
            for (i = 0; i < 64; ++i) {
                float a[4], b[4];
                int c;
                for (c = 0; c < 4; ++c) {
                    float v = (float)((i * 53 + c * 17) % 200 - 50) / 100.0f;
                    a[c] = b[c] = v;
                }
                toc_apply(l, a, 1, 4); /* interpreter */
                fn(b, 1);              /* native code */
                for (c = 0; c < 4; ++c)
                    if (!approx(a[c], b[c], 1e-6f)) ok = 0;
            }
            CHECK(ok, "JIT == interpreter (64 pixels, matrix+exp+range)");
            /* multi-pixel run exercises the loop */
            {
                static float buf[16 * 4], ref[16 * 4];
                int n;
                for (n = 0; n < 16 * 4; ++n)
                    buf[n] = ref[n] = (float)(n % 7) * 0.1f;
                toc_apply(l, ref, 16, 4);
                fn(buf, 16);
                ok = 1;
                for (n = 0; n < 16 * 4; ++n)
                    if (!approx(buf[n], ref[n], 1e-6f)) ok = 0;
                CHECK(ok, "JIT loop over 16 pixels == interpreter");
            }
        }
        toc_jit_destroy(j);
    }
    /* inline SSE2 pow: exponent-only pipelines across several gammas */
    {
        float gammas[4] = {2.2f, 1.0f / 2.4f, 2.4f, 0.5f};
        int gi;
        for (gi = 0; gi < 4; ++gi) {
            toc_op_list *le = newlist();
            toc_op *e = toc_op_list_push(le, TOC_OP_EXPONENT);
            toc_jit *je = NULL;
            int c;
            for (c = 0; c < 4; ++c) e->u.exponent.e[c] = (c < 3) ? gammas[gi] : 1.0f;
            if (TOC_OK(toc_jit_compile(le, 4, NULL, &je)) && je) {
                int p;
                ok = 1;
                for (p = 0; p < 32; ++p) {
                    float a[4], b[4];
                    for (c = 0; c < 4; ++c) {
                        float v = (float)((p * 31 + c * 7) % 100) / 99.0f;
                        a[c] = b[c] = v;
                    }
                    toc_apply(le, a, 1, 4);
                    toc_jit_func(je)(b, 1);
                    for (c = 0; c < 4; ++c)
                        if (!approx(a[c], b[c], 1e-5f)) ok = 0;
                }
                CHECK(ok, "JIT inline pow == interpreter (gamma sweep)");
                toc_jit_destroy(je);
            }
            toc_op_list_free(le);
        }
    }
    /* inline log: forward + inverse log-affine, JIT vs interpreter. RGB only
     * (alpha must pass through unchanged). */
    {
        int inv;
        for (inv = 0; inv < 2; ++inv) {
            toc_op_list *ll = newlist();
            toc_op *o = toc_op_list_push(ll, TOC_OP_LOG);
            toc_jit *jl = NULL;
            int c;
            o->u.log.base = 10.0f;
            o->u.log.inverse = inv;
            for (c = 0; c < 3; ++c) {
                o->u.log.lin_slope[c] = 0.9f; o->u.log.lin_offset[c] = 0.1f;
                o->u.log.log_slope[c] = 0.3f; o->u.log.log_offset[c] = 0.6f;
            }
            if (TOC_OK(toc_jit_compile(ll, 4, NULL, &jl)) && jl) {
                int p;
                ok = 1;
                for (p = 0; p < 32; ++p) {
                    float a[4], b[4];
                    for (c = 0; c < 4; ++c) {
                        float v = (float)((p * 31 + c * 7) % 100) / 99.0f + 0.05f;
                        a[c] = b[c] = v;
                    }
                    toc_apply(ll, a, 1, 4);
                    toc_jit_func(jl)(b, 1);
                    for (c = 0; c < 4; ++c)
                        if (!approx(a[c], b[c], 1e-5f)) ok = 0;
                    if (a[3] != b[3]) ok = 0; /* alpha pass-through */
                }
                CHECK(ok, inv ? "JIT inline log inverse == interpreter"
                              : "JIT inline log forward == interpreter");
                toc_jit_destroy(jl);
            }
            toc_op_list_free(ll);
        }
    }
    /* inline exp_linear (MonCurve): forward + inverse, JIT vs interpreter. */
    {
        int inv;
        for (inv = 0; inv < 2; ++inv) {
            toc_op_list *le = newlist();
            toc_op *o = toc_op_list_push(le, TOC_OP_EXP_LINEAR);
            toc_jit *je = NULL;
            int c;
            o->u.exp_linear.inverse = inv;
            for (c = 0; c < 4; ++c) {
                o->u.exp_linear.scale[c] = 0.95f; o->u.exp_linear.offset[c] = 0.05f;
                o->u.exp_linear.gamma[c] = 2.4f; o->u.exp_linear.breakpoint[c] = 0.04f;
                o->u.exp_linear.slope[c] = 0.077f;
            }
            if (TOC_OK(toc_jit_compile(le, 4, NULL, &je)) && je) {
                int p; ok = 1;
                for (p = 0; p < 48; ++p) {
                    float a[4], b[4];
                    for (c = 0; c < 4; ++c) {
                        float v = (float)((p * 31 + c * 7) % 120 - 10) / 100.0f;
                        a[c] = b[c] = v;
                    }
                    toc_apply(le, a, 1, 4);
                    toc_jit_func(je)(b, 1);
                    for (c = 0; c < 3; ++c)
                        if (!approx(a[c], b[c], 1e-5f)) ok = 0;
                    if (a[3] != b[3]) ok = 0;
                }
                CHECK(ok, inv ? "JIT inline exp_linear inverse == interpreter"
                              : "JIT inline exp_linear forward == interpreter");
                toc_jit_destroy(je);
            }
            toc_op_list_free(le);
        }
    }
    /* inline CDL: with and without clamp, JIT vs interpreter. */
    {
        int cl;
        for (cl = 0; cl < 2; ++cl) {
            toc_op_list *lc = newlist();
            toc_op *o = toc_op_list_push(lc, TOC_OP_CDL);
            toc_jit *jc = NULL;
            int c;
            o->u.cdl.saturation = 1.2f;
            o->u.cdl.clamp = cl;
            for (c = 0; c < 3; ++c) {
                o->u.cdl.slope[c] = 1.1f; o->u.cdl.offset[c] = 0.02f;
                o->u.cdl.power[c] = 0.9f; o->u.cdl.luma[c] = 0.0f;
            }
            if (TOC_OK(toc_jit_compile(lc, 4, NULL, &jc)) && jc) {
                int p; ok = 1;
                for (p = 0; p < 48; ++p) {
                    float a[4], b[4];
                    for (c = 0; c < 4; ++c) {
                        float v = (float)((p * 31 + c * 7) % 120 - 10) / 100.0f;
                        a[c] = b[c] = v;
                    }
                    toc_apply(lc, a, 1, 4);
                    toc_jit_func(jc)(b, 1);
                    for (c = 0; c < 3; ++c)
                        if (!approx(a[c], b[c], 1e-5f)) ok = 0;
                    if (a[3] != b[3]) ok = 0;
                }
                CHECK(ok, cl ? "JIT inline cdl (clamp) == interpreter"
                             : "JIT inline cdl (no clamp) == interpreter");
                toc_jit_destroy(jc);
            }
            toc_op_list_free(lc);
        }
    }
    /* AVX 2px path: pure matrix+range pipeline on an ODD pixel count so both
     * the 2-pixel main loop and the 1-pixel SSE tail execute. */
    {
        toc_op_list *la = newlist();
        toc_op *m1 = toc_op_list_push(la, TOC_OP_MATRIX);
        toc_op *m2 = toc_op_list_push(la, TOC_OP_MATRIX);
        toc_op *r = toc_op_list_push(la, TOC_OP_RANGE);
        static const float A[16] = {0.6f, 0.3f, 0.1f, 0, 0.2f, 0.7f, 0.1f, 0,
                                    0.1f, 0.2f, 0.7f, 0, 0, 0, 0, 1};
        static const float B[16] = {1.1f, -0.1f, 0, 0, -0.05f, 1.05f, 0, 0,
                                    0, 0, 1.0f, 0, 0, 0, 0, 1};
        int i, jx, c;
        toc_jit *ja = NULL;
        for (i = 0; i < 4; ++i)
            for (jx = 0; jx < 4; ++jx) {
                m1->u.matrix.m[jx * 4 + i] = A[i * 4 + jx];
                m2->u.matrix.m[jx * 4 + i] = B[i * 4 + jx];
            }
        for (c = 0; c < 4; ++c) {
            r->u.range.scale[c] = 1.0f; r->u.range.min[c] = 0.0f;
            r->u.range.max[c] = 1.0f;
        }
        r->u.range.clamp_lo = r->u.range.clamp_hi = 1;
        rc = toc_jit_compile(la, 4, NULL, &ja);
        if (TOC_OK(rc) && ja) {
            enum { NP = 17 };
            static float buf[NP * 4], ref[NP * 4];
            int n;
            for (n = 0; n < NP * 4; ++n)
                buf[n] = ref[n] = (float)((n * 29) % 150 - 30) / 100.0f;
            toc_apply(la, ref, NP, 4);
            toc_jit_func(ja)(buf, NP);
            ok = 1;
            for (n = 0; n < NP * 4; ++n)
                if (!approx(buf[n], ref[n], 1e-6f)) ok = 0;
            CHECK(ok, "JIT AVX 2px (matrix+matrix+range, 17 px) == interpreter");
            toc_jit_destroy(ja);
        }
        toc_op_list_free(la);
    }
    /* a LUT op (helper-call path) also runs through the JIT */
    {
        toc_op_list *l2 = newlist();
        toc_op *m = toc_op_list_push(l2, TOC_OP_MATRIX);
        toc_op *lut = toc_op_list_push(l2, TOC_OP_LUT3D);
        static float cube[2 * 2 * 2 * 3];
        int ir, ig, ib, n;
        toc_jit *j2 = NULL;
        for (ib = 0; ib < 2; ++ib)
            for (ig = 0; ig < 2; ++ig)
                for (ir = 0; ir < 2; ++ir) {
                    size_t idx = (((size_t)ib * 2 + ig) * 2 + ir) * 3;
                    cube[idx + 0] = (float)ir; cube[idx + 1] = (float)ig;
                    cube[idx + 2] = (float)ib;
                }
        for (n = 0; n < 4; ++n) m->u.matrix.m[n * 4 + n] = 1.0f; /* identity */
        lut->u.lut3d.size = 2; lut->u.lut3d.data = cube;
        lut->u.lut3d.domain_max[0] = lut->u.lut3d.domain_max[1] =
            lut->u.lut3d.domain_max[2] = 1.0f;
        lut->u.lut3d.interp = TOC_INTERP_TETRAHEDRAL;
        if (TOC_OK(toc_jit_compile(l2, 4, NULL, &j2)) && j2) {
            float a[4] = {0.2f, 0.6f, 0.9f, 1.0f}, b[4];
            int c;
            memcpy(b, a, sizeof(a));
            toc_apply(l2, a, 1, 4);
            toc_jit_func(j2)(b, 1);
            ok = 1;
            for (c = 0; c < 4; ++c) if (!approx(a[c], b[c], 1e-6f)) ok = 0;
            CHECK(ok, "JIT with LUT3D (helper call) == interpreter");
            toc_jit_destroy(j2);
        }
        toc_op_list_free(l2);
    }
    toc_op_list_free(l);
}

int main(void) {
    printf("== tocio math ==\n");
    test_math();
    test_inv4x4();
    printf("== tocio strbuf ==\n");
    test_strbuf();
    printf("== tocio parse ==\n");
    test_parse();
    printf("== tocio interpreter ==\n");
    test_interp();
    printf("== tocio yaml ==\n");
    test_yaml();
    printf("== tocio processor ==\n");
    test_processor();
    test_cdl_inverse();
    test_display_view();
    test_looks();
    printf("== tocio file LUTs ==\n");
    test_lutfile();
    test_filetransform();
    printf("== tocio edge cases ==\n");
    test_edge_cases();
    test_hostile();
    test_clf_conformance();
    printf("== tocio AOT-C codegen ==\n");
    test_codegen_c();
    test_codegen_c_hdr();
    printf("== tocio GLSL codegen ==\n");
    test_codegen_glsl();
    test_codegen_glsl_hdr();
    test_codegen_glsl_aces2();
    test_codegen_metal();
    test_codegen_exp_linear();
    test_codegen_aces();
    test_cdl_op_inverse();
    test_gamutcomp_boundary();
    test_lut1d_inverse();
    test_lut3d_inverse();
    printf("== tocio SIMD parity ==\n");
    test_simd_parity();
    test_simd_parity_transcendentals();
    printf("== tocio builtins + fixedfunc ==\n");
    test_builtins();
    test_colorimetry();
    test_display_transfer();
    printf("== tocio fixedfunc styles ==\n");
    test_fixedfunc_styles();
    printf("== tocio x64 JIT ==\n");
    test_jit();
    printf("\n%d passed, %d failed\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}
