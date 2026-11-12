/* Processor-build differential vectors: C `toc_processor.c` vs the Lean
 * pipeline model (`Tocio/ProcessorModel.lean`).
 *
 * Records:
 *   cdoc <id> | <hex of the config YAML>
 *   pcfg <id> | <0|1>                       (1 = config parse error)
 *   pq <id> cs <hex src> <hex dst> | <result>
 *   pq <id> dv <hex src> <hex display> <hex view> | <result>
 *
 * <result> is `ok:K1,K2,...` with the op-kind sequence, or `err:CODE`
 * (PARSE / UNSUPPORTED / NOT_FOUND / IO / NONINVERTIBLE / OUT_OF_MEMORY).
 * The checker rebuilds the same pipeline with the Lean model and compares
 * the result strings byte-for-byte.
 *
 * Vectors avoid FileTransform/BuiltinTransform (outside the model) and
 * never query the same view twice: `toc_cfg_view_looks` splits the looks
 * scalar in place, so a second call on the same view sees a mutated
 * buffer.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tocio.h"
#include "toc_internal.h"

static void print_hex(FILE *out, const char *p, size_t n) {
    for (size_t i = 0; i < n; i++) fprintf(out, "%02x", (unsigned char)p[i]);
}

static void hex_arg(FILE *out, const char *s) {
    print_hex(out, s, strlen(s));
}

static const char *kind_name(const toc_op *op) {
    switch (op->kind) {
    case TOC_OP_MATRIX: return "MATRIX";
    case TOC_OP_RANGE: return "RANGE";
    case TOC_OP_EXPONENT: return "EXPONENT";
    case TOC_OP_EXP_LINEAR: return "EXP_LINEAR";
    case TOC_OP_LOG: return "LOG";
    case TOC_OP_LOG_CAMERA: return "LOG_CAMERA";
    case TOC_OP_CDL: return "CDL";
    case TOC_OP_LUT1D: return "LUT1D";
    case TOC_OP_LUT3D: return "LUT3D";
    case TOC_OP_FIXEDFUNC: return "FIXEDFUNC";
    case TOC_OP_ACES_OUTPUT: return "ACES_OUTPUT";
    default: return "NOOP";
    }
}

static const char *err_name(toc_result r) {
    switch (r) {
    case TOC_ERROR_PARSE: return "PARSE";
    case TOC_ERROR_UNSUPPORTED: return "UNSUPPORTED";
    case TOC_ERROR_NOT_FOUND: return "NOT_FOUND";
    case TOC_ERROR_IO: return "IO";
    case TOC_ERROR_NONINVERTIBLE: return "NONINVERTIBLE";
    case TOC_ERROR_OUT_OF_MEMORY: return "OUT_OF_MEMORY";
    default: return "OTHER";
    }
}

static void print_result(FILE *out, toc_result rc, const toc_op_list *list) {
    if (!TOC_OK(rc) || !list) {
        fprintf(out, "err:%s", err_name(rc));
        return;
    }
    fprintf(out, "ok:");
    for (size_t i = 0; i < list->count; i++) {
        const toc_op *op = &list->ops[i];
        if (i) fputc(',', out);
        if (op->kind == TOC_OP_FIXEDFUNC)
            fprintf(out, "FIXEDFUNC(%d)", op->u.fixedfunc.style);
        else
            fprintf(out, "%s", kind_name(op));
    }
}

typedef struct {
    int is_display_view; /* 0: cs query, 1: display/view query */
    const char *a, *b, *c;
} pquery;

static void run_queries(FILE *out, size_t id, const toc_config *cfg,
                        const pquery *qs, size_t nq) {
    for (size_t i = 0; i < nq; i++) {
        toc_op_list *list = NULL;
        toc_result rc;
        if (qs[i].is_display_view)
            rc = toc_processor_from_display_view(cfg, qs[i].a, qs[i].b, qs[i].c,
                                                 NULL, &list);
        else
            rc = toc_processor_from_colorspaces(cfg, qs[i].a, qs[i].b, NULL, &list);
        fprintf(out, "pq %zu %s ", id, qs[i].is_display_view ? "dv" : "cs");
        hex_arg(out, qs[i].a);
        fputc(' ', out);
        hex_arg(out, qs[i].b);
        if (qs[i].is_display_view) {
            fputc(' ', out);
            hex_arg(out, qs[i].c);
        }
        fprintf(out, " | ");
        print_result(out, rc, list);
        fputc('\n', out);
        if (list) toc_op_list_free(list);
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }

    static const char *docs[] = {
        /* 0: scene colorspaces with matrix/log transforms, groups, data */
        "roles:\n"
        "  scene_linear: lin\n"
        "  data: raw\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: lin\n"
        "    to_scene_reference: !<MatrixTransform> {matrix: [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1]}\n"
        "  - !<ColorSpace>\n"
        "    name: logcs\n"
        "    from_scene_reference: !<LogTransform> {base: 2}\n"
        "  - !<ColorSpace>\n"
        "    name: raw\n"
        "    isdata: true\n"
        "  - !<ColorSpace>\n"
        "    name: grouped\n"
        "    to_scene_reference: !<GroupTransform>\n"
        "      children:\n"
        "        - !<MatrixTransform> {matrix: [1]}\n"
        "        - !<ExponentTransform> {value: 2.2}\n"
        "      direction: inverse\n"
        "  - !<ColorSpace>\n"
        "    name: cst\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: lin, dst: logcs}\n",
        /* 1: display/view config with looks, shared views, view transforms */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: srccs\n"
        "    to_scene_reference: !<MatrixTransform> {matrix: [1]}\n"
        "  - !<ColorSpace>\n"
        "    name: srccs2\n"
        "    from_scene_reference: !<ExponentTransform> {value: 2.2}\n"
        "  - !<ColorSpace>\n"
        "    name: raw\n"
        "    isdata: true\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: dispcs\n"
        "    to_display_reference: !<MatrixTransform> {matrix: [1]}\n"
        "  - !<ColorSpace>\n"
        "    name: disp2\n"
        "    from_display_reference: !<RangeTransform> {minInValue: 0, maxInValue: 1, minOutValue: 0, maxOutValue: 1}\n"
        "displays:\n"
        "  D:\n"
        "    - !<View> {name: Simple, colorspace: dispcs}\n"
        "    - !<View> {name: VTView, view_transform: VT2, display_colorspace: <USE_DISPLAY_NAME>}\n"
        "    - !<View> {name: LookView, colorspace: dispcs, looks: look1}\n"
        "    - !<View> {name: RawView, colorspace: raw}\n"
        "  E:\n"
        "    - !<Views> [SharedView]\n"
        "view_transforms:\n"
        "  - !<ViewTransform> {name: VT1, from_scene_reference: !<ExponentTransform> {value: 2.0}}\n"
        "  - !<ViewTransform> {name: VT2, from_scene_reference: !<LogTransform> {base: 10}}\n"
        "default_view_transform: VT1\n"
        "shared_views:\n"
        "  - !<View> {name: SharedView, colorspace: dispcs}\n"
        "looks:\n"
        "  - !<Look>\n"
        "    name: look1\n"
        "    process_space: srccs\n"
        "    transform: !<CDLTransform> {slope: 1}\n",
        /* 2: transform errors: empty range, bad bounds, log camera without
         *    break, unknown tag, colorspace transform without src/dst */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: bad1\n"
        "    to_scene_reference: !<RangeTransform> {}\n"
        "  - !<ColorSpace>\n"
        "    name: bad2\n"
        "    to_scene_reference: !<RangeTransform> {minInValue: 1, maxInValue: 1, minOutValue: 0, maxOutValue: 1}\n"
        "  - !<ColorSpace>\n"
        "    name: bad3\n"
        "    to_scene_reference: !<LogCameraTransform> {base: 2}\n"
        "  - !<ColorSpace>\n"
        "    name: bad4\n"
        "    to_scene_reference: !<MysteryTransform> {x: 1}\n"
        "  - !<ColorSpace>\n"
        "    name: bad5\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: a}\n",
        /* 3: inverted CDL decomposes; inverted group; singular-free matrices */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: cdlinv\n"
        "    from_scene_reference: !<CDLTransform> {slope: 1, direction: inverse}\n"
        "  - !<ColorSpace>\n"
        "    name: cdlfwd\n"
        "    to_scene_reference: !<CDLTransform> {slope: 1}\n"
        "  - !<ColorSpace>\n"
        "    name: grpinv\n"
        "    from_scene_reference: !<GroupTransform>\n"
        "      children:\n"
        "        - !<ExponentTransform> {value: 2.2}\n"
        "        - !<MatrixTransform> {matrix: [1]}\n",
        /* 4: fixed-function styles forward and inverted */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: ff1\n"
        "    to_scene_reference: !<FixedFunctionTransform> {style: ACES_Glow_10}\n"
        "  - !<ColorSpace>\n"
        "    name: ff2\n"
        "    to_scene_reference: !<FixedFunctionTransform> {style: XYZ_TO_uvY, direction: inverse}\n"
        "  - !<ColorSpace>\n"
        "    name: ff3\n"
        "    to_scene_reference: !<FixedFunctionTransform> {style: REC2100_SURROUND}\n"
        "  - !<ColorSpace>\n"
        "    name: ff4\n"
        "    to_scene_reference: !<FixedFunctionTransform> {style: Unknown_Style}\n",
        /* 5: log camera, range variants, forward group */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: lc\n"
        "    to_scene_reference: !<LogCameraTransform> {base: 2, lin_side_break: [0.1, 0.1, 0.1]}\n"
        "  - !<ColorSpace>\n"
        "    name: rg\n"
        "    to_scene_reference: !<RangeTransform> {minInValue: 0, maxInValue: 1, minOutValue: 0.5, maxOutValue: 2, style: noClamp}\n"
        "  - !<ColorSpace>\n"
        "    name: rg2\n"
        "    to_scene_reference: !<RangeTransform> {minInValue: 0.2}\n"
        "  - !<ColorSpace>\n"
        "    name: grp\n"
        "    to_scene_reference: !<GroupTransform>\n"
        "      children:\n"
        "        - !<ExponentTransform> {value: 2.2}\n"
        "        - !<MatrixTransform> {matrix: [1]}\n",
        /* 6: display-referred <-> scene-referred bridge; missing default VT */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: s1\n"
        "    to_scene_reference: !<ExponentTransform> {value: 2.2}\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: d1\n"
        "    from_display_reference: !<MatrixTransform> {matrix: [1]}\n",
        /* 7: view transform without any transform (UNSUPPORTED bridge) */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: s1\n"
        "    to_scene_reference: !<ExponentTransform> {value: 2.2}\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: d1\n"
        "    to_display_reference: !<MatrixTransform> {matrix: [1]}\n"
        "view_transforms:\n"
        "  - !<ViewTransform> {name: Empty}\n"
        "default_view_transform: Empty\n",
        /* 8: reverse/display VTs, <USE_DISPLAY_NAME>, look variants, untagged
         *    child, max-only range, inverted ColorSpaceTransform, camelCase */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: s\n"
        "    to_scene_reference: !<GroupTransform>\n"
        "      children:\n"
        "        - !<ExponentTransform> {value: 2.2}\n"
        "        - {}\n"
        "        - !<MatrixTransform> {matrix: [1]}\n"
        "  - !<ColorSpace>\n"
        "    name: rgmax\n"
        "    to_scene_reference: !<RangeTransform> {maxInValue: 1, maxOutValue: 2}\n"
        "  - !<ColorSpace>\n"
        "    name: cstinv\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: s, dst: rgmax, direction: inverse}\n"
        "  - !<ColorSpace>\n"
        "    name: lcamel\n"
        "    to_scene_reference: !<LogTransform> {base: 2, logSideSlope: [1, 1, 1]}\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: dispcs\n"
        "    from_display_reference: !<MatrixTransform> {matrix: [1]}\n"
        "displays:\n"
        "  dispcs:\n"
        "    - !<View> {name: UseName, view_transform: VTrev, display_colorspace: <USE_DISPLAY_NAME>}\n"
        "    - !<View> {name: DispVT, view_transform: VTdisp}\n"
        "    - !<View> {name: NoSpaceLook, colorspace: dispcs, looks: plainlook}\n"
        "    - !<View> {name: SpaceOnlyLook, colorspace: dispcs, looks: spacelook}\n"
        "    - !<View> {name: FlowLook, colorspace: dispcs, looks: flowlook}\n"
        "  d2:\n"
        "    - !<Views> [missingview]\n"
        "view_transform:\n"
        "  - !<ViewTransform> {name: VTrev, to_scene_reference: !<ExponentTransform> {value: 2.0}}\n"
        "  - !<ViewTransform> {name: VTdisp, from_display_reference: !<LogTransform> {base: 10}}\n"
        "  - !<ViewTransform> {name: VTbase, from_scene_reference: !<MatrixTransform> {matrix: [1]}}\n"
        "default_view_transform: VTbase\n"
        "looks:\n"
        "  - !<Look>\n"
        "    name: plainlook\n"
        "    transform: !<ExponentTransform> {value: 2.2}\n"
        "  - !<Look>\n"
        "    name: spacelook\n"
        "    process_space: dispcs\n"
        "  - !<Look> {name: flowlook, transform: !<ExponentTransform> {value: 2.2}}\n",
        /* 9: self-referencing colorspace transform -> walk depth cap */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: selfref\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: selfref, dst: other}\n"
        "  - !<ColorSpace>\n"
        "    name: other\n"
        "    to_scene_reference: !<ExponentTransform> {value: 2.2}\n",
        /* 10: mutually-referencing colorspaces -> walk depth cap */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: ca\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: ca, dst: cb}\n"
        "  - !<ColorSpace>\n"
        "    name: cb\n"
        "    to_scene_reference: !<ColorSpaceTransform> {src: cb, dst: ca}\n",
    };

    static const pquery q0[] = {
        {0, "lin", "logcs", NULL},
        {0, "scene_linear", "logcs", NULL},
        {0, "lin", "raw", NULL},
        {0, "raw", "logcs", NULL},
        {0, "grouped", "lin", NULL},
        {0, "cst", "lin", NULL},
        {0, "missing", "lin", NULL},
        {0, "lin", "missing", NULL},
    };
    static const pquery q1[] = {
        {1, "srccs", "D", "Simple"},
        {1, "srccs", "D", "VTView"},
        {1, "srccs", "D", "LookView"},
        {1, "srccs", "D", "RawView"},
        {1, "srccs2", "D", "Simple"},
        {1, "srccs", "E", "SharedView"},
        {1, "srccs", "D", "NoSuchView"},
        {1, "srccs", "NoSuchDisplay", "Simple"},
        {0, "srccs", "srccs2", NULL},
        {0, "srccs", "dispcs", NULL},
        {0, "dispcs", "srccs", NULL},
        {0, "srccs", "raw", NULL},
        {0, "disp2", "dispcs", NULL},
    };
    static const pquery q2[] = {
        {0, "bad1", "bad1", NULL},
        {0, "bad2", "bad2", NULL},
        {0, "bad3", "bad3", NULL},
        {0, "bad4", "bad4", NULL},
        {0, "bad5", "bad5", NULL},
        {0, "bad1", "bad2", NULL},
    };
    static const pquery q3[] = {
        {0, "cdlinv", "cdlinv", NULL},
        {0, "cdlfwd", "cdlinv", NULL},
        {0, "grpinv", "grpinv", NULL},
        {0, "grpinv", "cdlfwd", NULL},
    };
    static const pquery q4[] = {
        {0, "ff1", "ff1", NULL},
        {0, "ff2", "ff2", NULL},
        {0, "ff3", "ff3", NULL},
        {0, "ff4", "ff4", NULL},
        {0, "ff1", "ff2", NULL},
    };
    static const pquery q5[] = {
        {0, "lc", "lc", NULL},
        {0, "rg", "rg", NULL},
        {0, "rg2", "rg2", NULL},
        {0, "grp", "grp", NULL},
        {0, "lc", "rg", NULL},
    };
    static const pquery q6[] = {
        {0, "d1", "s1", NULL},
        {0, "s1", "d1", NULL},
    };
    static const pquery q7[] = {
        {0, "d1", "s1", NULL},
    };

    static const pquery q8[] = {
        {1, "s", "dispcs", "UseName"},
        {1, "s", "dispcs", "DispVT"},
        {1, "s", "dispcs", "NoSpaceLook"},
        {1, "s", "dispcs", "SpaceOnlyLook"},
        {1, "s", "dispcs", "FlowLook"},
        {1, "s", "d2", "missingview"},
        {0, "s", "rgmax", NULL},
        {0, "cstinv", "s", NULL},
        {0, "lcamel", "lcamel", NULL},
        {0, "rgmax", "rgmax", NULL},
    };
    static const pquery q9[] = {{0, "selfref", "other", NULL}};
    static const pquery q10[] = {{0, "ca", "cb", NULL}};
    static const pquery *qsets[] = {q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10};
    static const size_t qcounts[] = {sizeof(q0) / sizeof(q0[0]),
                                     sizeof(q1) / sizeof(q1[0]),
                                     sizeof(q2) / sizeof(q2[0]),
                                     sizeof(q3) / sizeof(q3[0]),
                                     sizeof(q4) / sizeof(q4[0]),
                                     sizeof(q5) / sizeof(q5[0]),
                                     sizeof(q6) / sizeof(q6[0]),
                                     sizeof(q7) / sizeof(q7[0]),
                                     sizeof(q8) / sizeof(q8[0]),
                                     sizeof(q9) / sizeof(q9[0]),
                                     sizeof(q10) / sizeof(q10[0])};

    /* Under-cap probe: a 30-level nested GroupTransform chain stays inside
     * both the YAML depth cap (128) and the walk cap (64). Deep chains cannot
     * reach the walk cap through YAML nesting, so the cap vectors use
     * colorspace-reference cycles instead. */
    static char *depth_docs[1];
    for (int d = 0; d < 1; d++) {
        int levels = 30;
        size_t cap = 65536, off = 0;
        char *buf = (char *)malloc(cap);
        if (!buf) return 1;
        off += (size_t)snprintf(buf + off, cap - off,
                                "colorspaces:\n  - !<ColorSpace>\n    name: deep\n"
                                "    to_scene_reference: !<GroupTransform>\n");
        for (int sp = 0; sp < 6; sp++) buf[off++] = ' ';
        off += (size_t)snprintf(buf + off, cap - off, "children:\n");
        for (int lvl = 1; lvl < levels; lvl++) {
            int ind = 4 + 4 * lvl;
            for (int sp = 0; sp < ind; sp++) buf[off++] = ' ';
            off += (size_t)snprintf(buf + off, cap - off, "- !<GroupTransform>\n");
            for (int sp = 0; sp < ind + 2; sp++) buf[off++] = ' ';
            off += (size_t)snprintf(buf + off, cap - off, "children:\n");
        }
        {
            int ind = 4 + 4 * levels;
            for (int sp = 0; sp < ind; sp++) buf[off++] = ' ';
            off += (size_t)snprintf(buf + off, cap - off,
                                    "- !<ExponentTransform> {value: 2.2}\n");
        }
        buf[off] = 0;
        depth_docs[d] = buf;
    }

    size_t ndocs = sizeof(docs) / sizeof(docs[0]);
    for (size_t id = 0; id < ndocs + 1; id++) {
        const char *text = id < ndocs ? docs[id] : depth_docs[id - ndocs];
        size_t len = strlen(text);
        toc_config *cfg = NULL;
        toc_result rc;

        fprintf(out, "cdoc %zu | ", id);
        print_hex(out, text, len);
        fprintf(out, "\n");

        rc = toc_config_parse(text, len, NULL, &cfg);
        fprintf(out, "pcfg %zu | %d\n", id, TOC_OK(rc) ? 0 : 1);
        if (TOC_OK(rc) && cfg) {
            if (id < ndocs) {
                run_queries(out, id, cfg, qsets[id], qcounts[id]);
            } else {
                static const pquery qdeep[] = {{0, "deep", "deep", NULL}};
                run_queries(out, id, cfg, qdeep, 1);
            }
            toc_config_free(cfg);
        }
    }
    for (int d = 0; d < 1; d++) free(depth_docs[d]);

    if (out != stdout) fclose(out);
    return 0;
}
