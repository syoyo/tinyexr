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
 * FileTransform is driven by the embedded reader map (`pfile` records);
 * BuiltinTransform styles expand through the model too. Vectors never query
 * the same view twice: `toc_cfg_view_looks` splits the looks
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


static uint32_t fbits(float f) {
    uint32_t u;
    memcpy(&u, &f, 4);
    return u;
}

static void emit_bits(FILE *out, const float *f, int n) {
    for (int i = 0; i < n; i++) fprintf(out, " %08x", fbits(f[i]));
}

/* One `pop` record per result op: `pop <id> | <qi> <k> <kind> <bits...>`.
 * The layout matches the AOT-C codegen recipes. */
static void emit_op_recipe(FILE *out, size_t id, size_t qi, size_t k,
                           const toc_op *op) {
    fprintf(out, "pop %zu | %zu %zu ", id, qi, k);
    switch (op->kind) {
    case TOC_OP_MATRIX:
        fprintf(out, "matrix");
        emit_bits(out, op->u.matrix.m, 16);
        emit_bits(out, op->u.matrix.off, 4);
        break;
    case TOC_OP_RANGE:
        fprintf(out, "range");
        emit_bits(out, op->u.range.scale, 4);
        emit_bits(out, op->u.range.offset, 4);
        emit_bits(out, op->u.range.min, 4);
        emit_bits(out, op->u.range.max, 4);
        fprintf(out, " %d %d", op->u.range.clamp_lo, op->u.range.clamp_hi);
        break;
    case TOC_OP_EXPONENT:
        fprintf(out, "exponent");
        emit_bits(out, op->u.exponent.e, 4);
        fprintf(out, " %d", op->u.exponent.mirror);
        break;
    case TOC_OP_EXP_LINEAR:
        fprintf(out, "explinear");
        emit_bits(out, op->u.exp_linear.scale, 4);
        emit_bits(out, op->u.exp_linear.offset, 4);
        emit_bits(out, op->u.exp_linear.gamma, 4);
        emit_bits(out, op->u.exp_linear.breakpoint, 4);
        emit_bits(out, op->u.exp_linear.slope, 4);
        fprintf(out, " %d %d", op->u.exp_linear.inverse, op->u.exp_linear.mirror);
        break;
    case TOC_OP_LOG:
        fprintf(out, "log");
        emit_bits(out, op->u.log.log_slope, 3);
        emit_bits(out, op->u.log.log_offset, 3);
        emit_bits(out, op->u.log.lin_slope, 3);
        emit_bits(out, op->u.log.lin_offset, 3);
        emit_bits(out, &op->u.log.base, 1);
        fprintf(out, " %d", op->u.log.inverse);
        break;
    case TOC_OP_LOG_CAMERA:
        fprintf(out, "logcam");
        emit_bits(out, op->u.logcam.log_slope, 3);
        emit_bits(out, op->u.logcam.log_offset, 3);
        emit_bits(out, op->u.logcam.lin_slope, 3);
        emit_bits(out, op->u.logcam.lin_offset, 3);
        emit_bits(out, op->u.logcam.lin_break, 3);
        emit_bits(out, op->u.logcam.linear_slope, 3);
        emit_bits(out, op->u.logcam.linear_offset, 3);
        emit_bits(out, &op->u.logcam.base, 1);
        fprintf(out, " %d", op->u.logcam.inverse);
        break;
    case TOC_OP_CDL:
        fprintf(out, "cdl");
        emit_bits(out, op->u.cdl.slope, 3);
        emit_bits(out, op->u.cdl.offset, 3);
        emit_bits(out, op->u.cdl.power, 3);
        emit_bits(out, &op->u.cdl.saturation, 1);
        emit_bits(out, op->u.cdl.luma, 3);
        fprintf(out, " %d %d", op->u.cdl.clamp, op->u.cdl.inverse);
        break;
    case TOC_OP_LUT1D:
        fprintf(out, "lut1d %d %d", op->u.lut1d.length, op->u.lut1d.channels);
        emit_bits(out, &op->u.lut1d.domain_min, 1);
        emit_bits(out, &op->u.lut1d.domain_max, 1);
        emit_bits(out, op->u.lut1d.data,
                  op->u.lut1d.length * (op->u.lut1d.channels == 1 ? 1 : 3));
        break;
    case TOC_OP_LUT3D:
        fprintf(out, "lut3d %d %d", op->u.lut3d.size,
                op->u.lut3d.interp == TOC_INTERP_TETRAHEDRAL ? 1 : 0);
        emit_bits(out, op->u.lut3d.domain_min, 3);
        emit_bits(out, op->u.lut3d.domain_max, 3);
        emit_bits(out, op->u.lut3d.data,
                  (size_t)op->u.lut3d.size * op->u.lut3d.size *
                      op->u.lut3d.size * 3);
        break;
    case TOC_OP_FIXEDFUNC:
        fprintf(out, "fixed %d %d", op->u.fixedfunc.style,
                op->u.fixedfunc.nparams);
        emit_bits(out, op->u.fixedfunc.params, 8);
        break;
    case TOC_OP_ACES_OUTPUT: {
        /* Every scalar `toc_aces2_init` derives from (peak, limiting primaries):
         * tonescale, chroma compression, both JMh matrices. The hue-indexed
         * tables are not modelled. */
        const toc_aces2 *t = (const toc_aces2 *)op->u.aces.t;
        fprintf(out, "aces2");
        emit_bits(out, &t->ts_n, 1);
        emit_bits(out, &t->ts_n_r, 1);
        emit_bits(out, &t->ts_g, 1);
        emit_bits(out, &t->ts_t_1, 1);
        emit_bits(out, &t->ts_c_t, 1);
        emit_bits(out, &t->ts_s_2, 1);
        emit_bits(out, &t->ts_u_2, 1);
        emit_bits(out, &t->ts_m_2, 1);
        emit_bits(out, &t->ts_fwd_limit, 1);
        emit_bits(out, &t->ts_inv_limit, 1);
        emit_bits(out, &t->ts_log_peak, 1);
        emit_bits(out, &t->cc_sat, 1);
        emit_bits(out, &t->cc_sat_thr, 1);
        emit_bits(out, &t->cc_compr, 1);
        emit_bits(out, &t->cc_scale, 1);
        emit_bits(out, &t->limit_J_max, 1);
        emit_bits(out, &t->model_gamma_inv, 1);
        emit_bits(out, &t->mid_J, 1);
        emit_bits(out, &t->focus_dist, 1);
        emit_bits(out, &t->lower_hull_gamma_inv, 1);
        emit_bits(out, t->out.rgb_to_cam, 9);
        emit_bits(out, t->out.cone_to_aab, 9);
        fprintf(out, " %d", op->u.aces.inverse);
        break;
    }
    default:
        fprintf(out, "noop");
        break;
    }
    fputc('\n', out);
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
        if (TOC_OK(rc) && list)
            for (size_t k = 0; k < list->count; k++)
                emit_op_recipe(out, id, i, k, &list->ops[k]);
        if (list) toc_op_list_free(list);
    }
}


/* ---- embedded files for FileTransform vectors --------------------------- */

static const char *FILE_SPI1D =
    "Version 1\n"
    "From 0.0 2.0\n"
    "Length 4\n"
    "Components 3\n"
    "{\n"
    "0.0 0.0 0.0\n"
    "0.25 0.3 0.35\n"
    "0.5 0.6 0.65\n"
    "1.0 1.0 1.0\n"
    "}\n";

static const char *FILE_SPI3D =
    "SPILUT 1.0\n"
    "3 3\n"
    "2 2 2\n"
    "0 0 0 0.0 0.0 0.0\n"
    "1 0 0 0.1 0.2 0.3\n"
    "0 1 0 0.4 0.5 0.6\n"
    "1 1 0 0.7 0.8 0.9\n"
    "0 0 1 0.11 0.21 0.31\n"
    "1 0 1 0.41 0.51 0.61\n"
    "0 1 1 0.71 0.81 0.91\n"
    "1 1 1 1.0 1.0 1.0\n";

static const char *FILE_CLF =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
    "<ProcessList xmlns=\"urn:AMP:CLF\" id=\"t\">\n"
    "<LUT1D outBitDepth=\"32f\">\n"
    "<Array dim=\"4 3\">\n"
    "0.0 0.0 0.0 0.25 0.3 0.35 0.5 0.6 0.65 1.0 1.0 1.0\n"
    "</Array>\n"
    "</LUT1D>\n"
    "</ProcessList>\n";

static toc_result file_reader(void *user, const char *name,
                              const toc_allocator *a, char **out, size_t *len) {
    const char *d = NULL;
    size_t n;
    char *buf;
    (void)user;
    if (!strcmp(name, "ramp.spi1d")) d = FILE_SPI1D;
    else if (!strcmp(name, "cube.spi3d")) d = FILE_SPI3D;
    else if (!strcmp(name, "ramp.clf")) d = FILE_CLF;
    else if (!strcmp(name, "blobs/lut.txt")) d = FILE_SPI3D; /* sniffed */
    if (!d) return TOC_ERROR_IO;
    n = strlen(d);
    buf = (char *)toc_malloc(a, n + 1);
    if (!buf) return TOC_ERROR_OUT_OF_MEMORY;
    memcpy(buf, d, n + 1);
    *out = buf;
    *len = n;
    return TOC_SUCCESS;
}

static void emit_file_records(FILE *out) {
    static const struct { const char *name; const char *data; } files[] = {
        {"ramp.spi1d", NULL}, {"cube.spi3d", NULL}, {"ramp.clf", NULL},
        {"blobs/lut.txt", NULL},
    };
    const char *data[4] = {FILE_SPI1D, FILE_SPI3D, FILE_CLF, FILE_SPI3D};
    for (int i = 0; i < 4; i++) {
        fprintf(out, "pfile ");
        print_hex(out, files[i].name, strlen(files[i].name));
        fputc(' ', out);
        print_hex(out, data[i], strlen(data[i]));
        fputc('\n', out);
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
        /* 12: FileTransform: spi1d, spi3d (with interpolation), clf,
         *     inverted (NONINVERTIBLE), missing file (IO), sniffed spi3d */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: filespi1\n"
        "    to_scene_reference: !<FileTransform> {src: ramp.spi1d}\n"
        "  - !<ColorSpace>\n"
        "    name: filespi3\n"
        "    to_scene_reference: !<FileTransform> {src: cube.spi3d, interpolation: nearest}\n"
        "  - !<ColorSpace>\n"
        "    name: fileclf\n"
        "    to_scene_reference: !<FileTransform> {src: ramp.clf}\n"
        "  - !<ColorSpace>\n"
        "    name: fileinv\n"
        "    to_scene_reference: !<FileTransform> {src: ramp.spi1d, direction: inverse}\n"
        "  - !<ColorSpace>\n"
        "    name: filemissing\n"
        "    to_scene_reference: !<FileTransform> {src: nope.spi1d}\n"
        "  - !<ColorSpace>\n"
        "    name: filesniff\n"
        "    to_scene_reference: !<FileTransform> {src: blobs/lut.txt}\n"
        "  - !<ColorSpace>\n"
        "    name: plain\n",
        /* 11: numeric lowering paths: MonCurve, explicit LinearSlope log
         *    camera, noclamp CDL, matrix offsets, fixed-function params,
         *    singular matrix inversion */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: ewl\n"
        "    to_scene_reference: !<ExponentWithLinearTransform> {gamma: [2.4, 2.2, 2.0, 1.0], offset: [0.055, 0.05, 0.04, 0]}\n"
        "  - !<ColorSpace>\n"
        "    name: ewl2\n"
        "    from_scene_reference: !<ExponentWithLinearTransform> {gamma: 2.2, offset: 0.05}\n"
        "  - !<ColorSpace>\n"
        "    name: logcam2\n"
        "    to_scene_reference: !<LogCameraTransform> {base: 10, lin_side_break: [0.18, 0.18, 0.18], linear_slope: [5.0, 5.0, 5.0], log_side_slope: [0.9, 0.9, 0.9], lin_side_offset: [0.01, 0.01, 0.01]}\n"
        "  - !<ColorSpace>\n"
        "    name: cdl2\n"
        "    to_scene_reference: !<CDLTransform> {slope: [1.2, 0.8, 1.1], offset: [0.1, 0.2, 0.3], power: [0.9, 1.1, 1.0], sat: 1.5, style: noclamp}\n"
        "  - !<ColorSpace>\n"
        "    name: mx2\n"
        "    to_scene_reference: !<MatrixTransform> {matrix: [1, 0.2, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0.01, 0.02, 0.03, 1], offset: [0.1, 0.2, 0.3, 0.4]}\n"
        "  - !<ColorSpace>\n"
        "    name: ffp\n"
        "    to_scene_reference: !<FixedFunctionTransform> {style: ACES_Gamut_Comp_13, params: [1.05, 1.1, 1.2, 0.8, 0.7, 0.9, 1.2]}\n"
        "  - !<ColorSpace>\n"
        "    name: ffr\n"
        "    from_scene_reference: !<FixedFunctionTransform> {style: REC2100_SURROUND, params: [0.78]}\n"
        "  - !<ColorSpace>\n"
        "    name: sing\n"
        "    to_scene_reference: !<MatrixTransform> {matrix: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]}\n",
        /* 13: BuiltinTransform expansion: the ACES AP matrices and log curves,
         *     derived colorimetry, camera-log and display builtins, the
         *     ACES 2.0 output chains, an unknown style, and inverses. */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: plain\n"
        "  - !<ColorSpace>\n"
        "    name: b0\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACEScg_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b1\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES2065-1_to_ACEScg}\n"
        "  - !<ColorSpace>\n"
        "    name: b2\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACEScct_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b3\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES2065-1_to_ACEScct}\n"
        "  - !<ColorSpace>\n"
        "    name: b4\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACEScc_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b5\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES2065-1_to_ACEScc}\n"
        "  - !<ColorSpace>\n"
        "    name: b6\n"
        "    to_scene_reference: !<BuiltinTransform> {style: UTILITY - ACES-AP0_to_CIE-XYZ-D65_BFD}\n"
        "  - !<ColorSpace>\n"
        "    name: b7\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-LMT - ACES 1.3 Reference Gamut Compression}\n"
        "  - !<ColorSpace>\n"
        "    name: b8\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ARRI_ALEXA-LOGC-EI800-AWG_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b9\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ARRI_LOGC4_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b10\n"
        "    to_scene_reference: !<BuiltinTransform> {style: SONY_SLOG3-SGAMUT3_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b11\n"
        "    to_scene_reference: !<BuiltinTransform> {style: SONY_SLOG3-SGAMUT3.CINE_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b12\n"
        "    to_scene_reference: !<BuiltinTransform> {style: SONY_SLOG3-SGAMUT3-VENICE_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b13\n"
        "    to_scene_reference: !<BuiltinTransform> {style: SONY_SLOG3-SGAMUT3.CINE-VENICE_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b14\n"
        "    to_scene_reference: !<BuiltinTransform> {style: RED_LOG3G10-RWG_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b15\n"
        "    to_scene_reference: !<BuiltinTransform> {style: PANASONIC_VLOG-VGAMUT_to_ACES2065-1}\n"
        "  - !<ColorSpace>\n"
        "    name: b16\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_sRGB}\n"
        "  - !<ColorSpace>\n"
        "    name: b17\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_DisplayP3}\n"
        "  - !<ColorSpace>\n"
        "    name: b18\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_Display-P3}\n"
        "  - !<ColorSpace>\n"
        "    name: b19\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_DisplayP3-HDR}\n"
        "  - !<ColorSpace>\n"
        "    name: b20\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_G2.2-REC.709}\n"
        "  - !<ColorSpace>\n"
        "    name: b21\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_G2.6-P3-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b22\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_DCI-P3}\n"
        "  - !<ColorSpace>\n"
        "    name: b23\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_REC.1886-REC.709}\n"
        "  - !<ColorSpace>\n"
        "    name: b24\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_Rec.1886-Rec.709}\n"
        "  - !<ColorSpace>\n"
        "    name: b25\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_REC.1886-REC.2020}\n"
        "  - !<ColorSpace>\n"
        "    name: b26\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_REC.2100-PQ}\n"
        "  - !<ColorSpace>\n"
        "    name: b27\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_Rec.2100-PQ}\n"
        "  - !<ColorSpace>\n"
        "    name: b28\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_ST2084-P3-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b29\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_Rec.2100-HLG}\n"
        "  - !<ColorSpace>\n"
        "    name: b30\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_DCDM-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b31\n"
        "    to_scene_reference: !<BuiltinTransform> {style: CIE-XYZ-D65_to_ST2084-DCDM-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b32\n"
        "    to_scene_reference: !<BuiltinTransform> {style: Linear-sRGB_to_Linear-P3-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b33\n"
        "    to_scene_reference: !<BuiltinTransform> {style: Linear-Rec709_to_Linear-Rec2020}\n"
        "  - !<ColorSpace>\n"
        "    name: b34\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACEScg_to_Linear-AP0}\n"
        "  - !<ColorSpace>\n"
        "    name: b35\n"
        "    to_scene_reference: !<BuiltinTransform> {style: Linear-AP0_to_CIE-XYZ-D65}\n"
        "  - !<ColorSpace>\n"
        "    name: b36\n"
        "    to_scene_reference: !<BuiltinTransform> {style: DISPLAY - CIE-XYZ-D65_to_sRGB - MIRROR NEGS}\n"
        "  - !<ColorSpace>\n"
        "    name: b37\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b38\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b39\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b40\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b41\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-REC2020_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b42\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-108nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b43\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-300nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b44\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b45\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b46\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-REC2020_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b47\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-REC2020_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b48\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-REC2020_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b49\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-REC709-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b50\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b51\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b52\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b53\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D60-in-XYZ-E_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b54\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-108nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b55\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-300nit-P3-D60-in-XYZ-E_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b56\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b57\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b58\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b59\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D60-in-P3-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b60\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b61\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b62\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b63\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b64\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-REC2020-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b65\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-REC2020-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b66\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-REC2020-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: b67\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-REC2020-D60-in-REC2020-D65_2.0}\n"
        "  - !<ColorSpace>\n"
        "    name: bbad\n"
        "    to_scene_reference: !<BuiltinTransform> {style: NoSuchBuiltin}\n"
        "  - !<ColorSpace>\n"
        "    name: binv\n"
        "    to_scene_reference: !<BuiltinTransform> {style: ACEScg_to_ACES2065-1, direction: inverse}\n",
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
    static const pquery q11[] = {
        {0, "filespi1", "plain", NULL},
        {0, "filespi3", "plain", NULL},
        {0, "fileclf", "plain", NULL},
        {0, "filesniff", "plain", NULL},
        {0, "fileinv", "plain", NULL},
        {0, "filemissing", "plain", NULL},
        {0, "plain", "filespi1", NULL},
        {0, "filespi1", "filespi1", NULL},
    };
    static const pquery q12[] = {
        {0, "ewl", "ewl", NULL},
        {0, "ewl2", "ewl2", NULL},
        {0, "logcam2", "logcam2", NULL},
        {0, "cdl2", "cdl2", NULL},
        {0, "mx2", "mx2", NULL},
        {0, "ffp", "ffp", NULL},
        {0, "ffr", "ffr", NULL},
        {0, "sing", "sing", NULL},
        {0, "ewl", "cdl2", NULL},
    };
    static const pquery q9[] = {{0, "selfref", "other", NULL}};
    static const pquery q10[] = {{0, "ca", "cb", NULL}};
    static const pquery q13[] = {
        {0, "b0", "plain", NULL},
        {0, "b1", "plain", NULL},
        {0, "b2", "plain", NULL},
        {0, "b3", "plain", NULL},
        {0, "b4", "plain", NULL},
        {0, "b5", "plain", NULL},
        {0, "b6", "plain", NULL},
        {0, "b7", "plain", NULL},
        {0, "b8", "plain", NULL},
        {0, "b9", "plain", NULL},
        {0, "b10", "plain", NULL},
        {0, "b11", "plain", NULL},
        {0, "b12", "plain", NULL},
        {0, "b13", "plain", NULL},
        {0, "b14", "plain", NULL},
        {0, "b15", "plain", NULL},
        {0, "b16", "plain", NULL},
        {0, "b17", "plain", NULL},
        {0, "b18", "plain", NULL},
        {0, "b19", "plain", NULL},
        {0, "b20", "plain", NULL},
        {0, "b21", "plain", NULL},
        {0, "b22", "plain", NULL},
        {0, "b23", "plain", NULL},
        {0, "b24", "plain", NULL},
        {0, "b25", "plain", NULL},
        {0, "b26", "plain", NULL},
        {0, "b27", "plain", NULL},
        {0, "b28", "plain", NULL},
        {0, "b29", "plain", NULL},
        {0, "b30", "plain", NULL},
        {0, "b31", "plain", NULL},
        {0, "b32", "plain", NULL},
        {0, "b33", "plain", NULL},
        {0, "b34", "plain", NULL},
        {0, "b35", "plain", NULL},
        {0, "b36", "plain", NULL},
        {0, "b37", "plain", NULL},
        {0, "b38", "plain", NULL},
        {0, "b39", "plain", NULL},
        {0, "b40", "plain", NULL},
        {0, "b41", "plain", NULL},
        {0, "b42", "plain", NULL},
        {0, "b43", "plain", NULL},
        {0, "b44", "plain", NULL},
        {0, "b45", "plain", NULL},
        {0, "b46", "plain", NULL},
        {0, "b47", "plain", NULL},
        {0, "b48", "plain", NULL},
        {0, "b49", "plain", NULL},
        {0, "b50", "plain", NULL},
        {0, "b51", "plain", NULL},
        {0, "b52", "plain", NULL},
        {0, "b53", "plain", NULL},
        {0, "b54", "plain", NULL},
        {0, "b55", "plain", NULL},
        {0, "b56", "plain", NULL},
        {0, "b57", "plain", NULL},
        {0, "b58", "plain", NULL},
        {0, "b59", "plain", NULL},
        {0, "b60", "plain", NULL},
        {0, "b61", "plain", NULL},
        {0, "b62", "plain", NULL},
        {0, "b63", "plain", NULL},
        {0, "b64", "plain", NULL},
        {0, "b65", "plain", NULL},
        {0, "b66", "plain", NULL},
        {0, "b67", "plain", NULL},
        {0, "plain", "b0", NULL},
        {0, "plain", "b1", NULL},
        {0, "plain", "b2", NULL},
        {0, "plain", "b3", NULL},
        {0, "plain", "b4", NULL},
        {0, "plain", "b5", NULL},
        {0, "plain", "b6", NULL},
        {0, "plain", "b7", NULL},
        {0, "plain", "b8", NULL},
        {0, "plain", "b12", NULL},
        {0, "plain", "b16", NULL},
        {0, "plain", "b30", NULL},
        {0, "plain", "b26", NULL},
        {0, "plain", "b29", NULL},
        {0, "plain", "b32", NULL},
        {0, "plain", "b34", NULL},
        {0, "plain", "b36", NULL},
        {0, "plain", "b43", NULL},
        {0, "bbad", "plain", NULL},
        {0, "binv", "plain", NULL},
        {0, "b0", "b1", NULL},
    };

    static const pquery *qsets[] = {q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13};
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
                                     sizeof(q10) / sizeof(q10[0]),
                                     sizeof(q11) / sizeof(q11[0]),
                                     sizeof(q12) / sizeof(q12[0]),
                                     sizeof(q13) / sizeof(q13[0])};

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

    emit_file_records(out);

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
        if (TOC_OK(rc) && cfg) toc_config_set_file_reader(cfg, file_reader, NULL);
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
