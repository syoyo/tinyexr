/* CLF differential vectors: C parse (+apply) vs Lean loadClf.
 * Line format:
 *   clf ok ops <n> [matrix <16> <4> | range <4> <4> <4> <4> <cl> <ch>]*
 *       <in...> | <out...> || <src_hex>
 *   clf fail parse|unsupported || <src_hex>
 * Hex: float bits or source bytes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tocio.h"
#include "toc_internal.h"

static uint64_t rng_state;
static uint64_t splitmix64(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static float randf(void) { return (float)(splitmix64() % 4000u) / 1000.0f - 1.0f; }

static toc_op_list *new_list(void) {
    toc_op_list *list = calloc(1, sizeof(toc_op_list));
    list->alloc = *toc_default_allocator();
    return list;
}

static void print_hex_src(FILE *out, const char *src, size_t len) {
    for (size_t i = 0; i < len; i++) fprintf(out, "%02x", (unsigned char)src[i]);
}

static void print_f32bits(FILE *out, const float *v, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t u;
        memcpy(&u, v + i, 4);
        fprintf(out, " %08x", u);
    }
}

static void emit_ok(FILE *out, const toc_op_list *list, const char *src,
                    size_t len, const float *in_img, const float *out_img,
                    size_t npix) {
    fprintf(out, "clf ok ops %zu", list->count);
    for (size_t k = 0; k < list->count; k++) {
        const toc_op *op = &list->ops[k];
        if (op->kind == TOC_OP_MATRIX) {
            fprintf(out, " matrix");
            print_f32bits(out, op->u.matrix.m, 16);
            print_f32bits(out, op->u.matrix.off, 4);
        } else if (op->kind == TOC_OP_RANGE) {
            fprintf(out, " range");
            print_f32bits(out, op->u.range.scale, 4);
            print_f32bits(out, op->u.range.offset, 4);
            print_f32bits(out, op->u.range.min, 4);
            print_f32bits(out, op->u.range.max, 4);
            fprintf(out, " %d %d", op->u.range.clamp_lo, op->u.range.clamp_hi);
        } else if (op->kind == TOC_OP_LUT1D) {
            fprintf(out, " lut1d %d", op->u.lut1d.length);
            print_f32bits(out, op->u.lut1d.data, (size_t)op->u.lut1d.length * 3);
        } else if (op->kind == TOC_OP_LUT3D) {
            fprintf(out, " lut3d %d %d", op->u.lut3d.size, op->u.lut3d.interp);
            print_f32bits(out, op->u.lut3d.data,
                          (size_t)op->u.lut3d.size * (size_t)op->u.lut3d.size *
                              (size_t)op->u.lut3d.size * 3);
        } else if (op->kind == TOC_OP_EXPONENT) {
            fprintf(out, " exponent");
            print_f32bits(out, op->u.exponent.e, 4);
            fprintf(out, " %d", op->u.exponent.mirror);
        } else if (op->kind == TOC_OP_EXP_LINEAR) {
            fprintf(out, " explin");
            print_f32bits(out, op->u.exp_linear.scale, 4);
            print_f32bits(out, op->u.exp_linear.offset, 4);
            print_f32bits(out, op->u.exp_linear.gamma, 4);
            print_f32bits(out, op->u.exp_linear.breakpoint, 4);
            print_f32bits(out, op->u.exp_linear.slope, 4);
            fprintf(out, " %d %d", op->u.exp_linear.inverse, op->u.exp_linear.mirror);
        } else if (op->kind == TOC_OP_LOG) {
            fprintf(out, " log");
            print_f32bits(out, &op->u.log.base, 1);
            fprintf(out, " %d", op->u.log.inverse);
            print_f32bits(out, op->u.log.log_slope, 3);
            print_f32bits(out, op->u.log.log_offset, 3);
            print_f32bits(out, op->u.log.lin_slope, 3);
            print_f32bits(out, op->u.log.lin_offset, 3);
        } else if (op->kind == TOC_OP_LOG_CAMERA) {
            fprintf(out, " logcam");
            print_f32bits(out, &op->u.logcam.base, 1);
            fprintf(out, " %d", op->u.logcam.inverse);
            print_f32bits(out, op->u.logcam.log_slope, 3);
            print_f32bits(out, op->u.logcam.log_offset, 3);
            print_f32bits(out, op->u.logcam.lin_slope, 3);
            print_f32bits(out, op->u.logcam.lin_offset, 3);
            print_f32bits(out, op->u.logcam.lin_break, 3);
            print_f32bits(out, op->u.logcam.linear_slope, 3);
            print_f32bits(out, op->u.logcam.linear_offset, 3);
        } else if (op->kind == TOC_OP_CDL) {
            fprintf(out, " cdl");
            print_f32bits(out, op->u.cdl.slope, 3);
            print_f32bits(out, op->u.cdl.offset, 3);
            print_f32bits(out, op->u.cdl.power, 3);
            print_f32bits(out, &op->u.cdl.saturation, 1);
            fprintf(out, " %d", op->u.cdl.clamp);
        } else {
            fprintf(out, " other%d", (int)op->kind);
        }
    }
    fprintf(out, " ");
    print_f32bits(out, in_img, npix * 4);
    fprintf(out, " |");
    print_f32bits(out, out_img, npix * 4);
    fprintf(out, " || ");
    print_hex_src(out, src, len);
    fprintf(out, "\n");
}

static void emit_fail(FILE *out, const char *src, size_t len, toc_result rc) {
    fprintf(out, "clf fail %s || ",
            rc == TOC_ERROR_UNSUPPORTED ? "unsupported" : "parse");
    print_hex_src(out, src, len);
    fprintf(out, "\n");
}

static void run_one(FILE *out, const char *src, size_t len) {
    toc_op_list *list = new_list();
    toc_result rc = toc_load_clf(list, src, len);
    if (TOC_OK(rc)) {
        float img[16], in_copy[16];
        for (int i = 0; i < 16; i++) img[i] = randf();
        memcpy(in_copy, img, sizeof(img));
        toc_apply(list, img, 4, 4);
        emit_ok(out, list, src, len, in_copy, img, 4);
    } else {
        emit_fail(out, src, len, rc);
    }
    toc_op_list_free(list);
}

/* --- generators --- */

static void wrap(char *buf, size_t *len, const char *body) {
    sprintf(buf, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                 "<ProcessList xmlns=\"urn:AMP:CLF\" id=\"t\">\n");
    *len = strlen(buf);
    strcat(buf, body);
    *len = strlen(buf);
    strcat(buf, "</ProcessList>\n");
    *len = strlen(buf);
}

static void gen_matrix(FILE *out, int mode) {
    static const int shapes[6][2] = {{3,3},{3,4},{4,4},{4,5},{3,3},{4,4}};
    int mode2 = (int)(splitmix64() % 3u);
    int rows, cols;
    char dim[32];
    char *buf = malloc(65536);
    if (mode == 2) { /* bad shape -> UNSUPPORTED */
        sprintf(dim, "%d %d", 2 + (int)(splitmix64() % 2u), 2 + (int)(splitmix64() % 2u));
        rows = cols = 0;
        (void)rows; (void)cols;
    } else if (mode2 == 2) { /* legacy 3-dim form */
        int c = 3 + (int)(splitmix64() % 2u);
        sprintf(dim, "%d %d 3", c, c);
        rows = 3; cols = c;
    } else {
        rows = shapes[mode2][0]; cols = shapes[mode2][1];
        sprintf(dim, "%d %d", rows, cols);
    }
    char body[32768];
    char *p = body;
    if (splitmix64() & 1) p += sprintf(p, "<Description>generated matrix</Description>\n");
    if (splitmix64() & 1) p += sprintf(p, "<!-- a comment -->\n");
    const char *depths[] = {"16f", "8i", "10i", "12i", "16i", "32f"};
    const char *bd_in = depths[splitmix64() % 6u];
    const char *bd_out = depths[splitmix64() % 6u];
    p += sprintf(p, "<Matrix inBitDepth=\"%s\" outBitDepth=\"%s\">\n", bd_in, bd_out);
    p += sprintf(p, "<Array dim=\"%s\">\n", dim);
    int n = rows * cols;
    int emit = mode == 1 ? n - 1 : n;
    for (int i = 0; i < emit; i++) p += sprintf(p, "%.6f ", randf());
    p += sprintf(p, "\n</Array>\n");
    if ((splitmix64() & 1) && mode != 2)
        p += sprintf(p, "<Offset>%.6f %.6f %.6f</Offset>\n", randf(), randf(), randf());
    p += sprintf(p, "</Matrix>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_range(FILE *out, int mode) {
    /* mode: 0 full pairs, 1 min only, 2 max only, 3 noClamp full, 4 invalid (no pair) */
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    const char *extra = mode == 3 ? " style=\"noClamp\"" : "";
    p += sprintf(p, "<Range%s>\n", extra);
    float mnI = randf(), mxI = mnI + 0.5f + randf();
    float mnO = randf(), mxO = mnO + 0.5f + randf();
    if (mode == 0 || mode == 3) {
        p += sprintf(p, "<minInValue>%.6f</minInValue>\n", mnI);
        p += sprintf(p, "<minOutValue>%.6f</minOutValue>\n", mnO);
    }
    if (mode != 1 && mode != 4) {
        p += sprintf(p, "<maxInValue>%.6f</maxInValue>\n", mxI);
        p += sprintf(p, "<maxOutValue>%.6f</maxOutValue>\n", mxO);
    }
    if (mode == 1) { /* min only */
        p += sprintf(p, "<minInValue>%.6f</minInValue>\n", mnI);
        p += sprintf(p, "<minOutValue>%.6f</minOutValue>\n", mnO);
    }
    p += sprintf(p, "</Range>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_fixed(FILE *out) {
    char *buf = malloc(65536);
    char body[] = "<FixedFunction style=\"ACES\">\n<Descriptor>SKIP</Descriptor>\n</FixedFunction>\n";
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_unknown(FILE *out) {
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    p += sprintf(p, "<SomethingCustom><Child>a</Child><Other>1 2 3</Other></SomethingCustom>\n");
    /* a real Matrix after the skipped unknown node */
    p += sprintf(p, "<Matrix>\n<Array dim=\"3 3\">\n");
    for (int i = 0; i < 9; i++) p += sprintf(p, "%.6f ", randf());
    p += sprintf(p, "\n</Array>\n</Matrix>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_noprocess(FILE *out) {
    const char *src = "<?xml version=\"1.0\"?>\n<NotCLF/>\n";
    run_one(out, src, strlen(src));
}

static void gen_sequence(FILE *out) {
    char *buf = malloc(65536);
    char body[65536];
    char *p = body;
    /* Matrix then Range */
    p += sprintf(p, "<Matrix>\n<Array dim=\"3 3\">\n");
    for (int i = 0; i < 9; i++) p += sprintf(p, "%.6f ", randf());
    p += sprintf(p, "\n</Array>\n</Matrix>\n");
    p += sprintf(p, "<Range>\n<minInValue>0.0</minInValue>\n<maxInValue>1.0</maxInValue>\n"
                    "<minOutValue>0.0</minOutValue>\n<maxOutValue>1.0</maxOutValue>\n</Range>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}


static void gen_exponent(FILE *out, int mode) {
    const char *styles[] = {"basicFwd", "basicRev", "basicMirrorFwd",
        "monCurveFwd", "monCurveRev", "monCurveMirrorFwd",
        "basicPassThruFwd", "weirdStyle"};
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    float e = 0.5f + randf();
    p += sprintf(p, "<Exponent style=\"%s\">\n", styles[mode % 8]);
    if (mode % 8 == 7) {
        p += sprintf(p, "</Exponent>\n"); /* no params at all -> PARSE/UNSUPPORTED */
    } else {
        if (splitmix64() & 1)
            p += sprintf(p, "<ExponentParams exponent=\"%.6f\" channel=\"R\"/>\n", e);
        else
            p += sprintf(p, "<ExponentParams exponent=\"%.6f\"/>\n", e);
        if (strstr(styles[mode % 8], "monCurve"))
            p += sprintf(p, "<ExponentParams offset=\"%.6f\"/>\n", randf());
        p += sprintf(p, "</Exponent>\n");
    }
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_log(FILE *out, int mode) {
    const char *styles[] = {"log10", "log2", "antiLog10", "antiLog2",
        "linToLog", "logToLin", "cameraLinToLog", "cameraLogToLin"};
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    if (mode == 8) { /* self-closing simple log */
        p += sprintf(p, "<Log style=\"log10\"/>\n");
    } else if (mode == 9) { /* unknown style -> UNSUPPORTED */
        p += sprintf(p, "<Log style=\"linToLogEcho\"/>\n</Log>\n");
    } else {
        p += sprintf(p, "<Log style=\"%s\">\n", styles[mode % 8]);
        if (mode % 8 < 4) {
            p += sprintf(p, "</Log>\n");
        } else {
            p += sprintf(p, "<LogParams base=\"%.6f\" logSideSlope=\"%.6f\" "
                            "linearSlope=\"%.6f\"\n", 2.0f + randf(),
                         1.0f + randf(), 1.0f + randf());
            if (mode % 8 >= 6)
                p += sprintf(p, " linSideBreak=\"%.6f\"\n", randf() + 0.1f);
            p += sprintf(p, "/>\n</Log>\n");
        }
    }
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_cdl(FILE *out, int mode) {
    const char *styles[] = {"Fwd", "Rev", "FwdNoClamp", "RevNoClamp", "xyzStyle"};
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    p += sprintf(p, "<ASC_CDL style=\"%s\">\n", styles[mode % 5]);
    p += sprintf(p, "<SOPNode>\n<Slope>%.6f %.6f %.6f</Slope>\n"
                    "<Offset>%.6f %.6f %.6f</Offset>\n"
                    "<Power>%.6f %.6f %.6f</Power>\n</SOPNode>\n",
                 1.0f + randf(), 1.0f + randf(), 1.0f + randf(),
                 randf(), randf(), randf(),
                 1.0f + randf(), 1.0f + randf(), 1.0f + randf());
    if (mode % 5 != 4 || (splitmix64() & 1))
        p += sprintf(p, "<SatNode>\n<Saturation>%.6f</Saturation>\n</SatNode>\n", randf());
    p += sprintf(p, "</ASC_CDL>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}


static void gen_lut1d(FILE *out, int mode) {
    char *buf = malloc(65536);
    char body[32768];
    char *p = body;
    int length = 2 + (int)(splitmix64() % 13u);
    int comps = (splitmix64() & 1) ? 1 : 3;
    if (mode == 4) comps = 2;              /* parse fail */
    if (mode == 5) length = 261;           /* > cap? no (1<<20) so still ok */
    const char *bd[] = {"16f", "8i", "10i", "16i"};
    p += sprintf(p, "<LUT1D outBitDepth=\"%s\">\n", bd[splitmix64() % 4u]);
    if (mode == 6) p += sprintf(p, "<Array dim=\"4 2 3\">\n");
    else p += sprintf(p, "<Array dim=\"%d %d\">\n", length, comps);
    int emit = length * comps;
    if (mode == 1) emit -= 1;               /* truncated -> PARSE */
    for (int i = 0; i < emit; i++) p += sprintf(p, "%.6f ", randf());
    p += sprintf(p, "\n</Array>\n</LUT1D>\n");
    if (mode == 2) p += sprintf(p, "<Array dim=\"2 1\">\n0.1 0.2\n</Array>\n"); /* double Array -> PARSE */
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

static void gen_lut3d(FILE *out, int mode) {
    char *buf = malloc(6291456);
    char body[6291456];
    char *p = body;
    int N = 2 + (int)(splitmix64() % 3u);
    const char *interp = (splitmix64() & 1) ? "tetrahedral" : "trilinear";
    p += sprintf(p, "<LUT3D interpolation=\"%s\">\n", interp);
    if (mode == 5) p += sprintf(p, "<Array dim=\"%d %d %d\">\n", N, N, N);
    else p += sprintf(p, "<Array dim=\"%d %d %d 3\">\n", N, N, N);
    int total = N * N * N * 3;
    int emit = mode == 1 ? total - 3 : total;
    for (int i = 0; i < emit; i++) p += sprintf(p, "%.6f ", randf());
    p += sprintf(p, "\n</Array>\n</LUT3D>\n");
    size_t len;
    wrap(buf, &len, body);
    run_one(out, buf, len);
    free(buf);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0xfeedface12345678ULL;
    toc_simd_init();
    for (int s = 0; s < 72; s++) gen_matrix(out, 0);
    for (int s = 0; s < 8; s++) gen_matrix(out, 1);   /* truncated */
    for (int s = 0; s < 8; s++) gen_matrix(out, 2);   /* bad dim */
    for (int s = 0; s < 60; s++) gen_range(out, (int)(splitmix64() % 5u));
    for (int s = 0; s < 8; s++) gen_fixed(out);        /* UNSUPPORTED */
    for (int s = 0; s < 12; s++) gen_unknown(out);
    for (int s = 0; s < 4; s++) gen_noprocess(out);    /* PARSE */
    for (int s = 0; s < 16; s++) gen_sequence(out);
    for (int s = 0; s < 48; s++) gen_exponent(out, (int)(splitmix64() % 10u));
    for (int s = 0; s < 48; s++) gen_log(out, (int)(splitmix64() % 10u));
    for (int s = 0; s < 40; s++) gen_cdl(out, (int)(splitmix64() % 5u));
    for (int s = 0; s < 48; s++) gen_lut1d(out, (int)(splitmix64() % 7u));
    for (int s = 0; s < 24; s++) gen_lut3d(out, (int)(splitmix64() % 6u));
    fclose(out);
    return 0;
}
