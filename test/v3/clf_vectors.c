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
    fclose(out);
    return 0;
}
