/* CSP differential vectors: C parse (+apply) vs Lean loadCsp.
 * Line format (same as clf_vectors):
 *   clf ok ops <n> [matrix <16> <4> | lut1d <len> <data> | lut3d <n> <tetra> <data>]
 *        <in...> | <out...> || <src_hex>
 *   clf fail parse|unsupported || <src_hex> */
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
    fprintf(out, "csp ok ops %zu", list->count);
    for (size_t k = 0; k < list->count; k++) {
        const toc_op *op = &list->ops[k];
        if (op->kind == TOC_OP_MATRIX) {
            fprintf(out, " matrix");
            print_f32bits(out, op->u.matrix.m, 16);
            print_f32bits(out, op->u.matrix.off, 4);
        } else if (op->kind == TOC_OP_LUT1D) {
            fprintf(out, " lut1d %d", op->u.lut1d.length);
            print_f32bits(out, op->u.lut1d.data, (size_t)op->u.lut1d.length * 3);
        } else if (op->kind == TOC_OP_LUT3D) {
            fprintf(out, " lut3d %d %d", op->u.lut3d.size, op->u.lut3d.interp);
            print_f32bits(out, op->u.lut3d.data,
                          (size_t)op->u.lut3d.size * (size_t)op->u.lut3d.size *
                              (size_t)op->u.lut3d.size * 3);
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
    fprintf(out, "csp fail %s || ",
            rc == TOC_ERROR_UNSUPPORTED ? "unsupported" : "parse");
    print_hex_src(out, src, len);
    fprintf(out, "\n");
}

static void run_one(FILE *out, const char *src, size_t len) {
    toc_op_list *list = new_list();
    toc_result rc = toc_load_csp(list, src, len);
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

/* Plain: 1D/3D, no preluts, no metadata. */
static void gen_plain(FILE *out, int is3d) {
    char *buf = malloc(6291456);
    char *p = buf;
    if (splitmix64() & 1) p += sprintf(p, "cspLutv100\n"); /* case-insensitive magic */
    else p += sprintf(p, "CSPLUTV100\n");
    p += sprintf(p, is3d ? "3D\n" : "1D\n");
    if (splitmix64() & 1) p += sprintf(p, "\n  \n"); /* blank lines ignored */
    if (splitmix64() & 1) {
        p += sprintf(p, "BEGIN METADATA\nTitle: generated\n\nEND METADATA\n");
    }
    p += sprintf(p, "0\n0\n0\n");
    if (is3d) {
        int N = 2 + (int)(splitmix64() % 3u);
        p += sprintf(p, "%d %d %d\n", N, N, N);
        int n3 = N * N * N;
        for (int i = 0; i < n3; i++)
            p += sprintf(p, "%.6f %.6f %.6f\n", randf(), randf(), randf());
    } else {
        int N = 2 + (int)(splitmix64() % 13u);
        p += sprintf(p, "%d\n", N);
        for (int i = 0; i < N; i++)
            p += sprintf(p, "%.6f %.6f %.6f\n", randf(), randf(), randf());
    }
    run_one(out, buf, (size_t)(p - buf));
    free(buf);
}

/* Prelut variant: per-channel count + input + output lines. */
static void gen_prelut(FILE *out, int mode) {
    char *buf = malloc(6291456);
    char *p = buf;
    p += sprintf(p, "CSPLUTV100\n1D\n");
    for (int ch = 0; ch < 3; ch++) {
        int cnt = mode == 1 ? 2 : (2 + (int)(splitmix64() % 4u));
        int ident = (splitmix64() & 1);
        p += sprintf(p, "%d\n", cnt);
        /* inputs: increasing sequence */
        float prev = randf();
        float ins[8], outs[8];
        for (int i = 0; i < cnt; i++) {
            prev += 0.5f + randf();
            ins[i] = prev;
            outs[i] = ident ? prev : prev + randf() * 0.1f;
        }
        for (int i = 0; i < cnt; i++) p += sprintf(p, "%.6f ", ins[i]);
        p += sprintf(p, "\n");
        for (int i = 0; i < cnt; i++) p += sprintf(p, "%.6f ", outs[i]);
        p += sprintf(p, "\n");
    }
    int N = 2 + (int)(splitmix64() % 5u);
    p += sprintf(p, "%d\n", N);
    for (int i = 0; i < N; i++)
        p += sprintf(p, "%.6f %.6f %.6f\n", randf(), randf(), randf());
    run_one(out, buf, (size_t)(p - buf));
    free(buf);
}

/* Failure parity fixtures. */
static void gen_bad(FILE *out, int mode) {
    static const char *srcs[] = {
        "CSPLUTV100\n2D\n",                                      /* UNSUPPORTED */
        "NOTACSP\n1D\n",                                         /* PARSE */
        "CSPLUTV100\n1D\n0\n0\n0\n1\n0.0 0.0 0.0\n",             /* n<2 PARSE */
        "CSPLUTV100\n1D\n0\n0\n0\n3\n0.1 0.2 0.3\nbad line\n0.4 0.5 0.6\n", /* junk line */
        "CSPLUTV100\n3D\n0\n0\n0\n3 3 4\n",                      /* unequal dims PARSE */
        "CSPLUTV100\n1D\n0\n0\n",                                /* missing counts */
        "CSPLUTV100\n",                                          /* missing dim line */
        "CSPLUTV100\n1D\n2\n0.0 1.0\n0.0 1.0 0.0 extra\n0\n0\n0\n3\n0.1 0.2 0.3\n0.1 0.2 0.3\n0.1 0.2 0.3\n", /* count line wonk: prelut needs 2 lines; first data line has 'extra' token */
        "CSPLUTV100\n1D\n0\n0\n0\n2\n0.1 0.2 0.3\n0.4 0.5 0.6 7.7\n",        /* 4 floats on LUT line */
    };
    run_one(out, srcs[mode % 9], strlen(srcs[mode % 9]));
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0xc0ffee123456789ULL;
    toc_simd_init();
    for (int s = 0; s < 48; s++) gen_plain(out, s & 1);
    for (int s = 0; s < 8; s++) gen_prelut(out, s & 1);
    for (int s = 0; s < 18; s++) gen_bad(out, s);
    fclose(out);
    return 0;
}
