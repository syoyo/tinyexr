/* SPI file differential vectors: C parse (+apply) vs Lean parse+apply.
 * Line format:
 *   spi1d ok lut1d <len> <ch> <dmin> <dmax> <interp> <data...> <in...> | <out...> || <src_hex>
 *   spi1d fail || <src_hex>
 *   spi3d ok lut3d <size> <dmin> <dmax> <interp> <data...> <in...> | <out...> || <src_hex>
 *   spi3d fail || <src_hex>
 * Hex: float bits or source bytes, 8/2 hex chars per word. */
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

static void emit_result(FILE *out, const char *kind, const toc_op_list *list,
                        const char *src, size_t len, const float *img,
                        size_t npix, int fail) {
    if (fail) {
        fprintf(out, "%s fail || ", kind);
        print_hex_src(out, src, len);
        fprintf(out, "\n");
        return;
    }
    for (size_t k = 0; k < list->count; k++) {
        const toc_op *op = &list->ops[k];
        if (op->kind == TOC_OP_LUT1D) {
            fprintf(out, "%s ok lut1d %d %d %08x %08x %d", kind,
                    op->u.lut1d.length, op->u.lut1d.channels,
                    *(uint32_t *)&op->u.lut1d.domain_min,
                    *(uint32_t *)&op->u.lut1d.domain_max, op->u.lut1d.interp);
            print_f32bits(out, op->u.lut1d.data,
                          (size_t)op->u.lut1d.length * (size_t)op->u.lut1d.channels);
        } else if (op->kind == TOC_OP_LUT3D) {
            fprintf(out, "%s ok lut3d %d %08x %08x %d", kind, op->u.lut3d.size,
                    *(uint32_t *)&op->u.lut3d.domain_min[0],
                    *(uint32_t *)&op->u.lut3d.domain_max[0], op->u.lut3d.interp);
            print_f32bits(out, op->u.lut3d.data,
                          (size_t)op->u.lut3d.size * (size_t)op->u.lut3d.size *
                              (size_t)op->u.lut3d.size * 3);
        }
    }
    fprintf(out, " ");
    print_f32bits(out, img, npix * 4);
    fprintf(out, " |");
    /* out pixels were already printed by caller via img; see below */
    fprintf(out, " || ");
    print_hex_src(out, src, len);
    fprintf(out, "\n");
    (void)out;
}

/* emit with in|out split */
static void emit_ok(FILE *out, const char *kind, const toc_op_list *list,
                    const char *src, size_t len, const float *in_img,
                    const float *out_img, size_t npix) {
    for (size_t k = 0; k < list->count; k++) {
        const toc_op *op = &list->ops[k];
        if (op->kind == TOC_OP_LUT1D) {
            fprintf(out, "%s ok lut1d %d %d %08x %08x %d", kind,
                    op->u.lut1d.length, op->u.lut1d.channels,
                    *(uint32_t *)&op->u.lut1d.domain_min,
                    *(uint32_t *)&op->u.lut1d.domain_max, op->u.lut1d.interp);
            print_f32bits(out, op->u.lut1d.data,
                          (size_t)op->u.lut1d.length * (size_t)op->u.lut1d.channels);
        } else if (op->kind == TOC_OP_LUT3D) {
            fprintf(out, "%s ok lut3d %d %08x %08x %d", kind, op->u.lut3d.size,
                    *(uint32_t *)&op->u.lut3d.domain_min[0],
                    *(uint32_t *)&op->u.lut3d.domain_max[0], op->u.lut3d.interp);
            print_f32bits(out, op->u.lut3d.data,
                          (size_t)op->u.lut3d.size * (size_t)op->u.lut3d.size *
                              (size_t)op->u.lut3d.size * 3);
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

/* .spi1d: Version/From/Length/Components header, `{ v* }` body. */
static void gen_spi1d(FILE *out, int fail_mode) {
    int length = 2 + (int)(splitmix64() % 19u);
    int comps = (splitmix64() & 1) ? 1 : 3;
    float from0 = randf(), from1 = randf();
    char *buf = malloc(65536);
    char *p = buf;
    if (splitmix64() & 1) p += sprintf(p, "Version 1\n");
    /* occasionally exponent notation */
    if (splitmix64() & 1)
        p += sprintf(p, "From %.6fe+03 %.6f\n", from0 / 1000.0f, from1 + 1.0f);
    else
        p += sprintf(p, "From %.6f %.6f\n", from0, from1 + 1.0f);
    p += sprintf(p, "Length %d\n", length);
    p += sprintf(p, "Components %d\n", comps);
    p += sprintf(p, "# comment line\n");
    if (splitmix64() & 1) p += sprintf(p, "{\n");
    int want = length * comps;
    int emit = want;
    if (fail_mode == 1) emit = want - 1; /* truncated body */
    for (int i = 0; i < emit; i++) {
        if (i % 4 == 0 && (splitmix64() & 1)) p += sprintf(p, "  # mid comment\n");
        p += sprintf(p, "%.6f ", randf());
    }
    if (splitmix64() & 1) p += sprintf(p, "\n}\n");
    size_t len = (size_t)(p - buf);
    toc_op_list *list = new_list();
    toc_result rc = toc_load_lutfile(list, "t.spi1d", buf, len, 0);
    if (fail_mode == 0 && TOC_OK(rc) && list->count) {
        float img[16], in_copy[16];
        for (int i = 0; i < 16; i++) img[i] = randf();
        memcpy(in_copy, img, sizeof(img));
        toc_apply(list, img, 4, 4);
        emit_ok(out, "spi1d", list, buf, len, in_copy, img, 4);
    } else {
        emit_result(out, "spi1d", list, buf, len, NULL, 0, 1);
    }
    free(buf);
    toc_op_list_free(list);
}

/* .spi3d: SPILUT ver nin nout N N N + N^3 (ir ig ib r g b) rows. */
static void gen_spi3d(FILE *out, int fail_mode) {
    int N = 2 + (int)(splitmix64() % 4u);
    char *buf = malloc(6291456);
    char *p = buf;
    p += sprintf(p, "SPILUT 1.0\n3 3\n%d %d %d\n", N, N, N);
    int total = N * N * N;
    /* random permutation of indices so rows are unordered */
    int *perm = malloc(sizeof(int) * (size_t)total);
    for (int i = 0; i < total; i++) perm[i] = i;
    for (int i = total - 1; i > 0; i--) {
        int j = (int)(splitmix64() % (uint64_t)(i + 1));
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    int rows = total;
    if (fail_mode == 1) rows = total - 1; /* truncated */
    for (int k = 0; k < rows; k++) {
        int idx = perm[k];
        int ir = idx % N, ig = (idx / N) % N, ib = idx / (N * N);
        if (fail_mode == 2 && k == 0) ir = N; /* out of range */
        p += sprintf(p, "%d %d %d %.6f %.6f %.6f\n", ir, ig, ib,
                     randf(), randf(), randf());
    }
    free(perm);
    size_t len = (size_t)(p - buf);
    toc_op_list *list = new_list();
    toc_result rc = toc_load_lutfile(list, "t.spi3d", buf, len, 0);
    if (fail_mode == 0 && TOC_OK(rc) && list->count) {
        float img[16], in_copy[16];
        for (int i = 0; i < 16; i++) img[i] = randf();
        memcpy(in_copy, img, sizeof(img));
        toc_apply(list, img, 4, 4);
        emit_ok(out, "spi3d", list, buf, len, in_copy, img, 4);
    } else {
        emit_result(out, "spi3d", list, buf, len, NULL, 0, 1);
    }
    free(buf);
    toc_op_list_free(list);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0xabcdef123456789ULL;
    toc_simd_init();
    for (int s = 0; s < 120; s++) gen_spi1d(out, 0);
    for (int s = 0; s < 48; s++) gen_spi3d(out, 0);
    /* failure parity cases */
    for (int s = 0; s < 12; s++) gen_spi1d(out, 1);
    for (int s = 0; s < 12; s++) gen_spi3d(out, 1);
    for (int s = 0; s < 8; s++) gen_spi3d(out, 2);
    fclose(out);
    return 0;
}
