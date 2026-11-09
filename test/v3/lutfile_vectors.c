/* LUT-file differential vectors: C LUT parse+apply vs Lean. */
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

static void rand_img(float *img, size_t n) {
    for (size_t i = 0; i < n; i++) img[i] = randf();
}

static void print_pixels(FILE *out, const float *in, const float *out_img, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint32_t u;
        memcpy(&u, in + i, 4);
        fprintf(out, " %08x", u);
    }
    fprintf(out, " |");
    for (size_t i = 0; i < n; i++) {
        uint32_t u;
        memcpy(&u, out_img + i, 4);
        fprintf(out, " %08x", u);
    }
    fprintf(out, "\n");
}

static void print_lut1d(FILE *out, const toc_op *op) {
    fprintf(out, " lut1d %d %d %08x %08x %d", op->u.lut1d.length,
            op->u.lut1d.channels,
            *(uint32_t *)&op->u.lut1d.domain_min,
            *(uint32_t *)&op->u.lut1d.domain_max, op->u.lut1d.interp);
    for (int i = 0; i < op->u.lut1d.length * op->u.lut1d.channels; i++) {
        uint32_t u;
        memcpy(&u, op->u.lut1d.data + i, 4);
        fprintf(out, " %08x", u);
    }
}

static void print_lut3d(FILE *out, const toc_op *op) {
    fprintf(out, " lut3d %d %08x %08x %d", op->u.lut3d.size,
            *(uint32_t *)&op->u.lut3d.domain_min[0],
            *(uint32_t *)&op->u.lut3d.domain_max[0], op->u.lut3d.interp);
    for (int i = 0; i < op->u.lut3d.size * op->u.lut3d.size *
            op->u.lut3d.size * 3; i++) {
        uint32_t u;
        memcpy(&u, op->u.lut3d.data + i, 4);
        fprintf(out, " %08x", u);
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    toc_simd_init();
    float img[16];
    /* .cube: 1D and 3D, trilinear + tetrahedral variants */
    for (int s = 0; s < 144; s++) {
        int is3d = (s & 1) && (((s >> 1) & 1) || (s % 3 == 0));
        toc_op_list *list = new_list();
        if (is3d) {
            int n = 2 + (int)(splitmix64() % 4u);
            char *buf = malloc(6291456);
            char *p = buf;
            p += sprintf(p, "TITLE \"t\"\nLUT_3D_SIZE %d\n", n);
            int count = n * n * n;
            for (int i = 0; i < count; i++)
                p += sprintf(p, "%.6f %.6f %.6f\n", randf(), randf(), randf());
            toc_result rc = toc_load_lutfile(list, "t.cube", buf, p - buf, 0);
            if (TOC_OK(rc) && list->count) {
                rand_img(img, 16);
                for (int variant = 0; variant < 2; variant++) {
                    for (size_t k = 0; k < list->count; k++)
                        if (list->ops[k].kind == TOC_OP_LUT3D)
                            list->ops[k].u.lut3d.interp =
                                variant ? TOC_INTERP_TETRAHEDRAL
                                        : TOC_INTERP_TRILINEAR;
                    float in_copy[16];
                    memcpy(in_copy, img, sizeof(img));
                    toc_apply(list, img, 4, 4);
                    fprintf(out, "%s", variant ? "cube3dt" : "cube3d");
                    for (size_t k = 0; k < list->count; k++)
                        if (list->ops[k].kind == TOC_OP_LUT3D)
                            print_lut3d(out, &list->ops[k]);
                    print_pixels(out, in_copy, img, 16);
                }
            }
            free(buf);
            toc_op_list_free(list);
        } else {
            int n = 2 + (int)(splitmix64() % 19u);
            char buf[8192];
            char *p = buf;
            p += sprintf(p, "TITLE \"t\"\nLUT_1D_SIZE %d\n", n);
            for (int i = 0; i < n; i++)
                p += sprintf(p, "%.6f %.6f %.6f\n", randf(), randf(), randf());
            toc_result rc = toc_load_lutfile(list, "t.cube", buf, p - buf, 0);
            if (TOC_OK(rc) && list->count) {
                rand_img(img, 4);
                float in_copy[4];
                memcpy(in_copy, img, sizeof(in_copy));
                toc_apply(list, img, 1, 4);
                fprintf(out, "cube1d");
                for (size_t k = 0; k < list->count; k++)
                    if (list->ops[k].kind == TOC_OP_LUT1D)
                        print_lut1d(out, &list->ops[k]);
                print_pixels(out, in_copy, img, 4);
            }
            toc_op_list_free(list);
        }
    }
    fclose(out);
    return 0;
}
