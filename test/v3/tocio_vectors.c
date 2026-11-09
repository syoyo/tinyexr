/* Tocio differential vectors: C toc_apply vs Lean op kernels. */
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

static float randf(void) {
    return (float)(splitmix64() % 4000u) / 1000.0f - 1.0f;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0x123456789abcdefULL;
    toc_simd_init();
    toc_op op;
    memset(&op, 0, sizeof(op));
    op.kind = TOC_OP_MATRIX;
    float img[4 * 4];
    for (int s = 0; s < 512; s++) {
        for (int i = 0; i < 16; i++) op.u.matrix.m[i] = randf();
        for (int i = 0; i < 4; i++) op.u.matrix.off[i] = randf();
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "matrix ");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, op.u.matrix.m + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.matrix.off + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        /* re-randomize input for range below */
        for (int i = 0; i < 16; i++) img[i] = randf();
        free(list.ops);
    }
    /* Range vectors. */
    for (int s = 0; s < 512 * 2; s++) {
        op.kind = TOC_OP_RANGE;
        for (int i = 0; i < 4; i++) {
            op.u.range.scale[i] = randf();
            op.u.range.offset[i] = randf();
            op.u.range.min[i] = randf();
            op.u.range.max[i] = 1.0f + randf();
        }
        op.u.range.clamp_lo = (int)(splitmix64() & 1u);
        op.u.range.clamp_hi = (int)(splitmix64() & 1u);
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "range ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.range.scale + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.range.offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.range.min + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.range.max + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d %d |", op.u.range.clamp_lo, op.u.range.clamp_hi);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }

    /* Exponent vectors (mirror + non-mirror). */
    for (int s = 0; s < 512; s++) {
        op.kind = TOC_OP_EXPONENT;
        int mirror = (int)(splitmix64() & 1u);
        for (int i = 0; i < 4; i++) op.u.exponent.e[i] = 0.5f + randf();
        op.u.exponent.mirror = mirror;
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "exponent ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exponent.e + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d |", mirror);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }
    /* Log / LogCam / ExpLinear / CDL vectors. */
    for (int s = 0; s < 256; s++) {
        /* Log */
        op.kind = TOC_OP_LOG;
        op.u.log.base = 2.0f;
        int inv = (int)(splitmix64() & 1u);
        op.u.log.inverse = inv;
        for (int i = 0; i < 3; i++) {
            op.u.log.log_slope[i] = 1.0f + randf();
            op.u.log.log_offset[i] = randf();
            op.u.log.lin_slope[i] = 1.0f + randf();
            op.u.log.lin_offset[i] = randf();
        }
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "log ");
        uint32_t ub;
        memcpy(&ub, &op.u.log.base, 4);
        fprintf(out, "%08x ", ub);
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.log.log_slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.log.log_offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.log.lin_slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.log.lin_offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d |", inv);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }
    /* LogCam */
    for (int s = 0; s < 256; s++) {
        op.kind = TOC_OP_LOG_CAMERA;
        op.u.logcam.base = 2.0f;
        int inv = (int)(splitmix64() & 1u);
        op.u.logcam.inverse = inv;
        for (int i = 0; i < 3; i++) {
            op.u.logcam.log_slope[i] = 1.0f + randf();
            op.u.logcam.log_offset[i] = randf();
            op.u.logcam.lin_slope[i] = 1.0f + randf();
            op.u.logcam.lin_offset[i] = randf();
            op.u.logcam.lin_break[i] = 0.5f + randf();
            op.u.logcam.linear_slope[i] = 1.0f + randf();
            op.u.logcam.linear_offset[i] = randf();
        }
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "logcam ");
        uint32_t ub;
        memcpy(&ub, &op.u.logcam.base, 4);
        fprintf(out, "%08x ", ub);
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.log_slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.log_offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.lin_slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.lin_offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.lin_break + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.linear_slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.logcam.linear_offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d |", inv);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }
    /* ExpLinear */
    for (int s = 0; s < 256; s++) {
        op.kind = TOC_OP_EXP_LINEAR;
        int inv = (int)(splitmix64() & 1u);
        int mir = (int)(splitmix64() & 1u);
        op.u.exp_linear.inverse = inv;
        op.u.exp_linear.mirror = mir;
        for (int i = 0; i < 4; i++) {
            op.u.exp_linear.scale[i] = 1.0f + randf();
            op.u.exp_linear.offset[i] = randf();
            op.u.exp_linear.gamma[i] = 1.0f + randf();
            op.u.exp_linear.breakpoint[i] = 0.5f + randf();
            op.u.exp_linear.slope[i] = 1.0f + randf();
        }
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "explin ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exp_linear.scale + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exp_linear.offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exp_linear.gamma + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exp_linear.breakpoint + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 4; i++) {
            uint32_t u;
            memcpy(&u, op.u.exp_linear.slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d %d |", inv, mir);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }
    /* CDL */
    for (int s = 0; s < 256; s++) {
        op.kind = TOC_OP_CDL;
        int inv = (int)(splitmix64() & 1u);
        int clamp = (int)(splitmix64() & 1u);
        op.u.cdl.inverse = inv;
        op.u.cdl.clamp = clamp;
        op.u.cdl.saturation = 0.5f + randf();
        for (int i = 0; i < 3; i++) {
            op.u.cdl.slope[i] = 1.0f + randf();
            op.u.cdl.offset[i] = randf();
            op.u.cdl.power[i] = 1.0f + randf();
        }
        for (int i = 0; i < 3; i++) op.u.cdl.luma[i] = randf();
        for (int i = 0; i < 16; i++) img[i] = randf();
        toc_op_list list;
        memset(&list, 0, sizeof(list));
        list.ops = malloc(sizeof(toc_op));
        list.ops[0] = op;
        list.count = 1;
        float in_copy[16];
        memcpy(in_copy, img, sizeof(img));
        toc_apply(&list, img, 4, 4);
        fprintf(out, "cdl ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.cdl.slope + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.cdl.offset + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " ");
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.cdl.power + i, 4);
            fprintf(out, " %08x", u);
        }
        uint32_t us;
        memcpy(&us, &op.u.cdl.saturation, 4);
        fprintf(out, " %08x ", us);
        for (int i = 0; i < 3; i++) {
            uint32_t u;
            memcpy(&u, op.u.cdl.luma + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " %d %d |", clamp, inv);
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, in_copy + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            uint32_t u;
            memcpy(&u, img + i, 4);
            fprintf(out, " %08x", u);
        }
        fprintf(out, "\n");
        free(list.ops);
    }
    fclose(out);
    return 0;
}
