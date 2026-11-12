/* GLSL codegen differential vectors: C `toc_emit_glsl` vs the Lean port
 * (`Tocio/CodegenGLSL.lean`).
 *
 * Records:
 *   ggtarget <id> <es30|330|vulkan>
 *   ggop <id> <kind> <params...>       same recipe format as the AOT-C gate
 *   ggtex <id> <name> <dim> <w> <h> <d> <ch> <interp>
 *   ggdoc <id> | <hex of the emitted shader source>
 *
 * ACES 2.0 output transforms are excluded (they need the precomputed
 * `toc_aces2` blob); everything else is covered.
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

static uint32_t fbits(float f) {
    uint32_t u;
    memcpy(&u, &f, 4);
    return u;
}

#define N_DOCS 8

typedef struct {
    int kind;
    float f[64];
    int i[8];
} cop;

static cop docs[N_DOCS][16];
static int doc_n[N_DOCS];
static const char *doc_target[N_DOCS];

static void emit_bits(FILE *out, const float *f, int n) {
    for (int i = 0; i < n; i++) fprintf(out, " %08x", fbits(f[i]));
}

static void emit_recipe(FILE *out, size_t id, const cop *c) {
    switch (c->kind) {
    case TOC_OP_MATRIX:
        fprintf(out, "ggop %zu matrix", id); emit_bits(out, c->f, 20); break;
    case TOC_OP_RANGE:
        fprintf(out, "ggop %zu range", id); emit_bits(out, c->f, 16);
        fprintf(out, " %d %d", c->i[0], c->i[1]); break;
    case TOC_OP_EXPONENT:
        fprintf(out, "ggop %zu exponent", id); emit_bits(out, c->f, 4);
        fprintf(out, " %d", c->i[0]); break;
    case TOC_OP_EXP_LINEAR:
        fprintf(out, "ggop %zu explinear", id); emit_bits(out, c->f, 20);
        fprintf(out, " %d %d", c->i[0], c->i[1]); break;
    case TOC_OP_LOG:
        fprintf(out, "ggop %zu log", id); emit_bits(out, c->f, 13);
        fprintf(out, " %d", c->i[0]); break;
    case TOC_OP_LOG_CAMERA:
        fprintf(out, "ggop %zu logcam", id); break;
    case TOC_OP_CDL:
        fprintf(out, "ggop %zu cdl", id); emit_bits(out, c->f, 13);
        fprintf(out, " %d %d", c->i[0], c->i[1]); break;
    case TOC_OP_LUT1D: {
        int len = c->i[0], ch = c->i[1];
        fprintf(out, "ggop %zu lut1d %d %d", id, len, ch);
        emit_bits(out, c->f, 2 + len * (ch == 1 ? 1 : 3));
        break;
    }
    case TOC_OP_LUT3D: {
        int size = c->i[0];
        fprintf(out, "ggop %zu lut3d %d %d", id, size, c->i[1]);
        emit_bits(out, c->f, 6 + size * size * size * 3);
        break;
    }
    case TOC_OP_FIXEDFUNC:
        fprintf(out, "ggop %zu fixed %d %d", id, c->i[0], c->i[1]);
        emit_bits(out, c->f, 8); break;
    default: break;
    }
    fputc('\n', out);
}

static toc_op_list *build_list(const cop *ops, size_t n) {
    toc_op_list *list = (toc_op_list *)calloc(1, sizeof(toc_op_list));
    if (!list) return NULL;
    list->alloc = *toc_default_allocator();
    for (size_t k = 0; k < n; k++) {
        const cop *c = &ops[k];
        toc_op *op = toc_op_list_push(list, (toc_op_kind)c->kind);
        if (!op) { toc_op_list_free(list); return NULL; }
        switch (c->kind) {
        case TOC_OP_MATRIX:
            for (int j = 0; j < 16; j++) op->u.matrix.m[j] = c->f[j];
            for (int j = 0; j < 4; j++) op->u.matrix.off[j] = c->f[16 + j];
            break;
        case TOC_OP_RANGE:
            for (int j = 0; j < 4; j++) {
                op->u.range.scale[j] = c->f[j];
                op->u.range.offset[j] = c->f[4 + j];
                op->u.range.min[j] = c->f[8 + j];
                op->u.range.max[j] = c->f[12 + j];
            }
            op->u.range.clamp_lo = c->i[0];
            op->u.range.clamp_hi = c->i[1];
            break;
        case TOC_OP_EXPONENT:
            for (int j = 0; j < 4; j++) op->u.exponent.e[j] = c->f[j];
            op->u.exponent.mirror = c->i[0];
            break;
        case TOC_OP_EXP_LINEAR:
            for (int j = 0; j < 4; j++) {
                op->u.exp_linear.scale[j] = c->f[j];
                op->u.exp_linear.offset[j] = c->f[4 + j];
                op->u.exp_linear.gamma[j] = c->f[8 + j];
                op->u.exp_linear.breakpoint[j] = c->f[12 + j];
                op->u.exp_linear.slope[j] = c->f[16 + j];
            }
            op->u.exp_linear.inverse = c->i[0];
            op->u.exp_linear.mirror = c->i[1];
            break;
        case TOC_OP_LOG:
            for (int j = 0; j < 3; j++) {
                op->u.log.log_slope[j] = c->f[j];
                op->u.log.log_offset[j] = c->f[3 + j];
                op->u.log.lin_slope[j] = c->f[6 + j];
                op->u.log.lin_offset[j] = c->f[9 + j];
            }
            op->u.log.base = c->f[12];
            op->u.log.inverse = c->i[0];
            break;
        case TOC_OP_LOG_CAMERA:
            break;
        case TOC_OP_CDL:
            for (int j = 0; j < 3; j++) {
                op->u.cdl.slope[j] = c->f[j];
                op->u.cdl.offset[j] = c->f[3 + j];
                op->u.cdl.power[j] = c->f[6 + j];
                op->u.cdl.luma[j] = c->f[10 + j];
            }
            op->u.cdl.saturation = c->f[9];
            op->u.cdl.clamp = c->i[0];
            op->u.cdl.inverse = c->i[1];
            break;
        case TOC_OP_LUT1D: {
            int len = c->i[0], ch = c->i[1];
            op->u.lut1d.data = (float *)(c->f + 2);
            op->u.lut1d.length = len;
            op->u.lut1d.channels = ch;
            op->u.lut1d.domain_min = c->f[0];
            op->u.lut1d.domain_max = c->f[1];
            op->u.lut1d.interp = TOC_INTERP_LINEAR;
            break;
        }
        case TOC_OP_LUT3D: {
            int size = c->i[0];
            op->u.lut3d.data = (float *)(c->f + 6);
            op->u.lut3d.size = size;
            for (int j = 0; j < 3; j++) {
                op->u.lut3d.domain_min[j] = c->f[j];
                op->u.lut3d.domain_max[j] = c->f[3 + j];
            }
            op->u.lut3d.interp =
                c->i[1] ? TOC_INTERP_TETRAHEDRAL : TOC_INTERP_TRILINEAR;
            break;
        }
        case TOC_OP_FIXEDFUNC:
            op->u.fixedfunc.style = c->i[0];
            op->u.fixedfunc.nparams = c->i[1];
            for (int j = 0; j < 8; j++) op->u.fixedfunc.params[j] = c->f[j];
            break;
        default: break;
        }
    }
    return list;
}

static cop *add(int id, int kind) {
    cop *c = &docs[id][doc_n[id]++];
    memset(c, 0, sizeof(*c));
    c->kind = kind;
    return c;
}

static void setf(float *dst, int n, const float *v) {
    for (int i = 0; i < n; i++) dst[i] = v[i];
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }

    /* 0: matrix + range (both clamp modes) + exponent, ES3.0 */
    {
        cop *c = add(0, TOC_OP_MATRIX);
        float m[16] = {1.5f, 0.25f, 0, 0, 0, 1.5f, 0, 0, 0, 0, 1.5f, 0,
                       0.1f, 0.2f, 0.3f, 1.0f};
        setf(c->f, 16, m);
        c->f[16] = 0.5f; c->f[17] = -0.25f; c->f[18] = 0.0f; c->f[19] = 0.125f;
        c = add(0, TOC_OP_RANGE);
        {
            float sc[4] = {2.0f, 0.5f, 1.0f, 1.0f};
            float ro[4] = {-1.0f, 0.25f, 0, 0};
            float lo[4] = {0, 0.1f, -3.4e38f, -3.4e38f};
            float hi[4] = {1.0f, 0.9f, 3.4e38f, 3.4e38f};
            setf(c->f, 4, sc); setf(c->f + 4, 4, ro);
            setf(c->f + 8, 4, lo); setf(c->f + 12, 4, hi);
            c->i[0] = 1; c->i[1] = 0;
        }
        c = add(0, TOC_OP_RANGE);
        {
            float v[4] = {1, 1, 1, 1};
            setf(c->f, 4, v); setf(c->f + 4, 4, v); setf(c->f + 8, 4, v);
            setf(c->f + 12, 4, v);
            c->i[0] = -0; c->i[1] = 0;
        }
        c = add(0, TOC_OP_EXPONENT);
        { float e[4] = {2.2f, 0.5f, 1.0f, 1.0f}; setf(c->f, 4, e); c->i[0] = 0; }
        c = add(0, TOC_OP_EXPONENT);
        { float e[4] = {2.2f, 2.2f, 2.2f, 1.0f}; setf(c->f, 4, e); c->i[0] = 1; }
        doc_target[0] = "es30";
    }
    /* 1: log forward/inverse + exp-linear mirrored/inverse, GLSL 330 */
    {
        cop *c = add(1, TOC_OP_LOG);
        {
            float ls[3] = {1, 1, 1}, lo[3] = {0, 0, 0}, ns[3] = {1, 1, 1}, no[3] = {0, 0, 0};
            for (int j = 0; j < 3; j++) {
                c->f[j] = ls[j]; c->f[3 + j] = lo[j]; c->f[6 + j] = ns[j]; c->f[9 + j] = no[j];
            }
            c->f[12] = 2.0f; c->i[0] = 0;
        }
        c = add(1, TOC_OP_LOG);
        {
            float ls[3] = {0.5f, 0.5f, 0.5f}, lo[3] = {0.1f, 0.1f, 0.1f};
            float ns[3] = {2, 2, 2}, no[3] = {-0.5f, -0.5f, -0.5f};
            for (int j = 0; j < 3; j++) {
                c->f[j] = ls[j]; c->f[3 + j] = lo[j]; c->f[6 + j] = ns[j]; c->f[9 + j] = no[j];
            }
            c->f[12] = 10.0f; c->i[0] = 1;
        }
        c = add(1, TOC_OP_EXP_LINEAR);
        {
            float sc[4] = {0.9f, 0.9f, 0.9f, 1.0f};
            float of[4] = {0.0625f, 0.0625f, 0.0625f, 0};
            float ga[4] = {2.4f, 2.4f, 2.4f, 1.0f};
            float br[4] = {0.04045f, 0.04045f, 0.04045f, 0};
            float sl[4] = {0.0472f, 0.0472f, 0.0472f, 1.0f};
            setf(c->f, 4, sc); setf(c->f + 4, 4, of); setf(c->f + 8, 4, ga);
            setf(c->f + 12, 4, br); setf(c->f + 16, 4, sl);
            c->i[0] = 1; c->i[1] = 1;
        }
        doc_target[1] = "330";
    }
    /* 2: CDL forward/inverse + 1D and 3D LUTs, ES3.0 */
    {
        cop *c = add(2, TOC_OP_CDL);
        {
            float sl[3] = {1.1f, 0.9f, 0.8f}, of[3] = {0.01f, -0.02f, 0.03f};
            float pw[3] = {0.9f, 1.0f, 1.2f}, lu[3] = {0.2126f, 0.7152f, 0.0722f};
            for (int j = 0; j < 3; j++) {
                c->f[j] = sl[j]; c->f[3 + j] = of[j]; c->f[6 + j] = pw[j]; c->f[10 + j] = lu[j];
            }
            c->f[9] = 1.2f; c->i[0] = 1; c->i[1] = 0;
        }
        c = add(2, TOC_OP_CDL);
        {
            float sl[3] = {1.1f, 0.9f, 0.8f}, of[3] = {0.01f, -0.02f, 0.03f};
            float pw[3] = {0.9f, 1.0f, 1.2f}, lu[3] = {0, 0, 0};
            for (int j = 0; j < 3; j++) {
                c->f[j] = sl[j]; c->f[3 + j] = of[j]; c->f[6 + j] = pw[j]; c->f[10 + j] = lu[j];
            }
            c->f[9] = 0.8f; c->i[0] = 1; c->i[1] = 1;
        }
        c = add(2, TOC_OP_LUT1D);
        {
            float d[2 + 9] = {0.25f, 1.5f, 0, 0, 0, 0.2f, 0.3f, 0.4f, 0.5f, 0.6f, 0.7f};
            setf(c->f, 11, d);
            c->i[0] = 3; c->i[1] = 3;
        }
        c = add(2, TOC_OP_LUT3D);
        {
            float d[6 + 24];
            for (int i = 0; i < 24; i++) d[6 + i] = (float)i / 24.0f;
            d[0] = -0.5f; d[1] = 0; d[2] = 0.5f;
            d[3] = 1.5f; d[4] = 1.0f; d[5] = 2.0f;
            setf(c->f, 6 + 24, d);
            c->i[0] = 2; c->i[1] = 1;
        }
        doc_target[2] = "es30";
    }
    /* 3: glow forward/inverse + dark-to-dim, GLSL 330 */
    {
        cop *c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.05f; c->f[1] = 0.08f; c->i[0] = 0; c->i[1] = 2;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.075f; c->f[1] = 0.1f; c->i[0] = 9; c->i[1] = 2;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.9811f; c->i[0] = 2; c->i[1] = 1;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 1.0192640913260627f; c->i[0] = 3; c->i[1] = 1;
        doc_target[3] = "330";
    }
    /* 4: redmod + gamutcomp13, Vulkan (ACES GLSL helpers) */
    {
        cop *c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 10; c->i[1] = 0;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 13; c->i[1] = 0;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->f[0] = 1.05f; c->f[1] = 1.1f; c->f[2] = 1.2f;
        c->f[3] = 0.8f; c->f[4] = 0.7f; c->f[5] = 0.9f;
        c->f[6] = 1.2f; c->i[0] = 4; c->i[1] = 7;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 5; c->i[1] = 7;
        c->f[0] = 1.05f; c->f[1] = 1.1f; c->f[2] = 1.2f;
        c->f[3] = 0.8f; c->f[4] = 0.7f; c->f[5] = 0.9f;
        c->f[6] = 1.2f;
        doc_target[4] = "vulkan";
    }
    /* 5: HSV/XYZ/PQ/HLG + REC2100, ES3.0 */
    {
        int styles[] = {14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25};
        for (int i = 0; i < 12; i++) {
            cop *c = add(5, TOC_OP_FIXEDFUNC);
            c->i[0] = styles[i]; c->i[1] = 0;
        }
        cop *c = add(5, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.78f; c->i[0] = 6; c->i[1] = 1;
        c = add(5, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.78f; c->i[0] = 7; c->i[1] = 1;
        doc_target[5] = "es30";
    }
    /* 6: log-camera (no GLSL case) + empty doc */
    {
        cop *c = add(6, TOC_OP_LOG_CAMERA);
        (void)c;
        doc_target[6] = "330";
    }
    /* 7: Vulkan with two LUTs (binding indices) */
    {
        cop *c = add(7, TOC_OP_LUT1D);
        {
            float d[2 + 3] = {0.0f, 1.0f, 0.0f, 0.5f, 1.0f};
            setf(c->f, 5, d);
            c->i[0] = 3; c->i[1] = 1;
        }
        c = add(7, TOC_OP_LUT3D);
        {
            float d[6 + 24];
            for (int i = 0; i < 24; i++) d[6 + i] = (float)i / 48.0f;
            d[0] = 0; d[1] = 0; d[2] = 0; d[3] = 1; d[4] = 1; d[5] = 1;
            setf(c->f, 6 + 24, d);
            c->i[0] = 2; c->i[1] = 0;
        }
        doc_target[7] = "vulkan";
    }

    for (size_t id = 0; id < N_DOCS; id++) {
        toc_glsl_target target = !strcmp(doc_target[id], "es30") ? TOC_GLSL_ES30
                                : !strcmp(doc_target[id], "330") ? TOC_GLSL_330
                                                                : TOC_GLSL_VULKAN450;
        toc_op_list *list;
        toc_shader sh;
        toc_result rc;

        fprintf(out, "ggtarget %zu %s\n", id, doc_target[id]);
        for (int k = 0; k < doc_n[id]; k++) emit_recipe(out, id, &docs[id][k]);

        list = build_list(docs[id], (size_t)doc_n[id]);
        memset(&sh, 0, sizeof(sh));
        rc = toc_emit_glsl(list, target, NULL, &sh);
        fprintf(out, "ggdoc %zu | ", id);
        if (TOC_OK(rc) && sh.source) print_hex(out, sh.source, strlen(sh.source));
        else fprintf(out, "ERR");
        fprintf(out, "\n");
        for (size_t t = 0; t < sh.num_textures; t++) {
            const toc_texture_desc *d = &sh.textures[t];
            fprintf(out, "ggtex %zu %s %s %d %d %d %d %d\n", id,
                    d->sampler_name, d->dim == TOC_TEX_3D ? "3D" : "2D",
                    d->width, d->height, d->depth, d->channels, d->interp_linear);
        }
        toc_shader_free(&sh);

        /* Metal (same op list, same recipes) */
        memset(&sh, 0, sizeof(sh));
        rc = toc_emit_metal(list, NULL, &sh);
        fprintf(out, "msldoc %zu | ", id);
        if (TOC_OK(rc) && sh.source) print_hex(out, sh.source, strlen(sh.source));
        else fprintf(out, "ERR");
        fprintf(out, "\n");
        for (size_t t = 0; t < sh.num_textures; t++) {
            const toc_texture_desc *d = &sh.textures[t];
            fprintf(out, "msltex %zu %s %s %d %d %d %d %d\n", id,
                    d->sampler_name, d->dim == TOC_TEX_3D ? "3D" : "2D",
                    d->width, d->height, d->depth, d->channels, d->interp_linear);
        }
        toc_shader_free(&sh);
        if (list) toc_op_list_free(list);
    }

    if (out != stdout) fclose(out);
    return 0;
}
