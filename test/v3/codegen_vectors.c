/* AOT-C codegen differential vectors: C `toc_emit_c` vs the Lean port
 * (`Tocio/CodegenC.lean`).
 *
 * Records:
 *   cgop <id> <kind> <params...>        one per op, floats as 8-hex-digit
 *                                       IEEE-754 bit patterns
 *   cgdoc <id> | <hex of the emitted C source>
 *
 * The generator builds each op list twice: from its C recipe (fed to
 * `toc_emit_c`) and as textual recipes for the Lean checker, which
 * rebuilds the same op list and emits the source itself. Sources must
 * match byte-for-byte. The scalar path (simd = 0) is covered;
 * ACES_GAMUTCOMP13 is excluded (its codegen-time scale needs the pow
 * approximation).
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

#define N_DOCS 12

typedef struct {
    int kind;
    int nf;
    float f[64];
    int ni;
    int i[8];
} cop;

/* Optional custom function name per doc (default "tocio_apply"). */
static const char *doc_names[N_DOCS];

static void emit_bits(FILE *out, const float *f, int n) {
    for (int i = 0; i < n; i++) fprintf(out, " %08x", fbits(f[i]));
}

static void emit_recipe(FILE *out, size_t id, const cop *c) {
    switch (c->kind) {
    case TOC_OP_MATRIX:
        fprintf(out, "cgop %zu matrix", id);
        emit_bits(out, c->f, 20);
        break;
    case TOC_OP_RANGE:
        fprintf(out, "cgop %zu range", id);
        emit_bits(out, c->f, 16);
        fprintf(out, " %d %d", c->i[0], c->i[1]);
        break;
    case TOC_OP_EXPONENT:
        fprintf(out, "cgop %zu exponent", id);
        emit_bits(out, c->f, 4);
        fprintf(out, " %d", c->i[0]);
        break;
    case TOC_OP_EXP_LINEAR:
        fprintf(out, "cgop %zu explinear", id);
        emit_bits(out, c->f, 20);
        fprintf(out, " %d %d", c->i[0], c->i[1]);
        break;
    case TOC_OP_LOG:
        fprintf(out, "cgop %zu log", id);
        emit_bits(out, c->f, 13);
        fprintf(out, " %d", c->i[0]);
        break;
    case TOC_OP_LOG_CAMERA:
        fprintf(out, "cgop %zu logcam", id);
        break;
    case TOC_OP_CDL:
        fprintf(out, "cgop %zu cdl", id);
        emit_bits(out, c->f, 13);
        fprintf(out, " %d %d", c->i[0], c->i[1]);
        break;
    case TOC_OP_LUT1D: {
        int len = c->i[0], ch = c->i[1];
        int n = len * (ch == 1 ? 1 : 3);
        fprintf(out, "cgop %zu lut1d %d %d", id, len, ch);
        emit_bits(out, c->f, 2 + n);
        break;
    }
    case TOC_OP_LUT3D: {
        int size = c->i[0], tet = c->i[1];
        int n = size * size * size * 3;
        fprintf(out, "cgop %zu lut3d %d %d", id, size, tet);
        emit_bits(out, c->f, 6 + n);
        break;
    }
    case TOC_OP_FIXEDFUNC:
        fprintf(out, "cgop %zu fixed %d %d", id, c->i[0], c->i[1]);
        emit_bits(out, c->f, 8);
        break;
    default:
        break;
    }
    fputc('\n', out);
}

/* Build a toc_op_list from a recipe array. LUT data points into the
 * recipe's float array (borrowed; the list owns nothing). */
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
            /* emits nothing in AOT-C; fields left zero */
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
        default:
            break;
        }
    }
    return list;
}

/* ---- vector definitions -------------------------------------------------- */


static cop docs[N_DOCS][16];
static int doc_n[N_DOCS];

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

    /* 0: matrix, range (both clamp modes), exponent (plain + mirror),
     *    exp-linear (forward + inverse + mirror), log (forward + inverse) */
    {
        cop *c = add(0, TOC_OP_MATRIX);
        float m[16] = {1.5f, 0.25f, 0, 0, 0, 1.5f, 0, 0, 0, 0, 1.5f, 0,
                       0.1f, 0.2f, 0.3f, 1.0f};
        float off[4] = {0.5f, -0.25f, 0, 0.125f};
        setf(c->f, 16, m);

        for (int j = 0; j < 4; j++) c->f[16 + j] = off[j];

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
            float sc[4] = {1, 1, 1, 1};
            float ro[4] = {0, 0, 0, 0};
            float lo[4] = {0, 0, 0, 0};
            float hi[4] = {1, 1, 1, 1};
            setf(c->f, 4, sc); setf(c->f + 4, 4, ro);
            setf(c->f + 8, 4, lo); setf(c->f + 12, 4, hi);
            c->i[0] = 1; c->i[1] = 1;
        }
        c = add(0, TOC_OP_EXPONENT);
        {
            float e[4] = {2.2f, 0.5f, 1.0f, 1.0f};
            setf(c->f, 4, e);
            c->i[0] = 0;
        }
        c = add(0, TOC_OP_EXPONENT);
        {
            float e[4] = {2.2f, 2.2f, 2.2f, 1.0f};
            setf(c->f, 4, e);
            c->i[0] = 1;
        }
        c = add(0, TOC_OP_EXP_LINEAR);
        {
            float sc[4] = {0.9f, 0.9f, 0.9f, 1.0f};
            float of[4] = {0.0625f, 0.0625f, 0.0625f, 0};
            float ga[4] = {2.4f, 2.4f, 2.4f, 1.0f};
            float br[4] = {0.04045f, 0.04045f, 0.04045f, 0};
            float sl[4] = {0.0472f, 0.0472f, 0.0472f, 1.0f};
            setf(c->f, 4, sc); setf(c->f + 4, 4, of);
            setf(c->f + 8, 4, ga); setf(c->f + 12, 4, br);
            setf(c->f + 16, 4, sl);
            c->i[0] = 0; c->i[1] = 0;
        }
        c = add(0, TOC_OP_EXP_LINEAR);
        {
            float sc[4] = {0.9f, 0.9f, 0.9f, 1.0f};
            float of[4] = {0.0625f, 0.0625f, 0.0625f, 0};
            float ga[4] = {2.4f, 2.4f, 2.4f, 1.0f};
            float br[4] = {0.04045f, 0.04045f, 0.04045f, 0};
            float sl[4] = {0.0472f, 0.0472f, 0.0472f, 1.0f};
            setf(c->f, 4, sc); setf(c->f + 4, 4, of);
            setf(c->f + 8, 4, ga); setf(c->f + 12, 4, br);
            setf(c->f + 16, 4, sl);
            c->i[0] = 1; c->i[1] = 1;
        }
        c = add(0, TOC_OP_LOG);
        {
            float ls[3] = {1.0f, 1.0f, 1.0f};
            float lo[3] = {0, 0, 0};
            float ns[3] = {1.0f, 1.0f, 1.0f};
            float no[3] = {0, 0, 0};
            for (int j = 0; j < 3; j++) {
                c->f[j] = ls[j]; c->f[3 + j] = lo[j];
                c->f[6 + j] = ns[j]; c->f[9 + j] = no[j];
            }
            c->f[12] = 2.0f;
            c->i[0] = 0;
        }
        c = add(0, TOC_OP_LOG);
        {
            float ls[3] = {0.5f, 0.5f, 0.5f};
            float lo[3] = {0.1f, 0.1f, 0.1f};
            float ns[3] = {2.0f, 2.0f, 2.0f};
            float no[3] = {-0.5f, -0.5f, -0.5f};
            for (int j = 0; j < 3; j++) {
                c->f[j] = ls[j]; c->f[3 + j] = lo[j];
                c->f[6 + j] = ns[j]; c->f[9 + j] = no[j];
            }
            c->f[12] = 10.0f;
            c->i[0] = 1;
        }
    }
    /* 1: CDL forward/inverse with clamp variants and explicit luma */
    {
        cop *c = add(1, TOC_OP_CDL);
        {
            float sl[3] = {1.1f, 0.9f, 0.8f};
            float of[3] = {0.01f, -0.02f, 0.03f};
            float pw[3] = {0.9f, 1.0f, 1.2f};
            float lu[3] = {0.2126f, 0.7152f, 0.0722f};
            for (int j = 0; j < 3; j++) {
                c->f[j] = sl[j]; c->f[3 + j] = of[j]; c->f[6 + j] = pw[j];
                c->f[10 + j] = lu[j];
            }
            c->f[9] = 1.2f;
            c->i[0] = 1; c->i[1] = 0;
        }
        c = add(1, TOC_OP_CDL);
        {
            float sl[3] = {1.1f, 0.9f, 0.8f};
            float of[3] = {0.01f, -0.02f, 0.03f};
            float pw[3] = {0.9f, 1.0f, 1.2f};
            float lu[3] = {0, 0, 0}; /* default luma path */
            for (int j = 0; j < 3; j++) {
                c->f[j] = sl[j]; c->f[3 + j] = of[j]; c->f[6 + j] = pw[j];
                c->f[10 + j] = lu[j];
            }
            c->f[9] = 0.8f;
            c->i[0] = 0; c->i[1] = 1;
        }
        c = add(1, TOC_OP_CDL);
        {
            float sl[3] = {1, 1, 1};
            float of[3] = {0, 0, 0};
            float pw[3] = {1, 1, 1};
            float lu[3] = {0, 0, 0};
            for (int j = 0; j < 3; j++) {
                c->f[j] = sl[j]; c->f[3 + j] = of[j]; c->f[6 + j] = pw[j];
                c->f[10 + j] = lu[j];
            }
            c->f[9] = 0.0f; /* sat 0 exercises the skip */
            c->i[0] = 1; c->i[1] = 1;
        }
    }
    /* 2: LUT ops (1D mono, 1D RGB, 3D trilinear + tetrahedral) */
    {
        cop *c = add(2, TOC_OP_LUT1D);
        {
            float d[6] = {0.0f, 1.0f, 0.0f, 0.25f, 0.5f, 1.0f};
            setf(c->f, 6, d);
            c->i[0] = 4; c->i[1] = 1;
        }
        c = add(2, TOC_OP_LUT1D);
        {
            float d[2 + 9] = {0.1f, 0.9f,
                              0.0f, 0.0f, 0.0f,
                              0.2f, 0.3f, 0.4f,
                              0.5f, 0.6f, 0.7f};
            setf(c->f, 11, d);
            c->i[0] = 3; c->i[1] = 3;
        }
        c = add(2, TOC_OP_LUT3D);
        {
            float d[6 + 24];
            for (int i = 0; i < 24; i++) d[6 + i] = (float)i / 24.0f;
            d[0] = 0; d[1] = 0; d[2] = 0; d[3] = 1; d[4] = 1; d[5] = 1;
            setf(c->f, 6 + 24, d);
            c->i[0] = 2; c->i[1] = 0;
        }
        c = add(2, TOC_OP_LUT3D);
        {
            float d[6 + 24];
            for (int i = 0; i < 24; i++) d[6 + i] = (float)(23 - i) / 32.0f;
            d[0] = -0.5f; d[1] = 0; d[2] = 0.5f;
            d[3] = 2; d[4] = 1.5f; d[5] = 2.5f;
            setf(c->f, 6 + 24, d);
            c->i[0] = 2; c->i[1] = 1;
        }
    }
    /* 3: fixed-function styles: glow10, darktodim, redmod03, hsv, xyz, luv, hlg */
    {
        cop *c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.05f; c->f[1] = 0.08f; c->i[0] = 0; c->i[1] = 2;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.9811f; c->i[0] = 2; c->i[1] = 1;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->i[0] = 10; c->i[1] = 0;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->i[0] = 15; c->i[1] = 0;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->i[0] = 16; c->i[1] = 0;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->i[0] = 20; c->i[1] = 0;
        c = add(3, TOC_OP_FIXEDFUNC);
        c->i[0] = 24; c->i[1] = 0;
    }
    /* 4: more fixed styles: rec2100 fwd/inv, glow03, redmod10 inv, uvY inv, pq */
    {
        cop *c = add(4, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.78f; c->i[0] = 6; c->i[1] = 1;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.78f; c->i[0] = 7; c->i[1] = 1;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->f[0] = 0.075f; c->f[1] = 0.1f; c->i[0] = 8; c->i[1] = 2;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 13; c->i[1] = 0;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 19; c->i[1] = 0;
        c = add(4, TOC_OP_FIXEDFUNC);
        c->i[0] = 22; c->i[1] = 0;
    }
    /* 5: empty op list */
    /* 6: log-camera (emits nothing) + matrix + exponent */
    {
        cop *c = add(6, TOC_OP_LOG_CAMERA);
        (void)c;
        c = add(6, TOC_OP_MATRIX);
        {
            float m[16] = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1};
            setf(c->f, 16, m);
            c->f[19] = 0.0f;
        }
        c = add(6, TOC_OP_EXPONENT);
        {
            float e[4] = {2.0f, 2.0f, 2.0f, 1.0f};
            setf(c->f, 4, e);
            c->i[0] = 0;
        }
    }
    /* 7: LUT index placement: exponent, lut1d, range, lut3d */
    {
        cop *c = add(7, TOC_OP_EXPONENT);
        {
            float e[4] = {2.2f, 2.2f, 2.2f, 1.0f};
            setf(c->f, 4, e);
        }
        c = add(7, TOC_OP_LUT1D);
        {
            float d[2 + 3] = {0.0f, 1.0f, 0.0f, 0.5f, 1.0f};
            setf(c->f, 5, d);
            c->i[0] = 3; c->i[1] = 1;
        }
        c = add(7, TOC_OP_RANGE);
        {
            float v[4] = {1, 1, 1, 1};
            setf(c->f, 4, v); setf(c->f + 4, 4, v);
            setf(c->f + 8, 4, v); setf(c->f + 12, 4, v);
            c->i[0] = 1; c->i[1] = 1;
        }
        c = add(7, TOC_OP_LUT3D);
        {
            float d[6 + 24];
            for (int i = 0; i < 24; i++) d[6 + i] = (float)i / 48.0f;
            d[0] = 0; d[1] = 0; d[2] = 0; d[3] = 1; d[4] = 1; d[5] = 1;
            setf(c->f, 6 + 24, d);
            c->i[0] = 2; c->i[1] = 1;
        }
    }
    /* 8: hex-float edges: -0.0, subnormal, inf/nan placeholders */
    {
        cop *c = add(8, TOC_OP_MATRIX);
        {
            float m[16] = {-0.0f, 1.0e-40f, 0.0f, 0.0f,
                           0.0f, -1.0f, 0.0f, 0.0f,
                           0.0f, 0.0f, 1.0e38f, 0.0f,
                           0.0f, 0.0f, 0.0f, 1.0f};
            float off[4] = {0.0f, -0.0f, 0.0f, 0.0f};
            setf(c->f, 16, m);
            for (int j = 0; j < 4; j++) c->f[16 + j] = off[j];
        }
        c = add(8, TOC_OP_EXPONENT);
        {
            /* inf and nan bit patterns exercise the placeholder paths */
            uint32_t ub[4] = {0x7f800000u, 0xff800000u, 0x7fc00000u, 0x3f800000u};
            for (int j = 0; j < 4; j++) memcpy(&c->f[j], &ub[j], 4);
            c->i[0] = 1;
        }
    }
    /* 9: custom function name */
    {
        cop *c = add(9, TOC_OP_EXPONENT);
        {
            float e[4] = {2.2f, 2.2f, 2.2f, 1.0f};
            setf(c->f, 4, e);
        }
        doc_names[9] = "my_apply";
    }
    /* 11: GamutComp13 forward/inverse (codegen-time pow scale) */
    {
        cop *c = add(11, TOC_OP_FIXEDFUNC);
        c->f[0] = 1.05f; c->f[1] = 1.05f; c->f[2] = 1.05f;
        c->f[3] = 0.8f; c->f[4] = 0.8f; c->f[5] = 0.8f;
        c->f[6] = 1.2f;
        c->i[0] = 4; c->i[1] = 7;
        c = add(11, TOC_OP_FIXEDFUNC);
        c->f[0] = 1.2f; c->f[1] = 1.1f; c->f[2] = 1.3f;
        c->f[3] = 0.9f; c->f[4] = 0.7f; c->f[5] = 0.85f;
        c->f[6] = 0.8f;
        c->i[0] = 5; c->i[1] = 7;
    }
    /* 10: invalid function name (not a C identifier) -> error */
    {
        cop *c = add(10, TOC_OP_EXPONENT);
        {
            float e[4] = {2.2f, 2.2f, 2.2f, 1.0f};
            setf(c->f, 4, e);
        }
        doc_names[10] = "1bad";
    }

    for (size_t id = 0; id < N_DOCS; id++) {
        for (int k = 0; k < doc_n[id]; k++) emit_recipe(out, id, &docs[id][k]);

        toc_op_list *list = build_list(docs[id], (size_t)doc_n[id]);
        char *src = NULL;
        size_t len = 0;
        toc_codegen_c_opts opts;
        toc_result rc;
        memset(&opts, 0, sizeof(opts));
        opts.func_name = doc_names[id];
        if (opts.func_name) fprintf(out, "cgname %zu %s\n", id, opts.func_name);
        rc = toc_emit_c(list, &opts, NULL, &src, &len);
        fprintf(out, "cgdoc %zu | ", id);
        if (TOC_OK(rc) && src) {
            print_hex(out, src, len);
            toc_free(toc_default_allocator(), src);
        } else {
            fprintf(out, "ERR");
        }
        fprintf(out, "\n");
        if (list) toc_op_list_free(list);
    }

    if (out != stdout) fclose(out);
    return 0;
}
