/* ASTC weight-quant LUT + infill vectors: C vs Lean.
 *
 * `W <qm> | <65 q> | <65 wt> | <65 err>`
 * `G <bx> <by> <wx> <wy> | <64 grid> | <count wt>`      (grid infill)
 * `Q <bx> <by> <wx> <wy> <qm> | <k weights> | <count wt>` (quantised infill)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static const uint8_t footprints[14][2] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6},
    {8, 8}, {10, 5}, {10, 6}, {10, 8}, {10, 10}, {12, 10}, {12, 12}};

static uint32_t rng = 0x9e3779b9u;
static uint32_t rnd(void) {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
}

/* weight_x/weight_y choices per footprint; the last is the `direct` pair. */
static int grid_choices(uint32_t bx, uint32_t by, uint32_t pairs[6][2]) {
    static const uint32_t base[5][2] = {{2, 2}, {2, 12}, {12, 2}, {5, 5}, {6, 10}};
    int i;
    for (i = 0; i < 5; i++) { pairs[i][0] = base[i][0]; pairs[i][1] = base[i][1]; }
    pairs[5][0] = bx;
    pairs[5][1] = by;
    return 6;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    tc_astc_encode_context ctx;
    memset(&ctx, 0, sizeof(ctx));
    tc_astc_build_color_pquant_lut(&ctx);
    {
        uint32_t vc, bits, qm, ideal;
        for (vc = 1; vc < 19u; ++vc)
            for (bits = 0; bits < 112u; ++bits) {
                uint32_t m;
                if (!tc_astc_choose_color_quant(vc, bits, &m)) m = 0xffu;
                ctx.color_quant_lut[vc][bits] = (uint8_t)m;
            }
        for (qm = 0; qm < 12u; ++qm) {
            uint32_t maxq = tc_astc_quant_levels(qm) - 1u;
            for (ideal = 0; ideal <= 64u; ++ideal) {
                uint32_t q = (ideal * maxq + 32u) / 64u;
                if (q > maxq) q = maxq;
                ctx.wq_q[qm][ideal] = (uint8_t)q;
                ctx.wq_wt[qm][ideal] = (uint8_t)tc_astc_weight_unquant(q, qm);
                {
                    int32_t d = (int32_t)ctx.wq_wt[qm][ideal] - (int32_t)ideal;
                    ctx.wq_err[qm][ideal] = (uint16_t)(d * d);
                }
            }
        }
    }
    for (uint32_t qm = 0; qm < 12u; qm++) {
        fprintf(out, "W %u |", qm);
        for (uint32_t ideal = 0; ideal <= 64u; ideal++) fprintf(out, " %u", ctx.wq_q[qm][ideal]);
        fprintf(out, " |");
        for (uint32_t ideal = 0; ideal <= 64u; ideal++) fprintf(out, " %u", ctx.wq_wt[qm][ideal]);
        fprintf(out, " |");
        for (uint32_t ideal = 0; ideal <= 64u; ideal++) fprintf(out, " %u", ctx.wq_err[qm][ideal]);
        fprintf(out, "\n");
    }
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1];
        uint32_t pairs[6][2];
        int np = grid_choices(bx, by, pairs);
        for (int pi = 0; pi < np; pi++) {
            uint32_t wx = pairs[pi][0], wy = pairs[pi][1];
            tc_astc_encode_context c2;
            const tc_astc_decim_cache_entry *e;
            uint8_t grid[144], wt[144];
            uint32_t count = bx * by, n = wx * wy;
            memset(&c2, 0, sizeof(c2));
            c2.block_x = bx;
            c2.block_y = by;
            c2.texel_count = count;
            e = tc_astc_get_decim_cache(&c2, wx, wy);
            if (!e) continue;
            for (uint32_t i = 0; i < n; i++) grid[i] = (uint8_t)(rnd() & 63u);
            tc_astc_infill_weights_grid(grid, e, count, wt);
            fprintf(out, "G %u %u %u %u |", bx, by, wx, wy);
            for (uint32_t i = 0; i < n; i++) fprintf(out, " %u", grid[i]);
            fprintf(out, " |");
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
            fprintf(out, "\n");
            for (uint32_t qm = 0; qm < 12u; qm++) {
                uint32_t maxq = tc_astc_quant_levels(qm) - 1u;
                uint8_t weights[144];
                for (uint32_t i = 0; i < n; i++)
                    weights[i] = (uint8_t)(maxq ? rnd() % maxq : 0u);
                tc_astc_infill_weights(weights, e, count, qm, wt);
                fprintf(out, "Q %u %u %u %u %u |", bx, by, wx, wy, qm);
                for (uint32_t i = 0; i < n; i++) fprintf(out, " %u", weights[i]);
                fprintf(out, " |");
                for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
                fprintf(out, "\n");
            }
        }
    }
    fclose(out);
    return 0;
}
