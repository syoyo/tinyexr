/* ASTC fit-path vectors (projection / weights / fit / misc): C vs Lean.
 *
 * A  <count> <axis> <block 4*count> | <lo_i> <hi_i>
 * PW <dot64> <recip> | <w>
 * P  <count> <pc> <partOf count> <lo 16> <hi 16> <block 4*count> <wantEndpoints>
 *    | <allActive> | <ideal count> | <active count> | <e0t 4*count> | <e1t 4*count>
 * W  <bx> <by> <wx> <wy> <qm> <count> <ideal count> | <out wx*wy> | <wt count>
 * WP <bx> <by> <wx> <wy> <qm> <count> <ideal count> <active count> | <out> | <wt>
 * F  <bx> <by> <wx> <wy> <qm> <count> <ideal> | <block 4*count> | <lo 4> <hi 4> | <sse>
 * FP <bx> <by> <wx> <wy> <qm> <count> <ideal> | <active> | <block> | <e0t> | <e1t> | <sse>
 * S  <count> <sum 3> | <sumsq 3> | <err|-1>
 * X  <qm> <64 weights> | <scramble 64> | <invert 64>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x6d2b79f5u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const uint8_t footprints[14][2] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6},
    {8, 8}, {10, 5}, {10, 6}, {10, 8}, {10, 10}, {12, 10}, {12, 12}};

static void init_ctx(tc_astc_encode_context *ctx, uint32_t bx, uint32_t by) {
    uint32_t qm, ideal;
    memset(ctx, 0, sizeof(*ctx));
    ctx->block_x = bx;
    ctx->block_y = by;
    ctx->texel_count = bx * by;
    for (qm = 0; qm < 12u; ++qm) {
        uint32_t maxq = tc_astc_quant_levels(qm) - 1u;
        for (ideal = 0; ideal <= 64u; ++ideal) {
            uint32_t q = (ideal * maxq + 32u) / 64u;
            if (q > maxq) q = maxq;
            ctx->wq_q[qm][ideal] = (uint8_t)q;
            ctx->wq_wt[qm][ideal] = (uint8_t)tc_astc_weight_unquant(q, qm);
        }
    }
}

static void print_u32_list(FILE *out, const uint32_t *v, uint32_t n) {
    for (uint32_t i = 0; i < n; i++) fprintf(out, " %u", v[i]);
}
static void print_u8_list(FILE *out, const uint8_t *v, uint32_t n) {
    for (uint32_t i = 0; i < n; i++) fprintf(out, " %u", v[i]);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    /* Axis extremes. */
    for (int s = 0; s < 400; s++) {
        uint32_t count = 1u + rnd() % 144u;
        uint32_t axis = rnd() % 5u;
        uint8_t block[144][4];
        uint32_t loI = 0, hiI = 0;
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)rnd();
        tc_astc_axis_extremes(block, count, axis, &loI, &hiI);
        fprintf(out, "A %u %u", count, axis);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %u %u\n", loI, hiI);
    }

    /* Projection weight. */
    for (int s = 0; s < 600; s++) {
        uint32_t denom = 1u + rnd() % (4u * 255u * 255u);
        uint32_t recip = TC_ASTC_PROJ_RECIP(denom);
        uint32_t dot64 = rnd() % (64u * denom + 1u);
        uint32_t w = tc_astc_project_weight(dot64, recip);
        fprintf(out, "PW %u %u | %u\n", dot64, recip, w);
    }

    /* Partition projection. */
    for (int s = 0; s < 80; s++) {
        const uint8_t *fp = footprints[rnd() % 14u];
        uint32_t bx = fp[0], by = fp[1], count = bx * by;
        uint32_t pc = 1u + rnd() % 4u;
        uint8_t block[144][4];
        uint32_t lo[4][4], hi[4][4];
        tc_astc_partition_info pi;
        uint8_t ideal[144], active[144], e0t[144][4], e1t[144][4];
        int all;
        memset(&pi, 0, sizeof(pi));
        for (uint32_t i = 0; i < count; i++) {
            for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)rnd();
            pi.partition_of_texel[i] = (uint8_t)(rnd() % pc);
        }
        for (uint32_t p = 0; p < pc; p++)
            for (uint32_t c = 0; c < 4; c++) {
                lo[p][c] = rnd() % 256u;
                hi[p][c] = rnd() % 256u;
                /* Force a solid partition now and then. */
                if (s % 7 == 3 && p == 0) hi[p][c] = lo[p][c];
            }
        all = tc_astc_partition_project(block, count, &pi, pc, lo, hi, ideal,
                                        active, (s % 2) ? e0t : NULL,
                                        (s % 2) ? e1t : NULL);
        fprintf(out, "P %u %u", count, pc);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", pi.partition_of_texel[i]);
        for (uint32_t p = 0; p < 4; p++) for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", lo[p][c]);
        for (uint32_t p = 0; p < 4; p++) for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", hi[p][c]);
        for (uint32_t i = 0; i < count; i++) for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " %d | %d |", s % 2, all);
        print_u8_list(out, ideal, count);
        fprintf(out, " |");
        print_u8_list(out, active, count);
        fprintf(out, " |");
        if (s % 2) {
            for (uint32_t i = 0; i < count; i++) for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", e0t[i][c]);
            fprintf(out, " |");
            for (uint32_t i = 0; i < count; i++) for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", e1t[i][c]);
        }
        fprintf(out, "\n");
    }

    /* Weights-from-ideal / fits. */
    static const uint32_t qms[3] = {4, 8, 11};
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1], count = bx * by;
        uint32_t pairs[6][2] = {{2, 2}, {5, 5}, {2, 12}, {12, 2}, {6, 10},
                                {bx, by}};
        for (int pi = 0; pi < 6; pi++) {
            uint32_t wx = pairs[pi][0], wy = pairs[pi][1], wc = wx * wy;
            /* The C writes out_weights into a uint8_t[64]: only weight grids
             * the encoder can select (weight count <= 64) are valid. */
            if (wc > 64u) continue;
            tc_astc_encode_context ctx;
            const tc_astc_decim_cache_entry *decim;
            uint8_t block[144][4], ideal[144], active[144], outw[64], wt[144];
            uint32_t lo[4], hi[4];
            for (uint32_t i = 0; i < count; i++) {
                for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)rnd();
                ideal[i] = (uint8_t)(rnd() % 65u);
                active[i] = (uint8_t)(rnd() & 1u);
            }
            for (uint32_t c = 0; c < 4; c++) { lo[c] = rnd() % 256u; hi[c] = rnd() % 256u; }
            init_ctx(&ctx, bx, by);
            decim = tc_astc_get_decim_cache(&ctx, wx, wy);
            if (!decim) continue;
            for (int k = 0; k < 3; k++) {
                uint32_t qm = qms[k];
                uint64_t e;
                tc_astc_weights_from_ideal(&ctx, count, ideal, qm, decim, wc, outw, wt);
                fprintf(out, "W %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
                print_u8_list(out, ideal, count);
                fprintf(out, " |");
                print_u8_list(out, outw, wc);
                fprintf(out, " |");
                print_u8_list(out, wt, count);
                fprintf(out, "\n");
                e = tc_astc_fit_from_ideal(&ctx, block, count, ideal, lo, hi, qm,
                                           decim, wc, outw, wt);
                fprintf(out, "F %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
                print_u8_list(out, ideal, count);
                fprintf(out, " |");
                for (uint32_t i = 0; i < count; i++)
                    for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
                fprintf(out, " |");
                print_u32_list(out, lo, 4);
                print_u32_list(out, hi, 4);
                fprintf(out, " | %llu\n", (unsigned long long)e);
                tc_astc_weights_from_ideal_pt(&ctx, count, ideal, active, qm,
                                              decim, wc, outw, wt);
                fprintf(out, "WP %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
                print_u8_list(out, ideal, count);
                fprintf(out, " |");
                print_u8_list(out, active, count);
                fprintf(out, " |");
                print_u8_list(out, outw, wc);
                fprintf(out, " |");
                print_u8_list(out, wt, count);
                fprintf(out, "\n");
                {
                    uint8_t e0t[144][4], e1t[144][4];
                    for (uint32_t i = 0; i < count; i++)
                        for (uint32_t c = 0; c < 4; c++) {
                            e0t[i][c] = (uint8_t)(rnd() & 0xffu);
                            e1t[i][c] = (uint8_t)(rnd() & 0xffu);
                        }
                    e = tc_astc_fit_from_ideal_pt(&ctx, block, count, ideal, active,
                                                  e0t, e1t, qm, decim, wc, outw, wt);
                    fprintf(out, "FP %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
                    print_u8_list(out, ideal, count);
                    fprintf(out, " |");
                    print_u8_list(out, active, count);
                    fprintf(out, " |");
                    for (uint32_t i = 0; i < count; i++)
                        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
                    fprintf(out, " |");
                    for (uint32_t i = 0; i < count; i++)
                        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", e0t[i][c]);
                    fprintf(out, " |");
                    for (uint32_t i = 0; i < count; i++)
                        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", e1t[i][c]);
                    fprintf(out, " | %llu\n", (unsigned long long)e);
                }
            }
        }
    }

    /* SSE from stats. */
    for (int s = 0; s < 300; s++) {
        uint32_t count = rnd() % 145u;
        uint64_t sum[3], sumsq[3];
        uint32_t c;
        uint64_t e;
        for (c = 0; c < 3; c++) {
            uint64_t mean = count ? rnd() % 256u : 0;
            sum[c] = mean * count;
            sumsq[c] = (mean * mean + 7u) * count;
        }
        e = tc_astc_rgb_sse_from_stats(sum, sumsq, count);
        fprintf(out, "S %u", count);
        for (c = 0; c < 3; c++) fprintf(out, " %llu", (unsigned long long)sum[c]);
        fprintf(out, " |");
        for (c = 0; c < 3; c++) fprintf(out, " %llu", (unsigned long long)sumsq[c]);
        fprintf(out, " | %lld\n", (long long)e);
    }

    /* Scramble / invert. */
    for (uint32_t qm = 0; qm < 12; qm++) {
        uint8_t w[64], ws[64], wi[64];
        uint32_t levels = tc_astc_quant_levels(qm);
        for (uint32_t i = 0; i < 64; i++) w[i] = (uint8_t)(rnd() % levels);
        memcpy(ws, w, sizeof(ws));
        memcpy(wi, w, sizeof(wi));
        tc_astc_scramble_weights(ws, 64, qm);
        tc_astc_invert_weights(wi, 64, qm);
        fprintf(out, "X %u", qm);
        print_u8_list(out, w, 64);
        fprintf(out, " |");
        print_u8_list(out, ws, 64);
        fprintf(out, " |");
        print_u8_list(out, wi, 64);
        fprintf(out, "\n");
    }

    fclose(out);
    return 0;
}
