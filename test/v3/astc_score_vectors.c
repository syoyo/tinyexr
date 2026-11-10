/* ASTC score-from-ideal / score-batch vectors: C vs Lean.
 *
 * `SF <bx> <by> <wx> <wy> <qm> <count> | <ideal> | <err>`
 * `SFA <bx> <by> <wx> <wy> <qm> <count> | <ideal> | <active> | <err>`
 * `SB <bx> <by> <wx> <wy> <qm> <count> <n> | <ideal0> | ... | <idealn-1> | <err0> ... <errn-1>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x5a827999u;
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
            {
                int32_t d = (int32_t)ctx->wq_wt[qm][ideal] - (int32_t)ideal;
                ctx->wq_err[qm][ideal] = (uint16_t)(d * d);
            }
        }
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const uint32_t qms[4] = {0, 4, 8, 11};
    for (int s = 0; s < 200; s++) {
        uint32_t bx = footprints[rnd() % 14u][0], by = footprints[rnd() % 14u][1];
        uint32_t count = bx * by;
        uint32_t wx = 2u + rnd() % (bx - 1u);
        uint32_t wy = 2u + rnd() % (by - 1u);
        if (wx * wy > 64u) { wx = 2; wy = 2; }
        uint32_t qm = qms[rnd() % 4u];
        uint8_t ideal[144], active[144];
        tc_astc_encode_context ctx;
        const tc_astc_decim_cache_entry *decim;
        uint64_t err;
        init_ctx(&ctx, bx, by);
        for (uint32_t i = 0; i < count; i++) {
            ideal[i] = (uint8_t)(rnd() % 65u);
            active[i] = (uint8_t)(rnd() & 1u);
        }
        decim = tc_astc_get_decim_cache(&ctx, wx, wy);
        if (!decim) continue;
        err = tc_astc_score_from_ideal(&ctx, count, ideal, NULL, qm, decim, wx * wy);
        fprintf(out, "SF %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", ideal[i]);
        fprintf(out, " | %llu\n", (unsigned long long)err);
        err = tc_astc_score_from_ideal(&ctx, count, ideal, active, qm, decim, wx * wy);
        fprintf(out, "SFA %u %u %u %u %u %u", bx, by, wx, wy, qm, count);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", ideal[i]);
        fprintf(out, " |");
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", active[i]);
        fprintf(out, " | %llu\n", (unsigned long long)err);
    }
    for (int s = 0; s < 120; s++) {
        uint32_t bx = footprints[rnd() % 14u][0], by = footprints[rnd() % 14u][1];
        uint32_t count = bx * by;
        uint32_t wx = 2u + rnd() % (bx - 1u);
        uint32_t wy = 2u + rnd() % (by - 1u);
        if (wx * wy > 64u) { wx = 2; wy = 2; }
        uint32_t qm = qms[rnd() % 4u];
        uint32_t n = 1u;
        uint8_t ideal[4][144];
        uint64_t errs[4];
        tc_astc_encode_context ctx;
        const tc_astc_decim_cache_entry *decim;
        const uint8_t *ip[4];
        init_ctx(&ctx, bx, by);
        for (uint32_t bi = 0; bi < n; bi++)
            for (uint32_t i = 0; i < count; i++) ideal[bi][i] = (uint8_t)(rnd() % 65u);
        for (uint32_t bi = 0; bi < n; bi++) ip[bi] = ideal[bi];
        decim = tc_astc_get_decim_cache(&ctx, wx, wy);
        if (!decim) continue;
        tc_astc_score_batch(&ctx, count, ip, n, qm, decim, wx * wy, errs);
        fprintf(out, "SB %u %u %u %u %u %u %u", bx, by, wx, wy, qm, count, n);
        for (uint32_t bi = 0; bi < n; bi++) {
            fprintf(out, " |");
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", ideal[bi][i]);
        }
        fprintf(out, " |");
        for (uint32_t bi = 0; bi < n; bi++) fprintf(out, " %llu", (unsigned long long)errs[bi]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
