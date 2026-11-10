/* ASTC least-squares / evaluation vectors: C vs Lean.
 *
 * R  <num> <den> | <res>
 * L  <count> <wt> <block> | <ok> <lo4> <hi4>
 * LP <count> <part> <partOf> <wt> <block> | <ok> <lo4> <hi4>
 * E  <count> <fmt> <qm> <wt> <lo4> <hi4> <block> | <sse>
 * EP <count> <pc> <partOf> <formats4> <partLo16> <partHi16> <qm> <wt> <block> | <sse|-1>
 * ED <count> <fmt> <qm> <wtc> <wta> <lo4> <hi4> <block> | <sse>
 * C  <count> <wanted> <block> | <res>
 * K  <lo3> <hi3> | <res>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x1b873593u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const uint8_t footprints[14][2] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6},
    {8, 8}, {10, 5}, {10, 6}, {10, 8}, {10, 10}, {12, 10}, {12, 12}};

static void init_ctx(tc_astc_encode_context *ctx) {
    uint32_t vc, bits, q;
    memset(ctx, 0, sizeof(*ctx));
    tc_astc_build_color_pquant_lut(ctx);
    for (vc = 1; vc < 19u; ++vc)
        for (bits = 0; bits < 112u; ++bits) {
            uint32_t m;
            if (!tc_astc_choose_color_quant(vc, bits, &m)) m = 0xffu;
            ctx->color_quant_lut[vc][bits] = (uint8_t)m;
        }
    for (q = 0; q < 21u; ++q) { }
}

static void mkblock(uint8_t block[144][4], uint8_t wt[144], uint8_t wt2[144],
                    uint32_t count) {
    for (uint32_t i = 0; i < count; i++) {
        for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)rnd();
        wt[i] = (uint8_t)(rnd() % 65u);
        wt2[i] = (uint8_t)(rnd() % 65u);
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    tc_astc_encode_context ctx;
    init_ctx(&ctx);

    /* Rounded division. */
    for (int s = 0; s < 800; s++) {
        int64_t num = (int64_t)(rnd() % 2000001u) - 1000000;
        int64_t den = 1 + (int64_t)(rnd() % 1048576u);
        fprintf(out, "R %lld %lld | %lld\n", (long long)num, (long long)den,
                (long long)tc_div_round_s64(num, den));
    }

    for (int s = 0; s < 220; s++) {
        const uint8_t *fp = footprints[rnd() % 14u];
        uint32_t count = (uint32_t)fp[0] * fp[1];
        uint8_t block[144][4], wt[144], wt2[144];
        uint32_t lo[4], hi[4];
        int ok;
        mkblock(block, wt, wt2, count);
        ok = tc_astc_lsq_endpoints(block, count, wt, lo, hi);
        fprintf(out, "L %u", count);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %d", ok);
        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", lo[c]);
        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", hi[c]);
        fprintf(out, "\n");

        {
            tc_astc_partition_info pi;
            uint32_t part = rnd() % 4u;
            memset(&pi, 0, sizeof(pi));
            for (uint32_t i = 0; i < count; i++) pi.partition_of_texel[i] = (uint8_t)(rnd() % 4u);
            ok = tc_astc_lsq_endpoints_partition(block, count, &pi, part, wt, lo, hi);
            fprintf(out, "LP %u %u", count, part);
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", pi.partition_of_texel[i]);
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
            fprintf(out, " | %d", ok);
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", lo[c]);
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", hi[c]);
            fprintf(out, "\n");
        }
    }

    static const uint32_t fmts[6] = {0, 4, 6, 8, 10, 12};
    static const uint32_t qms[5] = {4, 8, 12, 16, 20};
    for (int s = 0; s < 320; s++) {
        const uint8_t *fp = footprints[rnd() % 14u];
        uint32_t count = (uint32_t)fp[0] * fp[1];
        uint8_t block[144][4], wt[144], wt2[144];
        uint32_t lo[4], hi[4];
        uint32_t fmt = fmts[rnd() % 6u], qm = qms[rnd() % 5u];
        uint64_t e;
        mkblock(block, wt, wt2, count);
        for (uint32_t c = 0; c < 4; c++) { lo[c] = rnd() % 256u; hi[c] = rnd() % 256u; }
        e = tc_astc_eval_single_sse(&ctx, block, count, wt, fmt, lo, hi, qm);
        fprintf(out, "E %u %u %u", count, fmt, qm);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", lo[c]);
        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", hi[c]);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %llu\n", (unsigned long long)e);

        /* Dual-plane evaluation. */
        {
            uint32_t dfmt = (rnd() & 1u) ? 10u : 12u;
            uint64_t ed = tc_astc_eval_dual_sse(&ctx, block, count, wt, wt2, dfmt,
                                                lo, hi, qm);
            fprintf(out, "ED %u %u %u", count, dfmt, qm);
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
            for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt2[i]);
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", lo[c]);
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", hi[c]);
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
            fprintf(out, " | %llu\n", (unsigned long long)ed);
        }
    }

    for (int s = 0; s < 220; s++) {
        const uint8_t *fp = footprints[rnd() % 14u];
        uint32_t count = (uint32_t)fp[0] * fp[1];
        uint32_t pc = 1u + rnd() % 4u;
        uint8_t block[144][4], wt[144], wt2[144];
        uint32_t partLo[4][4], partHi[4][4];
        uint8_t formats[4];
        tc_astc_partition_info pi;
        uint32_t qm = qms[rnd() % 5u];
        uint64_t e;
        memset(&pi, 0, sizeof(pi));
        mkblock(block, wt, wt2, count);
        for (uint32_t i = 0; i < count; i++) pi.partition_of_texel[i] = (uint8_t)(rnd() % pc);
        for (uint32_t p = 0; p < pc; p++) {
            formats[p] = (uint8_t)fmts[rnd() % 6u];
            for (uint32_t c = 0; c < 4; c++) {
                partLo[p][c] = rnd() % 256u;
                partHi[p][c] = rnd() % 256u;
            }
        }
        e = tc_astc_eval_partition_sse(&ctx, block, count, &pi, pc, formats,
                                       partLo, partHi, qm, wt);
        fprintf(out, "EP %u %u", count, pc);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", pi.partition_of_texel[i]);
        for (uint32_t p = 0; p < 4; p++) fprintf(out, " %u", formats[p]);
        for (uint32_t p = 0; p < 4; p++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", partLo[p][c]);
        for (uint32_t p = 0; p < 4; p++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", partHi[p][c]);
        fprintf(out, " %u", qm);
        for (uint32_t i = 0; i < count; i++) fprintf(out, " %u", wt[i]);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %lld\n", e == (uint64_t)-1 ? -1LL : (long long)e);
    }

    for (int s = 0; s < 300; s++) {
        const uint8_t *fp = footprints[rnd() % 14u];
        uint32_t count = (uint32_t)fp[0] * fp[1];
        uint32_t wanted = 1u + rnd() % 4u;
        uint8_t block[144][4], wt[144], wt2[144];
        int r;
        mkblock(block, wt, wt2, count);
        /* Bias some blocks to a small palette so clusters are found. */
        if (s & 1) {
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)((i % 3u) * 60u);
        }
        r = tc_astc_block_has_rgb_clusters(block, count, wanted);
        fprintf(out, "C %u %u", count, wanted);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %d\n", r);
    }

    for (int s = 0; s < 300; s++) {
        uint32_t lo[3], hi[3];
        int r;
        for (uint32_t c = 0; c < 3; c++) { lo[c] = rnd() % 256u; hi[c] = rnd() % 256u; }
        r = tc_astc_partition_rgb_scale_ok(lo, hi);
        fprintf(out, "K %u %u %u", lo[0], lo[1], lo[2]);
        fprintf(out, " | %u %u %u | %d\n", hi[0], hi[1], hi[2], r);
    }

    fclose(out);
    return 0;
}
