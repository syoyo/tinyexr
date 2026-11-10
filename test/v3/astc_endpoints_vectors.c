/* ASTC endpoint plumbing vectors: C vs Lean.
 *
 * `T <pc> <f0..> | <typecode> <valuecount>`
 * `L <vc> <bits> | <ok> <qm>`
 * `E <qm> <pc> <f0..> <lo..> <hi..> | <values>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x2545f491u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static void print_formats(FILE *out, uint32_t pc, const uint8_t f[4]) {
    for (uint32_t i = 0; i < pc; i++) fprintf(out, " %u", f[i]);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    tc_astc_encode_context ctx;
    memset(&ctx, 0, sizeof(ctx));
    tc_astc_build_color_pquant_lut(&ctx);
    for (uint32_t qm = 0; qm < 12u; qm++) {
        uint32_t maxq = tc_astc_quant_levels(qm) - 1u;
        for (uint32_t ideal = 0; ideal <= 64u; ideal++) {
            uint32_t q = (ideal * maxq + 32u) / 64u;
            (void)q;
        }
    }
    /* Type code / value count. */
    for (uint32_t pc = 1; pc <= 4; pc++) {
        uint32_t total = pc == 4 ? 4096u : (1u << (4u * pc));
        for (uint32_t v = 0; v < total; v++) {
            uint8_t f[4] = {0, 0, 0, 0};
            uint32_t t = v;
            if (pc == 4 && v >= 4096u) break;
            for (uint32_t i = 0; i < pc; i++) { f[i] = (uint8_t)(t & 15u); t >>= 4; }
            fprintf(out, "T %u", pc);
            print_formats(out, pc, f);
            fprintf(out, " | %u %u\n", tc_astc_partition_endpoint_type_code(pc, f),
                   tc_astc_partition_endpoint_value_count(pc, f));
        }
    }
    /* choose/lut colour quant. */
    for (uint32_t vc = 1; vc < 19u; vc++) {
        for (uint32_t bits = 0; bits < 112u; bits++) {
            uint32_t m = 0;
            int ok = tc_astc_choose_color_quant(vc, bits, &m);
            fprintf(out, "L %u %u | %d %u\n", vc, bits, ok, ok ? m : 0u);
        }
    }
    /* emit endpoint values. */
    static const uint32_t qms[11] = {4, 6, 8, 10, 12, 14, 16, 17, 18, 19, 20};
    static const uint8_t formpool[8] = {0, 1, 2, 6, 8, 10, 12, 14};
    for (int s = 0; s < 2400; s++) {
        uint32_t qm = qms[rnd() % 11u];
        uint32_t pc = 1u + rnd() % 4u;
        uint8_t f[4];
        uint32_t lo[4][4], hi[4][4]; uint8_t vals[64];
        uint32_t i, c, n;
        for (i = 0; i < pc; i++) f[i] = formpool[rnd() % 8u];
        /* The C writes into a caller array sized 18; only emit the format
         * combinations the encoder can actually produce (<= 18 symbols). */
        if (tc_astc_partition_endpoint_value_count(pc, f) > 18u) continue;
        for (i = 0; i < 4; i++)
            for (c = 0; c < 4; c++) { lo[i][c] = rnd() % 256u; hi[i][c] = rnd() % 256u; }
        n = tc_astc_emit_partition_endpoint_values(&ctx, qm, pc, f, lo, hi, vals);
        fprintf(out, "E %u %u", qm, pc);
        print_formats(out, pc, f);
        for (i = 0; i < 4; i++) for (c = 0; c < 4; c++) fprintf(out, " %u", lo[i][c]);
        for (i = 0; i < 4; i++) for (c = 0; c < 4; c++) fprintf(out, " %u", hi[i][c]);
        fprintf(out, " |");
        for (i = 0; i < n; i++) fprintf(out, " %u", vals[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
