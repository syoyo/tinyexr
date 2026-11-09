/* BC6H encoder kernel vectors: C vs Lean.
 *
 * Exercises the deterministic primitives every BC6H mode packer uses.
 * One token kind per line:
 *   half  <32-bit float bits> | <half bits>
 *   qu    <float bits> | <quant_uf16>
 *   qs    <float bits> | <quant_sf16>
 *   uq    <q 0..1023> | <unquant mag>
 *   usq   <q -511..511> | <smag>
 *   e3    <a0 a1 a2> <r g b> | <err3_mag>
 *   e3s   <a0 a1 a2> <r g b> | <err3_smag>
 *   psn   <v> <bits> | <packed>
 *   ps10  <v> | <packed>
 *   pal   <lo0 lo1 lo2> <hi0 hi1 hi2> | <16 x 3 magnitudes>
 *   sel   <16x3 target> <lo0..2> <hi0..2> | <16 selectors> <err>
 *   qn    <float bits> <bits> | <quant>
 *   un    <q> <bits> | <mag>
 *   qsn   <float bits> <bits> | <quant>
 *   uns   <q> <bits> | <smag>
 *   rdiv  <num> <den> | <result>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0xabcdef0123456789ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float bits_to_f(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    /* half conversion over random patterns plus the special ranges. */
    for (int i = 0; i < 500; i++) {
        uint32_t u = (uint32_t)(rnd() >> 32);
        fprintf(out, "half %08x | %04x\n", u, tc_float_to_half_bits(bits_to_f(u)));
    }
    {
        static const uint32_t sp[] = {0x00000000u, 0x80000000u, 0x7f800000u,
                                      0xff800000u, 0x7fc00000u, 0x00000001u,
                                      0x00800000u, 0x3f800000u, 0xbf800000u,
                                      0x477fe000u, 0x477fffffu, 0x47800000u,
                                      0xc77fe000u, 0x33800000u, 0x33000000u};
        for (unsigned i = 0; i < sizeof(sp) / sizeof(sp[0]); i++)
            fprintf(out, "half %08x | %04x\n", sp[i],
                    tc_float_to_half_bits(bits_to_f(sp[i])));
    }
    for (int i = 0; i < 400; i++) {
        uint32_t u = (uint32_t)(rnd() >> 32);
        float f = bits_to_f(u);
        fprintf(out, "qu %08x | %u\n", u, tc_bc6h_quant_uf16(f));
        fprintf(out, "qs %08x | %d\n", u, tc_bc6h_quant_sf16(f));
    }
    for (int i = 0; i < 300; i++) {
        uint32_t q = (uint32_t)(rnd() % 1024u);
        int32_t sq = (int32_t)(rnd() % 1023u) - 511;
        fprintf(out, "uq %u | %u\n", q, tc_bc6h_unquant_uf16_to_mag(q));
        fprintf(out, "usq %d | %d\n", sq, tc_bc6h_unquant_sf16_to_smag(sq));
    }
    for (int i = 0; i < 300; i++) {
        uint32_t a[3], r = (uint32_t)(rnd() % 32768u), g = (uint32_t)(rnd() % 32768u),
                    b = (uint32_t)(rnd() % 32768u);
        int32_t as[3], rs, gs, bs;
        for (int c = 0; c < 3; c++) {
            a[c] = (uint32_t)(rnd() % 32768u);
            as[c] = (int32_t)(rnd() % 65535u) - 32767;
        }
        rs = (int32_t)(rnd() % 65535u) - 32767;
        gs = (int32_t)(rnd() % 65535u) - 32767;
        bs = (int32_t)(rnd() % 65535u) - 32767;
        fprintf(out, "e3 %u %u %u %u %u %u | %u\n", a[0], a[1], a[2], r, g, b,
                tc_bc6h_err3_mag(a, r, g, b));
        fprintf(out, "e3s %d %d %d %d %d %d | %u\n", as[0], as[1], as[2], rs, gs, bs,
                tc_bc6h_err3_smag(as, rs, gs, bs));
    }
    for (int i = 0; i < 200; i++) {
        int32_t v = (int32_t)(rnd() % 4096u) - 2048;
        uint32_t bits = 2u + (uint32_t)(rnd() % 10u);
        fprintf(out, "psn %d %u | %u\n", v, bits, tc_bc6h_pack_signed_n(v, bits));
        fprintf(out, "ps10 %d | %u\n", v, tc_bc6h_pack_signed10(v));
    }
    /* palette + selector choice */
    for (int i = 0; i < 150; i++) {
        uint32_t lo[3], hi[3], target[16][3];
        int32_t pr[16], pg[16], pb[16];
        uint8_t sel[16];
        for (int c = 0; c < 3; c++) {
            lo[c] = (uint32_t)(rnd() % 1024u);
            hi[c] = (uint32_t)(rnd() % 1024u);
        }
        for (int t = 0; t < 16; t++)
            for (int c = 0; c < 3; c++)
                target[t][c] = (uint32_t)(rnd() % 32768u);
        fprintf(out, "pal %u %u %u %u %u %u |", lo[0], lo[1], lo[2], hi[0], hi[1], hi[2]);
        tc_bc6h_pal16_uf16(lo, hi, pr, pg, pb);
        for (int s = 0; s < 16; s++)
            fprintf(out, " %d %d %d", pr[s], pg[s], pb[s]);
        fprintf(out, "\n");
        fprintf(out, "sel");
        for (int t = 0; t < 16; t++)
            fprintf(out, " %u %u %u", target[t][0], target[t][1], target[t][2]);
        fprintf(out, " %u %u %u %u %u %u |",
                lo[0], lo[1], lo[2], hi[0], hi[1], hi[2]);
        {
            uint64_t e = tc_bc6h_choose_selectors_uf16_scalar(target, lo, hi, sel);
            for (int t = 0; t < 16; t++) fprintf(out, " %u", sel[t]);
            fprintf(out, " %llu\n", (unsigned long long)e);
        }
    }
    for (int i = 0; i < 200; i++) {
        uint32_t u = (uint32_t)(rnd() >> 32);
        uint32_t bits = 2u + (uint32_t)(rnd() % 10u);
        int32_t v = (int32_t)(rnd() % 1023u) - 511;
        float f = bits_to_f(u);
        fprintf(out, "qn %08x %u | %u\n", u, bits, tc_bc6h_quant_uf16_n(f, bits));
        {
            uint32_t q = (uint32_t)(rnd() % (1u << bits));
            fprintf(out, "un %u %u | %u\n", q, bits, tc_bc6h_unquant_n_to_mag(q, bits));
        }
        fprintf(out, "qsn %08x %u | %d\n", u, bits, tc_bc6h_quant_sf16_n(f, bits));
        fprintf(out, "uns %d %u | %d\n", v, bits, tc_bc6h_unquant_n_to_smag(v, bits));
    }
    for (int i = 0; i < 200; i++) {
        int64_t num = (int64_t)(rnd() >> 20) - (int64_t)(rnd() >> 22);
        int64_t den = (int64_t)(rnd() % 100000u) + 1;
        fprintf(out, "rdiv %lld %lld | %lld\n", (long long)num, (long long)den,
                (long long)tc_bc6h_rdiv(num, den));
    }
    fclose(out);
    return 0;
}
