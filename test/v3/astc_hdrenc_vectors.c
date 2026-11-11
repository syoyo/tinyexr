/* ASTC HDR block encoder test-vector generator (C side).
 *
 * Emits one line per case (LNS-domain inputs, so the float boundary is
 * not exercised here):
 *   H1 <48 lns ints> | <ok> <16 hex bytes> <sse>   (cem11 single/dual)
 *   H2 <48 lns ints> | <ok> <16 hex bytes> <sse>   (cem11 2-subset)
 *   H3 <48 lns ints> | <ok> <16 hex bytes> <sse>   (cem7)
 *   H4 <64 lns ints> | <ok> <16 hex bytes> <sse>   (cem15)
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"
#include "texcomp_astc_hdr.c"

static uint32_t rng = 0xc0ffee11u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static void emit_rgb(FILE *out, char tag, const int lns[16][3]) {
    uint8_t outb[16];
    uint64_t sse = 0;
    if (tag == '1') sse = tc_encode_astc_hdr_cem11_block(lns, outb);
    else if (tag == '2') sse = tc_encode_astc_hdr_cem11_2subset_block(lns, outb);
    else sse = tc_encode_astc_hdr_cem7_block(lns, outb);
    int ok = sse != (uint64_t)-1;
    fprintf(out, "H%c", tag);
    for (int i = 0; i < 16; i++)
        for (int c = 0; c < 3; c++) fprintf(out, " %d", lns[i][c]);
    fprintf(out, " | %d", ok);
    if (ok) {
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
        fprintf(out, " %llu", (unsigned long long)sse);
    }
    fprintf(out, "\n");
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 60; s++) {
        int cls = s % 6;
        int lns[16][3], lns4[16][4];
        int base[3] = { (int)(rnd() % 40000), (int)(rnd() % 40000),
                        (int)(rnd() % 40000) };
        for (int i = 0; i < 16; i++) {
            for (int c = 0; c < 3; c++) {
                int v;
                switch (cls) {
                case 0: v = (int)(rnd() % 65536); break; /* noisy */
                case 1: v = base[c] + (int)(rnd() % 61) - 30; break; /* tight */
                case 2: v = (base[c] * (i + 3)) / 19; break; /* ramp */
                case 3: /* two regions */
                    v = (i < 8 ? base[c] : 65535 - base[c]) +
                        (int)(rnd() % 121) - 60;
                    break;
                case 4: v = (rnd() % 2) ? (int)(rnd() % 300) : 65535 - (int)(rnd() % 300); break;
                default: v = base[c]; break; /* near-constant */
                }
                if (v < 0) v = 0;
                if (v > 65535) v = 65535;
                lns[i][c] = v;
                lns4[i][c] = v;
            }
            lns4[i][3] = (int)(rnd() % 65536);
        }
        emit_rgb(out, '1', lns);
        emit_rgb(out, '2', lns);
        emit_rgb(out, '3', lns);
        /* cem15 */
        {
            uint8_t outb[16];
            uint64_t sse = tc_encode_astc_hdr_cem15_block(lns4, outb);
            int ok = sse != (uint64_t)-1;
            fprintf(out, "H4");
            for (int i = 0; i < 16; i++)
                for (int c = 0; c < 4; c++) fprintf(out, " %d", lns4[i][c]);
            fprintf(out, " | %d", ok);
            if (ok) {
                for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
                fprintf(out, " %llu", (unsigned long long)sse);
            }
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
