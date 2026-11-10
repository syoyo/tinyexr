/* ASTC ISE encode bits vectors: C vs Lean.
 *
 * `I <ql> <vc> <bitOffset> | <values> | <16 bytes> | <finalBitOffset>`
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x9e3779b9u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static const uint8_t bits[21] = {1, 0, 2, 0, 1, 3, 1, 2, 4, 2, 3, 5, 3, 4, 6, 4, 5, 7, 5, 6, 8};
    for (int s = 0; s < 600; s++) {
        uint32_t ql = rnd() % 21u;
        uint32_t vc = 1u + rnd() % 64u;
        uint32_t nbits = bits[ql];
        uint8_t vals[64];
        for (uint32_t i = 0; i < vc; i++) vals[i] = (uint8_t)(rnd() % (nbits ? (1u << nbits) : 2u));
        uint8_t outb[16];
        memset(outb, 0, 16);
        uint32_t bitoff = rnd() % 16u;
        uint32_t finaloff = bitoff;
        tc_result r = tc_astc_ise_encode_bits(ql, vc, vals, outb, 16, bitoff);
        if (r != TC_SUCCESS) continue;
        finaloff = bitoff + tc_astc_ise_sequence_bitcount(vc, ql);
        fprintf(out, "I %u %u %u |", ql, vc, bitoff);
        for (uint32_t i = 0; i < vc; i++) fprintf(out, " %u", vals[i]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
        fprintf(out, " | %u\n", finaloff);
    }
    fclose(out);
    return 0;
}
