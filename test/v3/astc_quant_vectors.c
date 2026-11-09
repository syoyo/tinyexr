/* ASTC colour quantizer vectors: C vs Lean.
 *
 * One line per quant method: `quant <qm> <256 values>`.
 * Uses the same entry point the ASTC HDR endpoint packers use. */
#include <stdio.h>
#include <stdint.h>
#include "texcomp.h"

/* Defined in texcomp_astc.c (no public header prototype). */
int tc_astc_hdr_color_roundtrip(uint32_t level, int value);

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (uint32_t qm = 0; qm <= 20; qm++) {
        fprintf(out, "quant %u", qm);
        for (int v = 0; v < 256; v++)
            fprintf(out, " %d", tc_astc_hdr_color_roundtrip(qm, v));
        fprintf(out, "\n");
    }
    /* Also the clamp edges the packer can pass in. */
    fprintf(out, "edges");
    for (uint32_t qm = 0; qm <= 20; qm += 4) {
        fprintf(out, " %d %d %d", tc_astc_hdr_color_roundtrip(qm, -7),
                tc_astc_hdr_color_roundtrip(qm, 255), tc_astc_hdr_color_roundtrip(qm, 4096));
    }
    fprintf(out, "\n");
    fclose(out);
    return 0;
}
