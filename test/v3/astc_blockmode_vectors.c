/* ASTC encoder block-mode parse vectors: C vs Lean.
 *
 * One line per 11-bit block mode: `M <mode> | <ok> <wx> <wy> <quant> <bits> <dual>`
 */
#include <stdio.h>
#include <stdint.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (uint32_t mode = 0; mode < 2048u; mode++) {
        tc_astc_block_mode_info info;
        int ok = tc_astc_decode_block_mode_2d(mode, &info);
        fprintf(out, "M %u | %d", mode, ok);
        if (ok)
            fprintf(out, " %u %u %u %u %u", info.weight_x, info.weight_y,
                    info.quant_method, info.weight_bits, info.dual_plane);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
