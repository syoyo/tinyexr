/* ASTC block-mode candidate list vectors: C vs Lean.
 *
 * `C <bx> <by> <quality> <endbit> <dual> <count>`
 * `K <idx> <wx> <wy> <quant> <bits> <rank>`
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

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    static tc_astc_block_mode_info cand[2048];
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1];
        int fp = tc_astc_footprint_index(bx, by);
        for (int quality = 0; quality <= 2; quality++) {
            static const uint32_t ebs[3] = {0u, 16u, 40u};
            for (int e = 0; e < 3; e++) {
                for (int dual = 0; dual < 2; dual++) {
                    uint32_t n, i;
                    n = dual ? tc_astc_build_dual_block_mode_candidates(bx, by, ebs[e],
                                                                        quality, cand)
                             : tc_astc_build_block_mode_candidates(bx, by, ebs[e],
                                                                   quality, cand);
                    fprintf(out, "C %u %u %d %u %d %u\n", bx, by, quality, ebs[e], dual, n);
                    for (i = 0; i < n; i++) {
                        uint64_t rank = tc_astc_candidate_rank(&cand[i], fp, (uint32_t)dual);
                        fprintf(out, "K %u %u %u %u %u %llu\n", i, cand[i].weight_x,
                                cand[i].weight_y, cand[i].quant_method,
                                cand[i].weight_bits, (unsigned long long)rank);
                    }
                }
            }
        }
    }
    fclose(out);
    return 0;
}
