/* ASTC weight-decimation vectors: C vs Lean.
 *
 * Per tap line: `T <bx> <by> <wx> <wy> <x> <y> | <n> <q> <w> ...`
 * Per entry line: `D <bx> <by> <wx> <wy> <direct> <count>
 *                   | <4 x (q,w) per texel> | <64 weight_contrib>`
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
    if (argc > 2) {
        /* Print only the tap lines (fast path for inspection). */
    }
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1];
        for (uint32_t wx = 2; wx <= 12; wx++) {
            for (uint32_t wy = 2; wy <= 12; wy++) {
                uint32_t xs[6], ys[6];
                xs[0] = 0; ys[0] = 0;
                xs[1] = bx - 1; ys[1] = 0;
                xs[2] = 0; ys[2] = by - 1;
                xs[3] = bx - 1; ys[3] = by - 1;
                xs[4] = bx / 2; ys[4] = by / 2;
                xs[5] = (bx * 7) / 13; ys[5] = (by * 11) / 17;
                for (int t = 0; t < 6; t++) {
                    uint8_t idx[4] = {0, 0, 0, 0}, contrib[4] = {0, 0, 0, 0};
                    uint32_t n = tc_astc_texel_weights_2d(bx, by, wx, wy, xs[t], ys[t],
                                                          idx, contrib);
                    fprintf(out, "T %u %u %u %u %u %u | %u", bx, by, wx, wy, xs[t], ys[t], n);
                    for (uint32_t k = 0; k < n; k++)
                        fprintf(out, " %u %u", idx[k], contrib[k]);
                    fprintf(out, "\n");
                }
            }
        }
    }
    static const uint32_t grids[8] = {2, 3, 4, 5, 6, 8, 10, 12};
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1];
        for (int g = 0; g < 8; g++) {
            uint32_t wx = grids[g], wy = grids[(g + 3) % 8];
            tc_astc_encode_context ctx;
            const tc_astc_decim_cache_entry *e;
            memset(&ctx, 0, sizeof(ctx));
            ctx.block_x = bx;
            ctx.block_y = by;
            ctx.texel_count = bx * by;
            e = tc_astc_get_decim_cache(&ctx, wx, wy);
            if (!e) { fprintf(out, "D %u %u %u %u | missing\n", bx, by, wx, wy); continue; }
            fprintf(out, "D %u %u %u %u %u %u |", bx, by, wx, wy, (unsigned)e->direct,
                    bx * by);
            for (uint32_t i = 0; i < bx * by; i++)
                for (int k = 0; k < 4; k++)
                    fprintf(out, " %u %u", e->tw_idx[i][k], e->tw_contrib[i][k]);
            fprintf(out, " |");
            for (int k = 0; k < 64; k++) fprintf(out, " %u", e->weight_contrib[k]);
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
