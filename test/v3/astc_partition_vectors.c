/* ASTC partition-cache vectors: C vs Lean.
 *
 * `S <bx> <by> <pc> <seed> <digest>`   per-seed map digest
 * `P <bx> <by> <pc> <n>`               cache header
 * `E <seed> <map hex> | <pc counts> | <3 bitmap lanes>`  cache entry
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
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1];
        uint32_t count = bx * by;
        int small = count < 32;
        for (uint32_t pc = 2; pc <= 4; pc++) {
            for (uint32_t seed = 0; seed < 1024; seed++) {
                uint32_t h = 2166136261u, i;
                for (i = 0; i < count; i++) {
                    uint8_t part = tc_astc_select_partition(seed, i % bx, i / bx, pc, small);
                    if (part >= pc) part = (uint8_t)(pc - 1u);
                    h = (h ^ part) * 16777619u;
                }
                fprintf(out, "S %u %u %u %u %u\n", bx, by, pc, seed, h);
            }
        }
    }
    static const uint8_t cacheprints[8][2] = {{4, 4}, {5, 4}, {5, 5}, {6, 5},
                                             {6, 6}, {8, 8}, {10, 10}, {12, 12}};
    for (int f = 0; f < 8; f++) {
        uint32_t bx = cacheprints[f][0], by = cacheprints[f][1];
        for (uint32_t pc = 2; pc <= 4; pc++) {
            tc_astc_encode_context ctx;
            tc_astc_partition_info cache[1024];
            uint32_t n = 0, k;
            memset(&ctx, 0, sizeof(ctx));
            ctx.block_x = bx;
            ctx.block_y = by;
            ctx.texel_count = bx * by;
            tc_astc_build_partition_cache(&ctx, pc, cache, &n);
            fprintf(out, "P %u %u %u %u\n", bx, by, pc, n);
            for (k = 0; k < n; k++) {
                uint32_t i;
                fprintf(out, "E %u ", (unsigned)cache[k].partition_index);
                for (i = 0; i < bx * by; i++)
                    fprintf(out, "%02x", cache[k].partition_of_texel[i]);
                fprintf(out, " |");
                /* C leaves partition_texel_count[p] unwritten for p >= pc
                 * (and never reads those), so only print the live entries. */
                for (i = 0; i < pc; i++)
                    fprintf(out, " %u", cache[k].partition_texel_count[i]);
                fprintf(out, " |");
                for (i = 0; i < 3; i++)
                    fprintf(out, " %llu", (unsigned long long)cache[k].bits[i]);
                fprintf(out, "\n");
            }
        }
    }
    fclose(out);
    return 0;
}
