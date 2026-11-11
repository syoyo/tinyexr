#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"

static uint32_t rng = 0x31415926u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const uint8_t footprints[8][2] = {
    {4, 4}, {5, 5}, {6, 6}, {8, 8}, {10, 5}, {10, 10}, {12, 10}, {12, 12}};

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 40; s++) {
        int f = rnd() % 8;
        uint32_t bx = footprints[f][0], by = footprints[f][1], count = bx * by;
        /* Cover every tier: the quality<=1 scoring paths (batched
         * score-from-ideal with positional indexing, and the active-mask
         * per-candidate scan) previously went unverified. */
        int quality = s % 3;
        /* Every 3rd case keeps random alpha (non-opaque): the C re-classifies
         * the scan-time endpoint-value count to CEM 10/12 before the candidate
         * loop, a path the all-opaque vectors never reached. Non-opaque blocks
         * can only encode with 2 partitions and need >= 25 texels. */
        int nonopaque = (s % 3 == 2);
        uint32_t pcr = rnd() % 3;
        uint32_t pc = nonopaque ? 2u : 2u + pcr;
        if (pc == 4 && !(bx == 4 || bx == 5 || bx == 6 || bx == 8)) pc = 2;
        if (nonopaque && count < 25u) { bx = footprints[3][0]; by = footprints[3][1]; count = bx * by; }
        uint8_t block[144][4];
        if (nonopaque) {
            /* Two RGB clusters with mixed alpha (200/255): partitions can
             * actually win on clustered content; pure noise always fails the
             * err*4 < base_err*3 acceptance test. */
            uint8_t p0[4], p1[4];
            for (int c = 0; c < 4; c++) p0[c] = (uint8_t)(rnd() % 256);
            for (int c = 0; c < 4; c++) p1[c] = (uint8_t)(rnd() % 256);
            for (uint32_t i = 0; i < count; i++) {
                uint8_t *t = block[i];
                if ((i % bx) * 2u < bx) {
                    t[0] = (uint8_t)(p0[0] + (rnd() % 32) - 16);
                    t[1] = (uint8_t)(p0[1] + (rnd() % 32) - 16);
                    t[2] = (uint8_t)(p0[2] + (rnd() % 32) - 16);
                    t[3] = 200;
                } else {
                    t[0] = (uint8_t)(p1[0] + (rnd() % 32) - 16);
                    t[1] = (uint8_t)(p1[1] + (rnd() % 32) - 16);
                    t[2] = (uint8_t)(p1[2] + (rnd() % 32) - 16);
                    t[3] = 255;
                }
            }
        } else if (s % 3 == 1) {
            /* Two opaque RGB clusters: partitions can win on clustered
             * content; pure noise usually fails the err*4 < base_err*3
             * acceptance test. */
            uint8_t p0[3], p1[3];
            for (int c = 0; c < 3; c++) p0[c] = (uint8_t)(rnd() % 256);
            for (int c = 0; c < 3; c++) p1[c] = (uint8_t)(rnd() % 256);
            for (uint32_t i = 0; i < count; i++) {
                uint8_t *t = block[i];
                if ((i % bx) * 2u < bx) {
                    t[0] = (uint8_t)(p0[0] + (rnd() % 32) - 16);
                    t[1] = (uint8_t)(p0[1] + (rnd() % 32) - 16);
                    t[2] = (uint8_t)(p0[2] + (rnd() % 32) - 16);
                } else {
                    t[0] = (uint8_t)(p1[0] + (rnd() % 32) - 16);
                    t[1] = (uint8_t)(p1[1] + (rnd() % 32) - 16);
                    t[2] = (uint8_t)(p1[2] + (rnd() % 32) - 16);
                }
                t[3] = 255;
            }
        } else {
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)rnd();
            for (uint32_t i = 0; i < count; i++) for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)rnd();
            for (uint32_t i = 0; i < count; i++) block[i][3] = 255;
        }
        tc_astc_encode_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        tc_astc_encode_context_init(&ctx, bx, by, quality);
        uint8_t outb[16];
        uint64_t err = 0;
        int ok = tc_encode_astc_partition_rgb_block(block, count, pc, &ctx, outb, &err);
        fprintf(out, "R %u %u %u %d", pc, bx, by, quality);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " | %d", ok);
        if (ok) {
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
            fprintf(out, " %llu", (unsigned long long)err);
        }
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
