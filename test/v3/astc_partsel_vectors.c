/* ASTC partition-search / block-classification vectors: C vs Lean.
 *
 * AX <count> <block> | <loI4> <hiI4>
 * BM <bbits3> <seed3> <mask3> <words> | <mm>
 * PR <count> <block> | <opaque> <luminance> <rgbscale>
 * S  <bx> <by> <pc> <block> | <ret> <idx>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_astc.c"

static uint32_t rng = 0x85ebca6bu;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const uint8_t footprints[14][2] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6},
    {8, 8}, {10, 5}, {10, 6}, {10, 8}, {10, 10}, {12, 10}, {12, 12}};

/* kind 0: 2-cluster, 1: 4-cluster, 2: gradient+noise, 3: uniform, 4: translucent. */
static void mkblock(uint8_t block[144][4], uint32_t count, uint32_t kind) {
    for (uint32_t i = 0; i < count; i++) {
        uint32_t c;
        switch (kind) {
        case 0: {
            uint32_t base = (i < count / 2) ? 30u : 200u;
            for (c = 0; c < 4; c++) block[i][c] = (uint8_t)(base + rnd() % 12u);
            break;
        }
        case 1: {
            uint32_t t = i % 4u;
            for (c = 0; c < 4; c++) block[i][c] = (uint8_t)(20u + t * 60u + rnd() % 8u);
            break;
        }
        case 2:
            for (c = 0; c < 4; c++)
                block[i][c] = (uint8_t)((i * 7u + c * 40u + rnd() % 30u) & 0xffu);
            break;
        case 3:
            for (c = 0; c < 4; c++) block[i][c] = 128;
            break;
        default:
            for (c = 0; c < 4; c++) block[i][c] = (uint8_t)(rnd() & 0xffu);
            block[i][3] = (uint8_t)(rnd() & 0xffu);
            break;
        }
    }
}

static void print_block(FILE *out, const uint8_t block[144][4], uint32_t count) {
    for (uint32_t i = 0; i < count; i++)
        for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    for (int s = 0; s < 200; s++) {
        uint32_t count = 1u + rnd() % 144u;
        uint8_t block[144][4];
        uint32_t loI[5], hiI[5];
        memset(loI, 0, sizeof(loI));
        memset(hiI, 0, sizeof(hiI));
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)(rnd() & 0xffu);
        if (s % 5 == 0)
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) block[i][c] = (uint8_t)(i * 3u + c);
        tc_astc_axis_extremes_rgba(block, count, loI, hiI);
        fprintf(out, "AX %u", count);
        print_block(out, block, count);
        fprintf(out, " |");
        for (int c = 0; c < 4; c++) fprintf(out, " %u", loI[c]);
        for (int c = 0; c < 4; c++) fprintf(out, " %u", hiI[c]);
        fprintf(out, "\n");
    }

    for (int s = 0; s < 300; s++) {
        uint64_t bbits[3], seed[3], mask[3];
        uint32_t words = 1u + rnd() % 3u;
        for (uint32_t w = 0; w < 3; w++) {
            uint64_t r = ((uint64_t)rnd() << 32) | rnd();
            bbits[w] = r;
            seed[w] = ((uint64_t)rnd() << 32) | rnd();
            mask[w] = (w < words) ? ~(uint64_t)0 : 0;
        }
        {
            uint32_t mm = tc_astc_bitmap_mismatch(bbits, seed, mask, words);
            fprintf(out, "BM");
            for (uint32_t w = 0; w < 3; w++) fprintf(out, " %llu", (unsigned long long)bbits[w]);
            for (uint32_t w = 0; w < 3; w++) fprintf(out, " %llu", (unsigned long long)seed[w]);
            for (uint32_t w = 0; w < 3; w++) fprintf(out, " %llu", (unsigned long long)mask[w]);
            fprintf(out, " %u | %u\n", words, mm);
        }
    }

    for (int s = 0; s < 200; s++) {
        uint32_t count = 1u + rnd() % 144u;
        uint32_t kind = rnd() % 5u;
        uint8_t block[144][4];
        int op, lum, sc;
        mkblock(block, count, kind);
        op = tc_astc_block_is_opaque(block, count);
        lum = tc_astc_block_is_luminance(block, count);
        sc = tc_astc_block_is_rgb_scale(block, count);
        fprintf(out, "PR %u", count);
        print_block(out, block, count);
        fprintf(out, " | %d %d %d\n", op, lum, sc);
    }

    /* Partition search: all footprints for 2 partitions, small ones for 3/4. */
    for (int f = 0; f < 14; f++) {
        uint32_t bx = footprints[f][0], by = footprints[f][1], count = bx * by;
        for (int k = 0; k < 3; k++) {
            tc_astc_encode_context ctx;
            uint8_t block[144][4];
            const tc_astc_partition_info *pi = NULL;
            const tc_astc_partition_info *cache;
            uint32_t cache_count;
            int r;
            long idx;
            uint32_t pc = 2;
            mkblock(block, count, (uint32_t)k);
            tc_astc_encode_context_init(&ctx, bx, by, 2);
            cache = ctx.part2_cache;
            cache_count = ctx.part2_count;
            r = tc_astc_find_best_partition(block, cache, cache_count, pc, &ctx, &pi);
            idx = pi ? (long)(pi - cache) : -1;
            fprintf(out, "S %u %u %u", bx, by, pc);
            print_block(out, block, count);
            fprintf(out, " | %d %ld\n", r, idx);
        }
    }
    {
        static const int small[4] = {0, 2, 4, 7}; /* 4x4, 5x5, 6x6, 8x8 */
        for (int si = 0; si < 4; si++) {
            int f = small[si];
            uint32_t bx = footprints[f][0], by = footprints[f][1], count = bx * by;
            for (uint32_t pc = 3; pc <= 4; pc++) {
                for (int k = 0; k < 2; k++) {
                    tc_astc_encode_context ctx;
                    uint8_t block[144][4];
                    const tc_astc_partition_info *pi = NULL;
                    const tc_astc_partition_info *cache;
                    uint32_t cache_count;
                    int r;
                    long idx;
                    mkblock(block, count, (uint32_t)k);
                    tc_astc_encode_context_init(&ctx, bx, by, 2);
                    cache = pc == 3 ? ctx.part3_cache : ctx.part4_cache;
                    cache_count = pc == 3 ? ctx.part3_count : ctx.part4_count;
                    r = tc_astc_find_best_partition(block, cache, cache_count, pc, &ctx,
                                                    &pi);
                    idx = pi ? (long)(pi - cache) : -1;
                    fprintf(out, "S %u %u %u", bx, by, pc);
                    print_block(out, block, count);
                    fprintf(out, " | %d %ld\n", r, idx);
                }
            }
        }
    }

    fclose(out);
    return 0;
}
