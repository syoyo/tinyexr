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

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 30; s++) {
        uint32_t bx = 4 + (rnd() % 3) * 2;
        uint32_t by = 4 + (rnd() % 3) * 2;
        if (bx > 10) bx = 8;
        if (by > 10) by = 8;
        uint32_t count = bx * by;
        if (count > 144) { bx = 4; by = 4; count = 16; }
        int quality = 1 + (s % 2);
        uint8_t block[144][4];
        for (uint32_t i = 0; i < count; i++) {
            for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)rnd();
            block[i][3] = (uint8_t)(50 + rnd() % 200);
        }
        if (s % 3 == 0) for (uint32_t i = 0; i < count; i++) block[i][1] = (uint8_t)(block[i][0] + 10);
        tc_astc_encode_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        tc_astc_encode_context_init(&ctx, bx, by, quality);
        uint8_t outb[16];
        uint64_t err = 0;
        int ok = tc_encode_astc_dual_rgba_block(block, count, quality, &ctx, outb, &err);
        fprintf(out, "D %u %u %d", bx, by, quality);
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
