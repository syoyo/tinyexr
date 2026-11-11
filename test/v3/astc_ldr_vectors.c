/* ASTC LDR block encoder test-vector generator (C side).
 *
 * Emits one line per case:
 *   L <bx> <by> <quality> <count*4 rgba bytes> | <16 hex block bytes>
 *
 * The Lean differential checker (lean/AstcLdrCheck.lean) replays these
 * against `astcEncodeLdrBlock` and requires bit-identical output.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"

static uint32_t rng = 0x8f16c9a5u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

static const struct { uint32_t x, y; } fps[] = {
    {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6}, {8, 8},
};

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 45; s++) {
        uint32_t bx = fps[s % 8].x, by = fps[s % 8].y;
        uint32_t count = bx * by;
        if (count > 144) { bx = 4; by = 4; count = 16; }
        int quality = s % 3;
        int cls = (s / 3) % 6;
        uint8_t block[144][4];
        for (uint32_t i = 0; i < count; i++) {
            for (uint32_t c = 0; c < 4; c++) block[i][c] = 0;
        }
        switch (cls) {
        case 0: /* noisy RGBA: high error, triggers partition/dual paths */
            for (uint32_t i = 0; i < count; i++) {
                for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)rnd();
                block[i][3] = (uint8_t)(50 + rnd() % 200);
            }
            break;
        case 1: /* luminance ramp: r=g=b, alpha varies (CEM 4) */
            for (uint32_t i = 0; i < count; i++) {
                uint32_t v = (rnd() % 3 + i * 97u + (rnd() & 15u)) & 0xff;
                block[i][0] = block[i][1] = block[i][2] = (uint8_t)v;
                block[i][3] = (uint8_t)(s % 2 ? 255 : (rnd() & 0xff));
            }
            break;
        case 2: /* rgb scale: one hue scaled per texel (CEM 6/10) */
        {
            uint8_t hue[3] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                               (uint8_t)(rnd() & 0xff) };
            for (uint32_t i = 0; i < count; i++) {
                uint32_t t = 64 + rnd() % 192;
                for (uint32_t c = 0; c < 3; c++)
                    block[i][c] = (uint8_t)((hue[c] * t) >> 8);
                block[i][3] = (uint8_t)(s % 3 == 0 ? 255 : (rnd() & 0xff));
            }
            break;
        }
        case 3: /* const colour (CEM 0/const fallback; opaque 6x6 = the
                   medium-tier opaque special cases) */
        {
            uint8_t col[4] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                               (uint8_t)(rnd() & 0xff), 255 };
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) block[i][c] = col[c];
            break;
        }
        case 4: /* high-contrast checker: 0/255 extremes */
            for (uint32_t i = 0; i < count; i++) {
                uint32_t v = (rnd() & 1) ? 255 : 0;
                block[i][0] = block[i][1] = block[i][2] = (uint8_t)v;
                block[i][3] = (uint8_t)((rnd() & 1) ? 255 : 0);
            }
            break;
        case 5: /* smooth gradient: low error, single-path early-out */
            for (uint32_t i = 0; i < count; i++) {
                uint32_t x = i % bx, y = i / bx;
                block[i][0] = (uint8_t)((x * 255) / (bx > 1 ? bx - 1 : 1));
                block[i][1] = (uint8_t)((y * 255) / (by > 1 ? by - 1 : 1));
                block[i][2] = (uint8_t)((x + y) * 255 /
                                        (bx + by > 2 ? bx + by - 2 : 1));
                block[i][3] = 255;
            }
            break;
        }
        tc_astc_encode_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        tc_astc_encode_context_init(&ctx, bx, by, quality);
        uint8_t outb[16];
        memset(outb, 0, sizeof(outb));
        tc_encode_astc_ldr_block(block, count, quality, &ctx, outb);
        fprintf(out, "L %u %u %d", bx, by, quality);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
