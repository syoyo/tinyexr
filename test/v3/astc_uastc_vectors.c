/* ASTC UASTC LDR block encoder test-vector generator (C side).
 *
 * Emits one line per case:
 *   U <bx> <by> <quality> <count*4 rgba bytes> | <16 hex block bytes>
 *
 * The Lean differential checker (lean/AstcUastcCheck.lean) replays these
 * against `astcEncodeUastcLdrBlock` and requires bit-identical output.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"

static uint32_t rng = 0x5eed1357u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 60; s++) {
        uint32_t bx = 4, by = 4, count = 16;
        int quality = s % 3;
        int cls = (s / 3) % 7;
        uint8_t block[144][4];
        memset(block, 0, sizeof(block));
        switch (cls) {
        case 0: /* noisy RGBA: exercises CEM 12 + 2-subset + dual + CEM 4 */
            for (uint32_t i = 0; i < count; i++) {
                for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)rnd();
                block[i][3] = (uint8_t)(rnd() % 2 ? 255 : 60 + rnd() % 60);
            }
            break;
        case 1: /* noisy opaque: CEM 8 single/2/3-subset + dual */
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 3; c++) block[i][c] = (uint8_t)rnd();
            for (uint32_t i = 0; i < count; i++) block[i][3] = 255;
            break;
        case 2: /* grayscale + alpha: CEM 4 modes 15/16/17 */
            for (uint32_t i = 0; i < count; i++) {
                uint8_t v = (uint8_t)(rnd() & 0xff);
                block[i][0] = block[i][1] = block[i][2] = v;
                block[i][3] = (uint8_t)(40 + rnd() % 200);
            }
            break;
        case 3: /* const colour: solid (void-extent) */
        {
            uint8_t col[4] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                               (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff) };
            for (uint32_t i = 0; i < count; i++)
                for (uint32_t c = 0; c < 4; c++) block[i][c] = col[c];
            break;
        }
        case 4: /* two-colour half split: partitions + ccs selection */
        {
            uint8_t a[4] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                             (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff) };
            uint8_t b[4] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                             (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff) };
            for (uint32_t i = 0; i < count; i++) {
                const uint8_t *p = ((i % 4) < 2) ? a : b;
                for (uint32_t c = 0; c < 4; c++) block[i][c] = p[c];
            }
            break;
        }
        case 5: /* smooth gradient */
            for (uint32_t i = 0; i < count; i++) {
                uint32_t x = i % 4, y = i / 4;
                block[i][0] = (uint8_t)(x * 85);
                block[i][1] = (uint8_t)(y * 85);
                block[i][2] = (uint8_t)((x + y) * 42);
                block[i][3] = 255;
            }
            break;
        case 6: /* single hue, alpha ramp: CEM 4 vs CEM 12 contest */
        {
            uint8_t hue[3] = { (uint8_t)(rnd() & 0xff), (uint8_t)(rnd() & 0xff),
                               (uint8_t)(rnd() & 0xff) };
            for (uint32_t i = 0; i < count; i++) {
                for (uint32_t c = 0; c < 3; c++)
                    block[i][c] = (uint8_t)(hue[c] + (rnd() % 17) - 8);
                block[i][3] = (uint8_t)(i * 16);
            }
            break;
        }
        }
        tc_astc_encode_context ctx;
        memset(&ctx, 0, sizeof(ctx));
        tc_astc_encode_context_init(&ctx, bx, by, quality);
        uint8_t outb[16];
        memset(outb, 0, sizeof(outb));
        tc_encode_uastc_ldr_block(block, count, &ctx, outb);
        fprintf(out, "U %u %u %d", bx, by, quality);
        for (uint32_t i = 0; i < count; i++)
            for (uint32_t c = 0; c < 4; c++) fprintf(out, " %u", block[i][c]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
