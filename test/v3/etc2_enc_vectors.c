/* ETC2 RGB / EAC alpha block-encoder vectors (C side).
 *   E <64 texel bytes (16 x RGBA, ETC order)> | flat | ind bits err | diff bits err
 *     | planar bits err | rgb | eac
 * The candidate encoders are static, so the sources are included directly.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_etc2.c"
#include "texcomp_eac.c"

static uint32_t rng = 0x9e3779b9u;
static uint32_t rn(void) { rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5; return rng; }
static uint8_t cl(int v) { return (uint8_t)(v < 0 ? 0 : v > 255 ? 255 : v); }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 400; s++) {
        uint8_t b[16][4];
        int cls = s % 10;
        int base[3] = {(int)(rn() % 256), (int)(rn() % 256), (int)(rn() % 256)};
        int other[3] = {(int)(rn() % 256), (int)(rn() % 256), (int)(rn() % 256)};
        int amp = 1 + (int)(rn() % 6);
        int gx[3], gy[3];
        for (int c = 0; c < 3; c++) { gx[c] = (int)(rn() % 41) - 20; gy[c] = (int)(rn() % 41) - 20; }
        for (int i = 0; i < 16; i++) {
            int x = i / 4, y = i % 4; /* ETC order */
            for (int c = 0; c < 3; c++) {
                int v;
                switch (cls) {
                case 0: v = (int)(rn() % 256); break;                      /* noise */
                case 1: v = base[c]; break;                                 /* flat */
                case 2: v = base[c] + (int)(rn() % (2 * amp + 1)) - amp; break; /* near-flat */
                case 3: v = base[c] + gx[c] * x + gy[c] * y; break;         /* smooth gradient */
                case 4: v = base[c] + gx[c] * x + gy[c] * y + (int)(rn() % 5) - 2; break;
                case 5: v = (x < 2) ? base[c] : other[c]; break;            /* left/right */
                case 6: v = (y < 2) ? base[c] : other[c]; break;            /* top/bottom */
                case 7: v = ((x < 2) ? base[c] : other[c]) + (int)(rn() % 9) - 4; break;
                case 8: v = (rn() & 1) ? base[c] : other[c]; break;         /* two-tone */
                default: v = base[c] + (int)(rn() % 64) - 32; break;
                }
                b[i][c] = cl(v);
            }
            switch (s % 4) {
            case 0: b[i][3] = (uint8_t)rn(); break;
            case 1: b[i][3] = 200; break;                                   /* constant */
            case 2: b[i][3] = (rn() & 1) ? 255 : 0; break;
            default: b[i][3] = cl(100 + 7 * x + 3 * y + (int)(rn() % 3)); break;
            }
        }
        uint8_t alpha[16];
        for (int i = 0; i < 16; i++) alpha[i] = b[i][3];
        uint64_t ie, de, pe;
        uint64_t flat = tc_encode_etc2_rgb_flat(b);
        uint64_t ind = tc_encode_etc1_individual(b, &ie);
        uint64_t dif = tc_encode_etc1_differential(b, &de);
        uint64_t pla = tc_encode_etc2_rgb_planar(b, &pe);
        uint64_t rgb = tc_encode_etc2_rgb(b);
        uint64_t eac = tc_encode_eac_alpha(alpha);
        fprintf(out, "E");
        for (int i = 0; i < 16; i++) for (int c = 0; c < 4; c++) fprintf(out, " %02x", b[i][c]);
        fprintf(out, " | %llx | %llx %llx | %llx %llx | %llx %llx | %llx | %llx\n",
                (unsigned long long)flat, (unsigned long long)ind, (unsigned long long)ie,
                (unsigned long long)dif, (unsigned long long)de, (unsigned long long)pla,
                (unsigned long long)pe, (unsigned long long)rgb, (unsigned long long)eac);
    }
    fclose(out);
    return 0;
}
