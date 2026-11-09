/* BC6H per-block mode-selection driver vectors: C vs Lean.
 *
 * Each line is `u <16 bytes>` (unsigned driver) or `s <16 bytes>` (signed
 * driver) for the block whose 16x3 float bits precede it as 48 hex words.
 * Per line: `u|s <48 float bits> | <16 bytes>`.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc6h.c"

static uint64_t rng = 0xdeadbeefcafef00dULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float F(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }

static void make_block(uint32_t px[16][3], int kind) {
    uint32_t e = 120u + (uint32_t)(rnd() % 18u);
    uint32_t mbase = (uint32_t)(rnd() % 200u) * 0x4000u;
    uint32_t sgn = (rnd() & 1u) ? 0x80000000u : 0u;
    for (int i = 0; i < 16; i++) {
        for (int c = 0; c < 3; c++) {
            uint32_t ee = e, m, s = sgn;
            switch (kind) {
            case 0: { /* tight, one sign */
                int32_t d = (int32_t)(rnd() % 9u) - 4;
                int64_t mm = (int64_t)mbase + (int64_t)d * 0x4000;
                if (mm < 0) mm = 0;
                if (mm > 0x7fffff) mm = 0x7fffff;
                m = (uint32_t)mm;
                break;
            }
            case 1: { /* tight magnitude, random signs */
                int32_t d = (int32_t)(rnd() % 9u) - 4;
                int64_t mm = (int64_t)mbase + (int64_t)d * 0x4000;
                if (mm < 0) mm = 0;
                if (mm > 0x7fffff) mm = 0x7fffff;
                m = (uint32_t)mm;
                s = (rnd() & 1u) ? 0x80000000u : 0u;
                break;
            }
            case 2: { /* wide: random exponent and sign */
                ee = 112u + (uint32_t)(rnd() % 32u);
                m = (uint32_t)(rnd() & 0x7fffffu);
                s = (rnd() & 1u) ? 0x80000000u : 0u;
                break;
            }
            default: { /* fully random finite float bits */
                uint32_t u = (uint32_t)rnd();
                u &= 0x807fffffu;
                u |= ((uint32_t)(1u + rnd() % 254u)) << 23;
                px[i][c] = u;
                continue;
            }
            }
            px[i][c] = s | (ee << 23) | m;
        }
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }
    for (int s = 0; s < 240; s++) {
        uint32_t px[16][3];
        float fp[16][3];
        uint8_t blk[16];
        make_block(px, s % 4);
        for (int i = 0; i < 16; i++)
            for (int c = 0; c < 3; c++) fp[i][c] = F(px[i][c]);
        for (int variant = 0; variant < 2; variant++) {
            if (variant == 0) tc_encode_bc6h_block_uf16(fp, blk);
            else tc_encode_bc6h_block_sf16(fp, blk);
            fprintf(out, "%c", variant == 0 ? 'u' : 's');
            for (int i = 0; i < 16; i++)
                for (int c = 0; c < 3; c++) fprintf(out, " %08x", px[i][c]);
            fprintf(out, " |");
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
