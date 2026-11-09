/* ASTC HDR differential vectors: encoder blocks + C HDR decode of seeded
 * 4x4 float images. Format mirrors the LDR one:
 *   0 <blockhex> | <16 x R G B A floathex>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"

static uint64_t rng_state;
static uint64_t splitmix64(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static float randf(void) { return (float)(splitmix64() % 4000u) / 1000.0f - 1.0f; }

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    rng_state = 0xabcdef123456789ULL;
    tc_astc_hdr_options opt;
    memset(&opt, 0, sizeof(opt));
    tc_astc_hdr_options_init(&opt);
    int wrote = 0;
    for (int s = 0; s < 512 && wrote < 256; s++) {
        float img[16][4];
        int constant = (s % 5 == 0);
        float cr = randf() * 2.0f;
        float cg = randf() * 2.0f;
        float cb = randf() * 2.0f;
        float ca = (splitmix64() & 1) ? 0.5f : randf();
        for (int i = 0; i < 16; i++) {
            /* mostly clustered values so the encoder lands in non-void CEM modes */
            img[i][0] = constant ? cr : cr * (0.9f + 0.05f * randf());
            img[i][1] = constant ? cg : cg * (0.9f + 0.05f * randf());
            img[i][2] = constant ? cb : cb * (0.9f + 0.05f * randf());
            img[i][3] = constant ? ca : ca * (0.9f + 0.05f * randf());
        }
        uint8_t blk[16];
        if (tc_astc_hdr_compress_rgbaf(&img[0][0], 4, 4, 16 * sizeof(float),
                                       &opt, blk, sizeof(blk)) != TC_SUCCESS)
            continue;
        float px[16][4];
        if (tc_astc_hdr_decompress_rgbaf(blk, 4, 4, 4, 4, 16 * sizeof(float),
                                         &px[0][0], sizeof(px)) != TC_SUCCESS)
            continue;
        fprintf(out, "0 ");
        for (int i = 0; i < 16; i++) fprintf(out, "%02x", blk[i]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) {
            for (int c = 0; c < 4; c++) {
                uint32_t u;
                memcpy(&u, &px[i][c], 4);
                fprintf(out, " %08x", u);
            }
        }
        fprintf(out, "\n");
        wrote++;
    }
    fclose(out);
    return 0;
}
