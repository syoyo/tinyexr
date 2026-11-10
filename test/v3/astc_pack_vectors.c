/* ASTC pack-partition-RGB vectors: C vs Lean.
 *
 * `P <blockMode> <partitionCount> <piSeed> <endpointFormatsMatched> <endpointHighpartSize>
 *   <endpointFormats...> <colorQuantMethod> <endpointValueCount> <weightBits>
 *   <weightbuf16> <colorValues...> | <16 bytes>`\n */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "texcomp_internal.h"
#include "texcomp_astc.c"

static uint32_t rng = 0x9e3779b9u;
static uint32_t rnd(void) {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    /* endpoint format templates per partition count */
    static const int fmts2[4][2] = {{6,6},{8,8},{10,10},{12,12}};
    static const int fmts3[4][3] = {{6,6,6},{8,8,8},{10,10,10},{12,12,12}};
    static const int fmts4[4][4] = {{6,6,6,6},{8,8,8,8},{6,8,6,8},{10,10,10,10}};

    for (int s = 0; s < 400; s++) {
        uint32_t partitionCount = 2 + rnd() % 3; /* 2,3,4 */
        uint32_t blockMode = rnd() % 2048;
        uint32_t piSeed = rnd() % 1024;
        int matched = rnd() % 2;
        uint32_t endpointHighpartSize = 0;
        uint32_t weightBits = (rnd() % 4) * 4 + 4; /* 4,8,12,16 */
        if (weightBits > 16) weightBits = 12;
        uint32_t colorQuantMethod;
        uint32_t endpointValueCount;
        const int *fmts;
        uint32_t nfmts = partitionCount;
        uint8_t formats[4] = {0, 0, 0, 0};

        if (partitionCount == 2) { fmts = fmts2[rnd() % 4]; }
        else if (partitionCount == 3) { fmts = fmts3[rnd() % 4]; }
        else { fmts = fmts4[rnd() % 4]; }
        for (uint32_t i = 0; i < nfmts; i++) formats[i] = (uint8_t)fmts[i];

        /* endpoint value count */
        endpointValueCount = 0;
        for (uint32_t i = 0; i < nfmts; i++) {
            int f = formats[i];
            if (f == 6) endpointValueCount += 4;
            else if (f == 10) endpointValueCount += 6;
            else if (f == 12) endpointValueCount += 8;
            else endpointValueCount += 6;
        }
        colorQuantMethod = (rnd() % 12) + 4;
        if (colorQuantMethod > 16) colorQuantMethod = 8;

        if (!matched) {
            endpointHighpartSize = 3 * partitionCount - 4;
        }

        /* weightbuf: 16 bytes */
        uint8_t weightbuf[16];
        for (int i = 0; i < 16; i++) weightbuf[i] = (uint8_t)rnd();

        /* color_values: endpointValueCount bytes, in range for quant method */
        static const uint8_t bits[21] = {1, 0, 2, 0, 1, 3, 1, 2, 4, 2, 3, 5, 3, 4, 6, 4, 5, 7, 5, 6, 8};
        uint8_t colorValues[64];
        uint32_t nbits = bits[colorQuantMethod];
        if (nbits == 0) nbits = 1;
        for (uint32_t i = 0; i < endpointValueCount && i < 64; i++)
            colorValues[i] = (uint8_t)(rnd() % (1u << nbits));

        /* call C */
        uint8_t outb[16];
        tc_astc_pack_partition_rgb(blockMode, partitionCount, piSeed,
            (const uint8_t *)formats, matched, endpointHighpartSize,
            colorValues, colorQuantMethod, endpointValueCount,
            weightBits, weightbuf, outb);

        /* emit vector */
        fprintf(out, "P %u %u %u %u %u", blockMode, partitionCount, piSeed, matched, endpointHighpartSize);
        for (uint32_t i = 0; i < nfmts; i++) fprintf(out, " %d", formats[i]);
        fprintf(out, " %u %u %u", colorQuantMethod, endpointValueCount, weightBits);
        for (int i = 0; i < 16; i++) fprintf(out, " %u", weightbuf[i]);
        for (uint32_t i = 0; i < endpointValueCount && i < 64; i++) fprintf(out, " %u", colorValues[i]);
        fprintf(out, " |");
        for (int i = 0; i < 16; i++) fprintf(out, " %02x", outb[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
