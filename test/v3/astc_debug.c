/* ASTC debug: dump intermediates for a block using the reference decoder. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tools/texcomp/test/astc_ref_decode.h"

int main(int argc, char **argv) {
    uint8_t block[16];
    for (int i = 0; i < 16; i++) {
        char tmp[3] = {argv[1][i*2], argv[1][i*2+1], 0};
        block[i] = (uint8_t)strtoul(tmp, NULL, 16);
    }
    uint32_t mode = aref_rd_bits(block, 0, 11);
    printf("mode=%u (0x%x)\n", mode, mode);
    uint32_t wx, wy, wq, dual;
    if (!aref_decode_block_mode_2d(mode, &wx, &wy, &wq, &dual)) { printf("bad mode\n"); return 1; }
    printf("wx=%u wy=%u wquant=%u dual=%u\n", wx, wy, wq, dual);
    uint32_t pc = aref_rd_bits(block, 11, 2) + 1;
    uint32_t wc = wx * wy * (dual ? 2 : 1);
    uint32_t wb = aref_ise_bitcount(wc, wq);
    printf("part=%u weight_count=%u weight_bits=%u\n", pc, wc, wb);
    uint8_t rev[16];
    for (uint32_t i = 0; i < 16; i++) rev[i] = aref_bitrev8(block[15 - i]);
    uint8_t ws[64];
    if (!aref_ise_decode(wq, wc, rev, 0, ws)) { printf("ise fail\n"); return 1; }
    printf("wsyms:");
    for (uint32_t i = 0; i < wc; i++) printf(" %u", ws[i]);
    printf("\nwgrid:");
    for (uint32_t i = 0; i < wx * wy; i++)
        printf(" %u", aref_weight_unquant[wq][dual ? ws[i * 2] : ws[i]]);
    printf("\n");
    uint32_t pindex = aref_rd_bits(block, 13, 10);
    uint32_t cf = aref_rd_bits(block, 23, 6);
    printf("pindex=%u cf=%u\n", pindex, cf);
    uint32_t cems[4] = {0,0,0,0};
    uint32_t color_start;
    if (pc == 1) { cems[0] = aref_rd_bits(block, 13, 4); color_start = 17; }
    else {
        color_start = 29;
        if ((cf & 3) == 0) for (uint32_t i = 0; i < pc; i++) cems[i] = cf >> 2;
        else {
            uint32_t base_class = (cf & 3) - 1;
            uint32_t extra = 3 * pc - 4;
            uint32_t ext = 128 - wb - extra;
            uint32_t code = cf | (aref_rd_bits(block, ext, extra) << 6);
            for (uint32_t i = 0; i < pc; i++) {
                uint32_t ci = (code >> (2 + i)) & 1;
                uint32_t mi = (code >> (2 + pc + 2 * i)) & 3;
                cems[i] = ((base_class + ci) << 2) | mi;
            }
        }
    }
    printf("cems: %u %u %u %u color_start=%u\n", cems[0], cems[1], cems[2], cems[3], color_start);
    uint32_t vcount = 0;
    for (uint32_t i = 0; i < pc; i++) vcount += (((cems[i] >> 2) + 1) * 2);
    printf("vcount=%u\n", vcount);
    uint32_t ccs_bits = dual ? 2 : 0;
    uint32_t used = color_start + wb + (dual ? 0 : 0) + ccs_bits;
    /* extra_bits needed for mult-partition case */
    uint32_t avail = 128 - used;
    int cq = -1;
    for (int i = 20; i >= 4; i--) if (aref_ise_bitcount(vcount, (uint32_t)i) <= avail) { cq = i; break; }
    printf("cq=%d\n", cq);
    uint8_t cs[18], vals[18];
    if (cq >= 0 && aref_ise_decode((uint32_t)cq, vcount, block, color_start, cs)) {
        for (uint32_t i = 0; i < vcount; i++)
            vals[i] = cq == 20 ? cs[i] : aref_color_unquant[cq - 4][cs[i]];
        printf("csyms:"); for (uint32_t i = 0; i < vcount; i++) printf(" %u", cs[i]);
        printf("\nvals:"); for (uint32_t i = 0; i < vcount; i++) printf(" %u", vals[i]);
        printf("\n");
        /* CEM dump */
        int is_dual = dual ? 1 : 0; (void)is_dual;
        for (uint32_t p = 0; p < pc; p++) { (void)p; }
    }
    return 0;
}
