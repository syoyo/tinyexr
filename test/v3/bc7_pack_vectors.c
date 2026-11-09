/* BC7 candidate pack/palette vectors: C vs Lean.
 *
 * The BC7 block packer and reconstruction palette are static inside
 * texcomp_bc7.c, so this translation unit includes it (the archive is
 * linked for the shared helpers, which resolve to these definitions).
 *
 * Emits, per line:
 *   bc7 <mode> <partition> <isel> <rot> <12 lo> <12 hi> <6 pbits>
 *       <16 sel> <16 asel> | <16 packed bytes>
 *   pal <same fields> | <subsets*n*4 palette bytes>
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "texcomp.h"
#include "../../tools/texcomp/src/texcomp_internal.h"
#include "../../tools/texcomp/src/texcomp_bc7.c"

static uint64_t rng = 0x1234abcd5678ef90ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void make_cand(tc_bc7_candidate *c, int mode_override) {
    memset(c, 0, sizeof(*c));
    c->mode = (uint8_t)(mode_override >= 0 ? mode_override : (int)(rnd() % 8u));
    c->partition = (uint8_t)(rnd() % 64u);
    c->index_selector = (c->mode == 4u || c->mode == 5u) ? (uint8_t)(rnd() % 2u) : 0u;
    c->rotation = (uint8_t)(rnd() % 4u);
    for (int s = 0; s < 3; s++) {
        for (int k = 0; k < 4; k++) {
            c->lo[s][k] = (uint8_t)rnd();
            c->hi[s][k] = (uint8_t)rnd();
        }
        c->pbits[s][0] = (uint8_t)(rnd() % 2u);
        c->pbits[s][1] = (uint8_t)(rnd() % 2u);
    }
    /* Selectors must be in range for the mode (the encoder always is): the
     * packer's anchor-swap subtraction assumes `sel < ncolor`. */
    {
        unsigned ncolor = 1u << (tc_bc7_color_index_bits[c->mode] + c->index_selector);
        unsigned nalpha = ncolor;
        if (tc_bc7_sep_alpha[c->mode] &&
            tc_bc7_alpha_index_bits[c->mode] > c->index_selector)
            nalpha = 1u << (tc_bc7_alpha_index_bits[c->mode] - c->index_selector);
        for (int i = 0; i < 16; i++) {
            c->selectors[i] = (uint8_t)(rnd() % ncolor);
            c->alpha_selectors[i] = (uint8_t)(rnd() % nalpha);
        }
    }
}

static void print_cand(FILE *out, const tc_bc7_candidate *c) {
    fprintf(out, "%u %u %u %u", c->mode, c->partition, c->index_selector, c->rotation);
    for (int s = 0; s < 3; s++)
        for (int k = 0; k < 4; k++) fprintf(out, " %u", c->lo[s][k]);
    for (int s = 0; s < 3; s++)
        for (int k = 0; k < 4; k++) fprintf(out, " %u", c->hi[s][k]);
    for (int s = 0; s < 3; s++)
        for (int k = 0; k < 2; k++) fprintf(out, " %u", c->pbits[s][k]);
    for (int i = 0; i < 16; i++) fprintf(out, " %u", c->selectors[i]);
    for (int i = 0; i < 16; i++) fprintf(out, " %u", c->alpha_selectors[i]);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    tc_bc7_candidate c;
    uint8_t blk[16];
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    for (int mode = 0; mode < 8; mode++) {
        for (int s = 0; s < 60; s++) {
            make_cand(&c, mode);
            tc_pack_candidate(&c, blk);
            fprintf(out, "bc7 ");
            print_cand(out, &c);
            fprintf(out, " |");
            for (int i = 0; i < 16; i++) fprintf(out, " %02x", blk[i]);
            fprintf(out, "\n");
        }
    }
    for (int mode = 0; mode < 8; mode++) {
        for (int s = 0; s < 20; s++) {
            uint8_t pal[3][16][4];
            unsigned subsets = tc_bc7_num_subsets[mode];
            unsigned maxSel = 1u << (tc_bc7_color_index_bits[mode] + c.index_selector);
            unsigned aBits = tc_bc7_alpha_index_bits[mode];
            unsigned n;
            make_cand(&c, mode);
            maxSel = 1u << (tc_bc7_color_index_bits[c.mode] + c.index_selector);
            n = maxSel;
            if (aBits > c.index_selector) {
                unsigned m = 1u << (aBits - c.index_selector);
                if (m > n) n = m;
            }
            memset(pal, 0, sizeof(pal));
            tc_fill_palette(&c, c.mode, pal);
            fprintf(out, "pal ");
            print_cand(out, &c);
            fprintf(out, " |");
            for (unsigned ss = 0; ss < subsets; ss++)
                for (unsigned sel = 0; sel < n; sel++)
                    for (int k = 0; k < 4; k++) fprintf(out, " %u", pal[ss][sel][k]);
            fprintf(out, "\n");
        }
    }
    fclose(out);
    return 0;
}
