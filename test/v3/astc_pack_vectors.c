/* ASTC HDR endpoint pack differential vectors (encoder side).
 *
 * Emits, per line:
 *   cem11 <6x lns0> <6x lns1 (first 3 used)> | <6 packed bytes>
 *   alpha <alns0> <alns1> | <2 packed bytes>
 * The C packers are called at colour quant level 20 (the identity level the
 * block encoders use); the Lean ports model that path.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Defined in texcomp_astc_hdr.c (no public header prototype). */
void tc_astc_cem11_pack(const int lns0[3], const int lns1[3], int level,
                        uint8_t v[6]);
void tc_astc_cem7_pack(const int e0[3], const int e1[3], int level,
                       uint8_t v[4]);
void tc_astc_hdr_alpha_pack(int alns0, int alns1, uint8_t out[2]);

static uint64_t rng_state = 0x9e3779b97f4a7c15ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* Mix of fully random and clustered endpoint pairs: the mode search only
 * reaches its base+offset branches when the endpoints are close. */
static void make_pair(int a[3], int b[3], int cluster) {
    for (int c = 0; c < 3; c++) {
        if (cluster) {
            int base = (int)(rnd() % 65536u);
            int d = (int)(rnd() % 2049u) - 1024;
            int v = base + d;
            a[c] = v < 0 ? 0 : (v > 65535 ? 65535 : v);
            v = base + d + (int)(rnd() % 129u) - 64;
            b[c] = v < 0 ? 0 : (v > 65535 ? 65535 : v);
        } else {
            a[c] = (int)(rnd() % 65536u);
            b[c] = (int)(rnd() % 65536u);
        }
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }
    for (int s = 0; s < 900; s++) {
        int a[3], b[3];
        uint8_t v[6];
        make_pair(a, b, s % 3 != 0);
        tc_astc_cem11_pack(a, b, 20, v);
        fprintf(out, "cem11 %d %d %d %d %d %d |", a[0], a[1], a[2], b[0], b[1], b[2]);
        for (int i = 0; i < 6; i++) fprintf(out, " %02x", v[i]);
        fprintf(out, "\n");
    }
    for (int s = 0; s < 600; s++) {
        int a[3], b[3];
        uint8_t v[4];
        make_pair(a, b, s % 2 == 0);
        tc_astc_cem7_pack(a, b, 20, v);
        fprintf(out, "cem7 %d %d %d %d %d %d |", a[0], a[1], a[2], b[0], b[1], b[2]);
        for (int i = 0; i < 4; i++) fprintf(out, " %02x", v[i]);
        fprintf(out, "\n");
    }
    for (int s = 0; s < 300; s++) {
        int a0, a1;
        uint8_t v[2];
        if (s % 3 == 0) {
            a0 = (int)(rnd() % 65281u);
            a1 = a0 + (int)(rnd() % 257u) - 128;
        } else {
            a0 = (int)(rnd() % 65281u);
            a1 = (int)(rnd() % 65281u);
        }
        if (a1 < 0) a1 = 0;
        tc_astc_hdr_alpha_pack(a0, a1, v);
        fprintf(out, "alpha %d %d |", a0, a1);
        for (int i = 0; i < 2; i++) fprintf(out, " %02x", v[i]);
        fprintf(out, "\n");
    }
    fclose(out);
    return 0;
}
