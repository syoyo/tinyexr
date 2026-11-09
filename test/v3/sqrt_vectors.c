/* Correctly-rounded sqrtf vectors: C (freestanding exact + libm) vs Lean.
 *
 * Per line: `sqrt <input bits> <exact bits> <libm bits>`
 * The generator asserts exact == libm; the Lean checker compares against the
 * exact column.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "toc_internal.h"

static uint64_t rng = 0x9e3779b97f4a7c15ULL;
static uint64_t rnd(void) {
    uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static float F(uint32_t u) { float f; memcpy(&f, &u, 4); return f; }
static uint32_t B(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }

static int emit(FILE *out, uint32_t u) {
    uint32_t a = B(toc_sqrtf_exact(F(u)));
    uint32_t b = B(sqrtf(F(u)));
    fprintf(out, "sqrt %08x %08x %08x\n", u, a, b);
    return a != b;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    int diffs = 0;
    if (argc > 1) { out = fopen(argv[1], "w"); if (!out) return 1; }

    /* Specials and boundaries. */
    {
        static const uint32_t sp[] = {
            0x00000000u, 0x80000000u, 0x7f800000u, 0xff800000u, 0x7fc00000u,
            0x7fc12345u, 0x7f812345u, 0xffc12345u, 0x7f7fffffu, 0x00000001u,
            0x00000002u, 0x003fffffu, 0x00400000u, 0x00400001u, 0x007fffffu,
            0x00800000u, 0x3f800000u, 0xbf800000u, 0x40000000u, 0x40800000u,
            0x4b000000u, 0x7effffffu, 0x7f000000u, 0x7f000001u,
        };
        for (unsigned i = 0; i < sizeof(sp) / sizeof(sp[0]); i++)
            diffs += emit(out, sp[i]);
    }
    /* Every power of two exponent (all representable exponents). */
    for (uint32_t e = 0; e < 255; e++) {
        diffs += emit(out, (e << 23));
        diffs += emit(out, (e << 23) | 0x400000u);
        diffs += emit(out, (e << 23) | 0x7fffffu);
    }
    /* Exact squares of small integers and of 24-bit significands. */
    for (uint32_t n = 1; n <= 4096; n++) {
        float f = (float)n;
        diffs += emit(out, B(f * f));
    }
    /* Rounding-boundary probes: values just around midpoints. */
    for (uint32_t mant = 0; mant < 0x800000u; mant += 0x1555u) {
        diffs += emit(out, (127u << 23) | mant);
        diffs += emit(out, (100u << 23) | mant);
        diffs += emit(out, (150u << 23) | mant);
    }
    /* Random patterns (all classes: zero exp, subnormal, normal, huge). */
    for (int i = 0; i < 20000; i++)
        diffs += emit(out, (uint32_t)(rnd() >> 32));

    fclose(out);
    if (diffs) {
        fprintf(stderr, "exact vs libm: %d differences\n", diffs);
        return 2;
    }
    return 0;
}
