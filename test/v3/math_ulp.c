/*
 * TinyEXR - validation of the two libm-free math tiers against libm.
 *
 *   ./build/math_ulp            structured + random (CI default)
 *   ./build/math_ulp --full     exhaustive sweeps (long)
 *
 * Reports, per function: the maximum ULP distance, the number of exactly
 * equal results and the number of results over the tier threshold. Exits
 * non-zero if any threshold is exceeded.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "exr_math.h"
#include "exr_math_impl.h"

/* Original core entry points (defined in the same object) for the frozen test. */
float exr_util_log2f(float x);
float exr_util_exp2f(float x);

static int g_full = 0;
static int g_pow_one = 0;
static int g_accurate = 0;
static int g_failed = 0;

static uint32_t f2b(float f) { return exr_math_i_f2b32(f); }
static float b2f(uint32_t u) { return exr_math_i_b2f32(u); }

/* Ordered integer mapping: monotone across the whole binary32 domain. */
static uint32_t ordered(uint32_t b) {
    return (b & 0x80000000u) ? ~b : (b | 0x80000000u);
}
static uint64_t ulp_dist(float a, float b) {
    uint32_t ua = f2b(a), ub = f2b(b);
    uint32_t oa, ob;
    int64_t d;
    if (a != a || b != b) return (a != a && b != b) ? 0 : 1;
    oa = ordered(ua);
    ob = ordered(ub);
    d = (int64_t)oa - (int64_t)ob;
    return d < 0 ? (uint64_t)-d : (uint64_t)d;
}

typedef struct {
    const char *name;
    uint64_t max_ulp;
    uint64_t exact;
    uint64_t over;
    uint64_t n;
    uint64_t limit;
} stat;

static void report(const stat *s) {
    printf("%-12s n=%-12llu max_ulp=%-6llu exact=%-12llu over=%llu (limit %llu)\n",
           s->name, (unsigned long long)s->n, (unsigned long long)s->max_ulp,
           (unsigned long long)s->exact, (unsigned long long)s->over,
           (unsigned long long)s->limit);
    if (s->over) g_failed = 1;
}
static void add(stat *s, float got, float ref) {
    uint64_t d = ulp_dist(got, ref);
    ++s->n;
    if (d == 0) ++s->exact;
    if (d > s->max_ulp) s->max_ulp = d;
    if (d > s->limit) ++s->over;
}

static uint32_t st = 0x12345678u;
static uint32_t rnd(void) {
    st ^= st << 13; st ^= st >> 17; st ^= st << 5; return st;
}
static float random_finite_f32(void) {
    uint32_t b = rnd() & 0x7f7fffffu;
    return b2f(b);
}

/* ---- special-value contracts --------------------------------------------- */

static void check_special(void) {
    stat s = { "special", 0, 0, 0, 0, 0 };
    float inf = b2f(0x7f800000u), nan = b2f(0x7fc00000u);
    int ok = 1;
    if (!(isnan(exr_math_log2f(-1.0f)))) ok = 0;
    if (!isinf(exr_math_log2f(0.0f)) || exr_math_log2f(0.0f) > 0) ok = 0;
    if (exr_math_log2f(inf) != inf) ok = 0;
    if (!isnan(exr_math_log2f(nan))) ok = 0;
    if (exr_math_exp2f(inf) != inf) ok = 0;
    if (exr_math_exp2f(-inf) != 0.0f) ok = 0;
    if (!isnan(exr_math_exp2f(nan))) ok = 0;
    if (exr_math_exp2f(127.0f) != exr_math_i_b2f32(0x7f000000u)) ok = 0;
    if (exr_math_powf(0.0f, 2.0f) != 0.0f) ok = 0;
    if (exr_math_powf(0.0f, -1.0f) != inf) ok = 0;
    if (exr_math_powf(2.0f, 0.0f) != 1.0f) ok = 0;
    if (exr_math_powf(-2.0f, 2.0f) != 4.0f) ok = 0;
    if (!isnan(exr_math_powf(-2.0f, 0.5f))) ok = 0;
    if (!isnan(exr_math_sqrtf_exact(-1.0f))) ok = 0;
    if (exr_math_sqrtf_exact(0.0f) != 0.0f) ok = 0;
    if (exr_math_sqrtf_exact(4.0f) != 2.0f) ok = 0;
    if (exr_math_sqrtf_exact(inf) != inf) ok = 0;
    s.n = 16;
    s.exact = ok ? 16 : 0;
    s.over = ok ? 0 : 1;
    s.max_ulp = ok ? 0 : 1;
    report(&s);
    if (!ok) g_failed = 1;
}

/* ---- exact square root ---------------------------------------------------- */

static void check_sqrt_exact(void) {
    stat s = { "sqrt_exact", 0, 0, 0, 0, 0 };
    uint64_t i;
    if (g_full) {
        for (i = 0; i <= 0xffffffffULL; ++i) {
            float x = b2f((uint32_t)i);
            add(&s, exr_math_sqrtf_exact(x), sqrtf(x));
        }
    } else {
        static const uint32_t seeds[] = {
            0x00000001u, 0x00000002u, 0x00400000u, 0x007fffffu,
            0x00800000u, 0x3f800000u, 0x40000000u, 0x7f7fffffu,
            0x7f800000u, 0x7fc00000u, 0xff800000u, 0x80000000u
        };
        size_t k;
        for (k = 0; k < sizeof(seeds) / sizeof(seeds[0]); ++k)
            add(&s, exr_math_sqrtf_exact(b2f(seeds[k])), sqrtf(b2f(seeds[k])));
        for (i = 0; i < (1u << 24); ++i) {
            float x = random_finite_f32();
            add(&s, exr_math_sqrtf_exact(x), sqrtf(x));
        }
    }
    report(&s);
}

/* ---- log2f ---------------------------------------------------------------- */

static void log2_sample(stat *s, float x) {
    if (!(x > 0.0f) || !isfinite(x)) return;
    add(s, exr_math_log2f(x), log2f(x));
}
static void check_log2(void) {
    static const int exps[] = { 1, 64, 126, 127, 128, 191, 254 };
    stat s = { "log2f", 0, 0, 0, 0, 1 };
    uint64_t i;
    size_t k;
    if (g_full) {
        for (i = 1; i <= 254; ++i) {
            uint32_t m;
            for (m = 0; m < (1u << 23); ++m)
                log2_sample(&s, b2f(((uint32_t)i << 23) | m));
        }
    } else {
        for (k = 0; k < sizeof(exps) / sizeof(exps[0]); ++k) {
            uint32_t m;
            for (m = 0; m < (1u << 23); ++m)
                log2_sample(&s, b2f(((uint32_t)exps[k] << 23) | m));
        }
        for (i = 0; i < (1u << 24); ++i) log2_sample(&s, random_finite_f32());
    }
    report(&s);
}

/* ---- exp2f / expf --------------------------------------------------------- */

static void exp2_sample(stat *s2, stat *se, float x) {
    if (!isfinite(x) || x < -125.0f || x > 127.0f) return;
    add(s2, exr_math_exp2f(x), exp2f(x));
    if (x > -87.0f && x < 88.0f) add(se, exr_math_expf(x), expf(x));
}
static void check_exp2(void) {
    stat s2 = { "exp2f", 0, 0, 0, 0, 1 };
    stat se = { "expf", 0, 0, 0, 0, 1 };
    uint64_t i;
    if (g_full) {
        for (i = 0; i <= 0xffffffffULL; ++i)
            exp2_sample(&s2, &se, b2f((uint32_t)i));
    } else {
        for (i = 0; i < (1u << 25); ++i) {
            float x = -126.0f + 253.0f * (float)(i & 0xffffffu) / 16777215.0f;
            exp2_sample(&s2, &se, x);
        }
        for (i = 0; i < (1u << 24); ++i)
            exp2_sample(&s2, &se, random_finite_f32() * 126.0f);
    }
    report(&s2);
    report(&se);
}

/* ---- powf ----------------------------------------------------------------- */

static void pow_sample(stat *s, float x, float y) {
    float ref;
    if (!(x > 0.0f) || !isfinite(x) || !isfinite(y)) return;
    ref = powf(x, y);
    if (!isfinite(ref)) return;
    add(s, exr_math_powf(x, y), ref);
}
static void check_pow(void) {
    stat s = { "powf", 0, 0, 0, 0, 1 };
    uint64_t i;
    if (g_full) {
        uint32_t m;
        for (m = 0; m < (1u << 23); ++m) {
            float x = b2f(0x3f800000u | m);
            int y;
            for (y = -8; y <= 8; ++y) pow_sample(&s, x, (float)y);
        }
    } else {
        for (i = 0; i < (1u << 24); ++i) {
            float x = b2f(0x3f800000u | (uint32_t)(rnd() & 0x7fffffu));
            float y = (float)((int)(rnd() % 17) - 8) +
                      (float)(rnd() & 0xffffu) / 65535.0f;
            pow_sample(&s, x, y);
        }
    }
    report(&s);
}

/* Exhaustive `powf(x, 1)` sweep over every positive normal binary32 input.
 * This is the Lean `powf_pow2_one_exact` / `powf_one_44ulp_witness` domain. */
static void check_pow_one(void) {
    stat s = { "powf(x,1)", 0, 0, 0, 0, 1 };
    uint32_t ef, m;
    if (!(g_full || g_pow_one)) return;
    for (ef = 1; ef <= 253; ++ef) {
        for (m = 0; m < (1u << 23); ++m) {
            float x = b2f((ef << 23) | m);
            add(&s, exr_math_powf(x, 1.0f), x);
        }
    }
    report(&s);
}

/* ---- tier independence: fast tier must still equal the original core ------ */

static void check_fast_frozen(void) {
    stat s = { "fast-frozen", 0, 0, 0, 0, 0 };
    uint64_t i;
    for (i = 0; i < (1u << 22); ++i) {
        float x = random_finite_f32();
        if (x > 0.0f && isfinite(x)) {
            add(&s, exr_math_log2f_fast(x), exr_util_log2f(x));
            add(&s, exr_math_exp2f_fast(x - 64.0f), exr_util_exp2f(x - 64.0f));
        }
    }
    report(&s);
}

/* ---- f64 table helpers ---------------------------------------------------- */

static void check_f64(void) {
    stat ss = { "sin64", 0, 0, 0, 0, 4 };
    stat se = { "exp64", 0, 0, 0, 0, 8 };
    stat sq = { "sqrt64", 0, 0, 0, 0, 8 };
    int i;
    for (i = 0; i < 20000; ++i) {
        double x = 3.0 * 3.14159265358979323846 * i / 19999.0;
        if (fabs(exr_math_sin(x) - sin(x)) > 1e-13) ++ss.over;
        ++ss.n;
    }
    for (i = 0; i < 20000; ++i) {
        double x = -4.5 * i / 19999.0;
        if (fabs(exr_math_exp64(x) - exp(x)) > 2e-13 * exp(x)) ++se.over;
        ++se.n;
    }
    for (i = 0; i < 20000; ++i) {
        double x = (double)i / 19999.0;
        if (fabs(exr_math_sqrt64(x) - sqrt(x)) > 2e-13) ++sq.over;
        ++sq.n;
    }
    report(&ss);
    report(&se);
    report(&sq);
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "--full") == 0) g_full = 1;
    if (argc > 1 && strcmp(argv[1], "--pow-one") == 0) g_pow_one = 1;
    if (argc > 1 && strcmp(argv[1], "--accurate") == 0) g_accurate = 1;
    if (g_accurate) {
        g_full = 1;
        printf("math ULP check: accurate-tier exhaustive domains\n");
        check_log2();
        check_exp2();
        check_pow();
        check_pow_one();
        printf("math ULP check: %s\n", g_failed ? "FAIL" : "OK");
        return g_failed ? 1 : 0;
    }
    if (g_pow_one) {
        printf("math ULP check: powf(x,1) exhaustive normal domain\n");
        check_pow_one();
        printf("math ULP check: %s\n", g_failed ? "FAIL" : "OK");
        return g_failed ? 1 : 0;
    }
    printf("math ULP check: %s\n", g_full ? "exhaustive" : "structured");
    check_special();
    check_sqrt_exact();
    check_log2();
    check_exp2();
    check_pow();
    check_pow_one();
    check_fast_frozen();
    check_f64();
    printf("math ULP check: %s\n", g_failed ? "FAIL" : "OK");
    return g_failed ? 1 : 0;
}
