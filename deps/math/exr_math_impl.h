/*
 * TinyEXR - shared, dependency-free scalar math (two accuracy tiers).
 *
 * This header contains the single source of truth for the first-party
 * transcendentals used by the shipped libraries. It is header-only (all
 * functions are `static inline`) so each library gets its own copy without
 * cross-linking. Thin translation units export the prefixed symbols:
 *
 *   src/exr_math.c                  -> exr_math_* (core), exr_util_* (frozen fast)
 *   tools/resize/src/tir_math.c     -> tir_math_*
 *   tools/texcomp/src/texcomp_math.c-> tc_math_*
 *
 * Tiers (see ~/.opencode/plan/lean-remaining-math-2026-11-24.md):
 *   *_fast  : the original ~1e-6 relative polynomials. FROZEN bit-for-bit;
 *             the core color/ACES and tocio codegen outputs depend on them.
 *   *       : accurate tier. `log2f`/`exp2f`/`logf`/`powf` use binary64
 *             intermediates and round once to binary32; `expf` already uses a
 *             binary64 range reduction. Target: correctly rounded (0 ULP) on
 *             the practical TIR/texcomp/tocio domains.
 *   *_exact : integer-exact IEEE binary32/binary64 square root.
 *
 * No <math.h>, no libm, no libc allocator. All bit casts use unions (C11).
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#ifndef TINYEXR_MATH_IMPL_H_
#define TINYEXR_MATH_IMPL_H_

#include <stddef.h>
#include <stdint.h>

/* ---- bit casts and constants --------------------------------------------- */

static inline float exr_math_i_b2f32(uint32_t u) {
    union { uint32_t u; float f; } v;
    v.u = u;
    return v.f;
}
static inline uint32_t exr_math_i_f2b32(float f) {
    union { float f; uint32_t u; } v;
    v.f = f;
    return v.u;
}
static inline double exr_math_i_b2f64(uint64_t u) {
    union { uint64_t u; double d; } v;
    v.u = u;
    return v.d;
}
static inline uint64_t exr_math_i_f2b64(double d) {
    union { double d; uint64_t u; } v;
    v.d = d;
    return v.u;
}

#define EXR_MATH_I_INF_POS_F (exr_math_i_b2f32(0x7f800000u))
#define EXR_MATH_I_INF_NEG_F (exr_math_i_b2f32(0xff800000u))
#define EXR_MATH_I_NAN_F     (exr_math_i_b2f32(0x7fc00000u))
#define EXR_MATH_I_LN2_F     0.6931471805599453f
#define EXR_MATH_I_LOG2E_F   1.4426950408889634f
#define EXR_MATH_I_LN2_D     0.693147180559945309417232121458
#define EXR_MATH_I_LOG2E_D   1.44269504088896340736

static inline double exr_math_i_exp64(double x);
static inline double exr_math_i_sqrt64(double x);

/* Binary64 log2 with mantissa reduction to [sqrt(1/2), sqrt(2)] and the
 * atanh series through t^27. Used only by the accurate f32 wrappers, which
 * round once at the end. */
static inline double exr_math_i_log2_64(double x) {
    uint64_t u = exr_math_i_f2b64(x);
    int e = (int)((u >> 52) & 0x7ffu) - 1023;
    double m, t, t2, p;
    if (e == -1023) {
        int sh = 0;
        uint64_t mnt = u & UINT64_C(0x000fffffffffffff);
        while (!(mnt & UINT64_C(0x0010000000000000))) { mnt <<= 1; ++sh; }
        m = exr_math_i_b2f64(UINT64_C(0x3ff0000000000000) |
                             (mnt & UINT64_C(0x000fffffffffffff)));
        e = -1022 - sh;
    } else {
        m = exr_math_i_b2f64(UINT64_C(0x3ff0000000000000) |
                             (u & UINT64_C(0x000fffffffffffff)));
    }
    if (m > 1.4142135623730951) { m *= 0.5; ++e; }
    t = (m - 1.0) / (m + 1.0);
    t2 = t * t;
    /* 2/(ln2*(2k+1)), k = 13..0 */
    p = 0.1068662993251084;
    p = 0.11541560327111706 + t2 * p;
    p = 0.12545174268599682 + t2 * p;
    p = 0.1373995277037108 + t2 * p;
    p = 0.15186263588304877 + t2 * p;
    p = 0.16972882833987804 + t2 * p;
    p = 0.19235933878519512 + t2 * p;
    p = 0.2219530832136867 + t2 * p;
    p = 0.2623081892525388 + t2 * p;
    p = 0.3205988979753252 + t2 * p;
    p = 0.41219858311113244 + t2 * p;
    p = 0.5770780163555853 + t2 * p;
    p = 0.9617966939259757 + t2 * p;
    p = 2.8853900817779268 + t2 * p;
    return (double)e + t * p;
}

/* =========================================================================
 * FROZEN FAST TIER (core exr_util_* / tocio toc_* op order, unchanged)
 * ========================================================================= */

static inline float exr_math_i_log2f_fast(float x) {
    union { float f; uint32_t u; } v;
    int e;
    float m, t, t2, ln;
    if (!(x > 0.0f)) return x < 0.0f ? EXR_MATH_I_NAN_F : EXR_MATH_I_INF_NEG_F;
    v.f = x;
    e = (int)((v.u >> 23) & 0xffu) - 127;
    v.u = (v.u & 0x007fffffu) | 0x3f800000u;
    m = v.f;
    t = (m - 1.0f) / (m + 1.0f);
    t2 = t * t;
    ln = 2.0f * t *
         (1.0f + t2 * (1.0f / 3.0f +
                       t2 * (1.0f / 5.0f +
                             t2 * (1.0f / 7.0f + t2 * (1.0f / 9.0f)))));
    return (float)e + ln * EXR_MATH_I_LOG2E_F;
}

static inline float exr_math_i_exp2f_fast(float x) {
    union { uint32_t u; float f; } v;
    float k, f, g, p;
    int ki;
    if (x > 127.0f) return EXR_MATH_I_INF_POS_F;
    if (x < -126.0f) return 0.0f;
    k = (x >= 0.0f) ? (float)(int)(x + 0.5f) : (float)(int)(x - 0.5f);
    f = x - k;
    g = f * EXR_MATH_I_LN2_F;
    p = 1.0f + g * (1.0f + g * (0.5f + g * (1.0f / 6.0f +
        g * (1.0f / 24.0f + g * (1.0f / 120.0f + g * (1.0f / 720.0f))))));
    ki = (int)k;
    v.u = (uint32_t)((ki + 127) << 23);
    return p * v.f;
}

static inline float exr_math_i_powf_fast(float x, float y) {
    if (!(x > 0.0f)) {
        if (x == 0.0f)
            return (y > 0.0f) ? 0.0f : (y == 0.0f ? 1.0f : EXR_MATH_I_INF_POS_F);
        return EXR_MATH_I_NAN_F;
    }
    return exr_math_i_exp2f_fast(y * exr_math_i_log2f_fast(x));
}

static inline float exr_math_i_sqrtf_fast(float x) {
    if (!(x > 0.0f)) return 0.0f;
    return exr_math_i_exp2f_fast(0.5f * exr_math_i_log2f_fast(x));
}

/* =========================================================================
 * ACCURATE TIER -- binary64 intermediates, one final binary32 rounding.
 * Mirrored by lean/Math/F32.lean (compiled `Float` ops, same order).
 * ========================================================================= */

static inline float exr_math_i_log2f(float x) {
    uint32_t u;
    if (x != x) return x;
    if (!(x > 0.0f)) return x < 0.0f ? EXR_MATH_I_NAN_F : EXR_MATH_I_INF_NEG_F;
    u = exr_math_i_f2b32(x);
    if (((u >> 23) & 0xffu) == 0xffu) return EXR_MATH_I_INF_POS_F;
    return (float)exr_math_i_log2_64((double)x);
}

/* exp2f: evaluate exp(x*ln2) in binary64 and round once. */
static inline float exr_math_i_exp2f(float x) {
    if (x != x) return x;
    if (x >= 128.0f) return EXR_MATH_I_INF_POS_F;
    if (x < -150.0f) return 0.0f;
    return (float)exr_math_i_exp64((double)x * EXR_MATH_I_LN2_D);
}

static inline float exr_math_i_logf(float x) {
    uint32_t u;
    if (x != x) return x;
    if (!(x > 0.0f)) return x < 0.0f ? EXR_MATH_I_NAN_F : EXR_MATH_I_INF_NEG_F;
    u = exr_math_i_f2b32(x);
    if (((u >> 23) & 0xffu) == 0xffu) return EXR_MATH_I_INF_POS_F;
    return (float)(exr_math_i_log2_64((double)x) * EXR_MATH_I_LN2_D);
}
static inline double exr_math_i_exp_poly(double r);
static inline double exr_math_i_floor64(double x);

/*
 * expf needs a double-precision range reduction: the f32 product x*log2e
 * alone loses ~40 ULP near x=88. We still return binary32 and the Lean model
 * can mirror the double ops (`Float.toFloat32` / `Float32.toFloat`).
 */
static inline float exr_math_i_expf(float x) {
    const double ln2_hi = 6.93147180369123816490e-01;
    const double ln2_lo = 1.90821492927058770002e-10;
    double d, kd, r, p, scale;
    int k;
    uint64_t bits;
    if (x != x) return x;
    if (x > 88.72283f) return EXR_MATH_I_INF_POS_F;
    if (x < -103.97208f) return 0.0f;
    d = (double)x;
    kd = exr_math_i_floor64(d * 1.44269504088896340736 + 0.5);
    k = (int)kd;
    r = d - kd * ln2_hi;
    r -= kd * ln2_lo;
    p = exr_math_i_exp_poly(r);
    if (k >= -1022) bits = (uint64_t)(k + 1023) << 52;
    else bits = (uint64_t)(k + 1075) << 52;
    scale = exr_math_i_b2f64(bits);
    if (k < -1022) scale *= 0x1p-52;
    return (float)(p * scale);
}
static inline double exr_math_i_powi_64(double x, int n) {
    int m = n < 0 ? -n : n;
    double b = x, r = 1.0;
    while (m) {
        if (m & 1) r *= b;
        b *= b;
        m >>= 1;
    }
    return n < 0 ? 1.0 / r : r;
}

static inline float exr_math_i_powf(float x, float y) {
    int iy = 0;
    int yint = 0;
    if (y == 0.0f) return 1.0f;
    if (y == 1.0f) return x;
    if (x == 1.0f) return 1.0f;
    if (y != y) return y;
    if (y >= -8.0f && y <= 8.0f) {
        iy = (int)y;
        yint = ((float)iy == y);
    }
    if (!(x > 0.0f)) {
        if (x == 0.0f)
            return (y > 0.0f) ? 0.0f : EXR_MATH_I_INF_POS_F;
        if (yint) return (float)exr_math_i_powi_64((double)x, iy);
        return EXR_MATH_I_NAN_F;
    }
    if (((exr_math_i_f2b32(x) >> 23) & 0xffu) == 0xffu)
        return (y > 0.0f) ? EXR_MATH_I_INF_POS_F : 0.0f;
    if (yint) return (float)exr_math_i_powi_64((double)x, iy);
    if (y == 1.5f) return (float)((double)x * exr_math_i_sqrt64((double)x));
    {
        double t = (double)y * exr_math_i_log2_64((double)x);
        if (t >= 128.0) return EXR_MATH_I_INF_POS_F;
        if (t < -150.0) return 0.0f;
        return (float)exr_math_i_exp64(t * EXR_MATH_I_LN2_D);
    }
}
static inline float exr_math_i_sqrtf(float x) {
    if (x != x) return x;
    if (!(x > 0.0f)) return x < 0.0f ? EXR_MATH_I_NAN_F : 0.0f;
    return exr_math_i_exp2f(0.5f * exr_math_i_log2f(x));
}

/* ---- integer-exact binary32 square root (from toc_sqrtf_exact) ----------- */

static inline uint64_t exr_math_i_isqrt64(uint64_t n) {
    uint64_t res = 0, bit = (uint64_t)1 << 62;
    while (bit > n) bit >>= 2;
    while (bit) {
        if (n >= res + bit) { n -= res + bit; res = (res >> 1) + bit; }
        else { res >>= 1; }
        bit >>= 2;
    }
    return res;
}

static inline float exr_math_i_sqrtf_exact(float x) {
    uint32_t sign, expo, mant;
    uint64_t M, A, N, S, hi, round_bit, sticky;
    int s, t, d, e;
    uint32_t u = exr_math_i_f2b32(x);
    sign = u >> 31;
    expo = (u >> 23) & 0xffu;
    mant = u & 0x7fffffu;
    if (expo == 255u) {
        if (mant) return exr_math_i_b2f32(u | 0x00400000u);
        if (sign) return EXR_MATH_I_NAN_F;
        return x;
    }
    if (u == 0u || u == 0x80000000u) return x;
    if (sign) return EXR_MATH_I_NAN_F;
    if (expo == 0u) {
        int lz = 0;
        while (!(mant & 0x00800000u)) { mant <<= 1; ++lz; }
        M = mant;
        s = -149 - lz;
    } else {
        M = mant | 0x00800000u;
        s = (int)expo - 127 - 23;
    }
    if (s & 1) { A = M << 1; t = (s - 1) / 2; }
    else { A = M; t = s / 2; }
    N = A << 38; /* A < 2^25 -> N < 2^63 */
    S = exr_math_i_isqrt64(N);
    d = 0;
    { uint64_t tmp = S; while (tmp >>= 1) ++d; }
    d -= 23;
    hi = S >> d;
    round_bit = (S >> (uint32_t)(d - 1)) & 1u;
    sticky = ((S & ((((uint64_t)1) << (uint32_t)(d - 1)) - 1u)) != 0u) ||
             (S * S != N);
    if (round_bit && (sticky || (hi & 1u))) ++hi;
    e = d + t + 4;
    if (hi == (((uint64_t)1) << 24)) { hi >>= 1; ++e; }
    return exr_math_i_b2f32(((uint32_t)(e + 127) << 23) |
                            ((uint32_t)hi & 0x7fffffu));
}

/* =========================================================================
 * F64 HELPERS for the tir table builder (build time only, no Lean model).
 * Domains actually used: sinc x in [0,3*pi], gaussian exponent in [-4.5,0],
 * kaiser sqrt argument in [0,1], floor/ceil on axis centers.
 * ========================================================================= */

#define EXR_MATH_I_PI        3.14159265358979323846
#define EXR_MATH_I_PIO2_HI   1.570796326794896558e+00
#define EXR_MATH_I_PIO2_LO   6.123233995736766036e-17
#define EXR_MATH_I_2OPI      0.63661977236758134308
#define EXR_MATH_I_TWO52     4503599627370496.0

static inline double exr_math_i_fabs64(double x) {
    return exr_math_i_b2f64(exr_math_i_f2b64(x) & UINT64_C(0x7fffffffffffffff));
}

static inline double exr_math_i_floor64(double x) {
    uint64_t u = exr_math_i_f2b64(x);
    uint64_t expo = (u >> 52) & 0x7ffu;
    uint64_t mask;
    int e;
    if (expo == 0x7ffu) return x;              /* inf / NaN */
    e = (int)expo - 1023;
    if (e >= 52) return x;                     /* already integral */
    if (e < 0) return (u >> 63) ? -1.0 : 0.0;  /* |x| < 1 */
    mask = (UINT64_C(1) << (52 - e)) - 1u;
    if (u >> 63) u = (u + mask) & ~mask;       /* toward -inf */
    else u &= ~mask;
    return exr_math_i_b2f64(u);
}
static inline double exr_math_i_ceil64(double x) {
    return -exr_math_i_floor64(-x);
}

/* sin/cos on [-pi/4,pi/4] via Taylor; argument is reduced by pi/2 below. */
static inline double exr_math_i_sin_small(double r) {
    double r2 = r * r, p;
    p = -1.0 / 1307674368000.0;                /* -1/15! */
    p = 1.0 / 6227020800.0 + r2 * p;           /* +1/13! */
    p = -1.0 / 39916800.0 + r2 * p;            /* -1/11! */
    p = 1.0 / 362880.0 + r2 * p;               /* +1/9!  */
    p = -1.0 / 5040.0 + r2 * p;                /* -1/7!  */
    p = 1.0 / 120.0 + r2 * p;                  /* +1/5!  */
    p = -1.0 / 6.0 + r2 * p;                   /* -1/3!  */
    return r + r * r2 * p;
}
static inline double exr_math_i_cos_small(double r) {
    double r2 = r * r, p;
    p = -1.0 / 87178291200.0;                  /* -1/14! */
    p = 1.0 / 479001600.0 + r2 * p;            /* +1/12! */
    p = -1.0 / 3628800.0 + r2 * p;             /* -1/10! */
    p = 1.0 / 40320.0 + r2 * p;                /* +1/8!  */
    p = -1.0 / 720.0 + r2 * p;                 /* -1/6!  */
    p = 1.0 / 24.0 + r2 * p;                   /* +1/4!  */
    p = -0.5 + r2 * p;                         /* -1/2!  */
    return 1.0 + r2 * p;
}

static inline void exr_math_i_sincos64(double x, double *sn, double *cs) {
    double qd, r, s, c;
    int q;
    if (x != x) { *sn = x; *cs = x; return; }
    qd = exr_math_i_floor64(x * EXR_MATH_I_2OPI + 0.5);
    if (qd > 2147483647.0 || qd < -2147483647.0) { *sn = 0.0; *cs = 1.0; return; }
    q = (int)qd;
    /* Cody-Waite reduction: two terms keep r accurate for |x| <= ~1e6. */
    r = x - (double)q * EXR_MATH_I_PIO2_HI;
    r -= (double)q * EXR_MATH_I_PIO2_LO;
    s = exr_math_i_sin_small(r);
    c = exr_math_i_cos_small(r);
    switch (q & 3) {
        case 0: *sn = s;        *cs = c;        break;
        case 1: *sn = c;        *cs = -s;       break;
        case 2: *sn = -s;       *cs = -c;       break;
        default:*sn = -c;       *cs = s;        break;
    }
}
static inline double exr_math_i_sin(double x) {
    double s, c;
    exr_math_i_sincos64(x, &s, &c);
    return s;
}
static inline double exr_math_i_cos(double x) {
    double s, c;
    exr_math_i_sincos64(x, &s, &c);
    return c;
}

/* exp(r) for r in [-ln2/2, ln2/2], degree-16 Taylor. */
static inline double exr_math_i_exp_poly(double r) {
    double p;
    p = 1.0 / 20922789888000.0;                /* 1/16! */
    p = 1.0 / 1307674368000.0 + r * p;         /* 1/15! */
    p = 1.0 / 87178291200.0 + r * p;
    p = 1.0 / 6227020800.0 + r * p;
    p = 1.0 / 479001600.0 + r * p;
    p = 1.0 / 39916800.0 + r * p;
    p = 1.0 / 3628800.0 + r * p;
    p = 1.0 / 362880.0 + r * p;
    p = 1.0 / 40320.0 + r * p;
    p = 1.0 / 5040.0 + r * p;
    p = 1.0 / 720.0 + r * p;
    p = 1.0 / 120.0 + r * p;
    p = 1.0 / 24.0 + r * p;
    p = 1.0 / 6.0 + r * p;
    p = 0.5 + r * p;
    p = 1.0 + r * p;
    return 1.0 + r * p;
}

/* Range reduction x = k*ln2 + r, then the shared Taylor polynomial. */
static inline double exr_math_i_exp64(double x) {
    const double ln2_hi = 6.93147180369123816490e-01;
    const double ln2_lo = 1.90821492927058770002e-10;
    double kd, r, p, scale;
    int k;
    uint64_t bits;
    if (x != x) return x;
    if (x > 709.0) return exr_math_i_b2f64(UINT64_C(0x7ff0000000000000));
    if (x < -745.0) return 0.0;
    kd = exr_math_i_floor64(x * 1.44269504088896340736 + 0.5);
    if (kd > 1023.0 || kd < -1074.0) return x > 0.0 ? 1e308 : 0.0;
    k = (int)kd;
    r = x - (double)k * ln2_hi;
    r -= (double)k * ln2_lo;
    p = exr_math_i_exp_poly(r);
    if (k >= -1022) bits = (uint64_t)(k + 1023) << 52;
    else bits = (uint64_t)(k + 1075) << 52;     /* subnormal scale */
    scale = exr_math_i_b2f64(bits);
    if (k < -1022) scale *= 0x1p-52;
    return p * scale;
}

/* Newton sqrt with a bit-pattern seed; six iterations are ample for the
 * tir table domain. Special values match IEEE expectations. */
static inline double exr_math_i_sqrt64(double x) {
    double r;
    uint64_t u;
    int i;
    if (x != x) return x;
    if (x == 0.0) return x;
    if (x < 0.0) return exr_math_i_b2f64(UINT64_C(0x7ff8000000000000));
    if (x > 1e308) return x;                     /* +inf */
    u = exr_math_i_f2b64(x);
    u = (u >> 1) + UINT64_C(0x1ff8000000000000);
    r = exr_math_i_b2f64(u);
    for (i = 0; i < 6; ++i) r = 0.5 * (r + x / r);
    return r;
}

#endif /* TINYEXR_MATH_IMPL_H_ */
