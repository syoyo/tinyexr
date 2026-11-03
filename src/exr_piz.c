/*
 * TinyEXR - PIZ codec (wavelet + Huffman + range LUT).
 *
 * Pure-C11 port of OpenEXR's PIZ decoder (wav2 inverse lifting, canonical
 * Huffman with RLE, and the bitmap range LUT). Large tables are heap-allocated
 * to keep stack usage small and thread-safe.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr_internal.h"

#define PIZ_BITMAP_SIZE 8192
#define PIZ_USHORT_RANGE 65536
#define PIZ_HUF_ENCSIZE (PIZ_USHORT_RANGE + 1) /* 65537 */

#define HUF_DECBITS 12
#define HUF_DECSIZE (1 << HUF_DECBITS)
#define HUF_DECMASK (HUF_DECSIZE - 1)
#if defined(__GNUC__) && !defined(__clang__)
#define PIZ_OPT_O3 __attribute__((optimize("O3")))
#else
#define PIZ_OPT_O3
#endif
#define SHORT_ZEROCODE_RUN 59
#define LONG_ZEROCODE_RUN 63
#define SHORTEST_LONG_RUN (2 + LONG_ZEROCODE_RUN - SHORT_ZEROCODE_RUN)

typedef struct {
    uint32_t *p;  /* long-code symbol list */
    uint32_t lit; /* short: symbol; long: count */
} HufDec;

typedef struct {
    uint16_t *start;
    int nx, ny, size;
} PizChan;

typedef struct {
    int64_t *hcode;
    uint8_t *lengths;
    uint32_t *symbols;
    size_t symbols_capacity;
    uint32_t *fast;
    HufDec *longdec;
    uint32_t *counts;
    uint32_t *long_storage;
    size_t long_capacity;
    uint32_t *ids;
    size_t ids_capacity;
    uint16_t *rev_lut;
    uint16_t *tmp;
    size_t tmp_capacity;
    PizChan *channels;
    size_t channels_capacity;
    int *emitted;
    size_t emitted_capacity;
    uint8_t *bitmap;
    uint16_t bitmap_max;
    int bitmap_valid;
} PizHufWorkspace;

void exr_piz_context_free(exr_context *ctx) {
    PizHufWorkspace *w;
    const exr_allocator *a;
    void **slot;
    if (!ctx) return;
    slot = exr_context_piz_slot(ctx);
    w = slot ? (PizHufWorkspace *)*slot : NULL;
    if (!w) return;
    a = exr_context_allocator(ctx);
    exr_free(a, w->long_storage);
    exr_free(a, w->ids);
    exr_free(a, w->emitted);
    exr_free(a, w->channels);
    exr_free(a, w->tmp);
    exr_free(a, w->rev_lut);
    exr_free(a, w->bitmap);
    exr_free(a, w->counts);
    exr_free(a, w->longdec);
    exr_free(a, w->fast);
    exr_free(a, w->hcode);
    exr_free(a, w->lengths);
    exr_free(a, w->symbols);
    exr_free(a, w);
    *slot = NULL;
}

/* ---- range LUT ------------------------------------------------------------ */

static PIZ_OPT_O3 uint16_t reverse_lut_from_bitmap(const uint8_t *bitmap,
                                                   uint16_t *lut) {
    int k = 1, i;
    lut[0] = 0;
    for (i = 0; i < PIZ_BITMAP_SIZE; ++i) {
        unsigned bits = bitmap[i];
        if (i == 0) bits &= ~1u; /* value zero is always emitted above */
        while (bits != 0) {
#if defined(__GNUC__) || defined(__clang__)
            unsigned bit = (unsigned)__builtin_ctz(bits);
#else
            unsigned bit = 0;
            while (((bits >> bit) & 1u) == 0) ++bit;
#endif
            lut[k++] = (uint16_t)((i << 3) + (int)bit);
            bits &= bits - 1u;
        }
    }
    {
        uint16_t n = (uint16_t)(k - 1);
        while (k < PIZ_USHORT_RANGE) lut[k++] = 0;
        return n;
    }
}

static PIZ_OPT_O3 void apply_lut(const uint16_t *restrict lut,
                                 uint16_t *restrict data, size_t n) {
    while (n >= 8) {
        data[0] = lut[data[0]];
        data[1] = lut[data[1]];
        data[2] = lut[data[2]];
        data[3] = lut[data[3]];
        data[4] = lut[data[4]];
        data[5] = lut[data[5]];
        data[6] = lut[data[6]];
        data[7] = lut[data[7]];
        data += 8;
        n -= 8;
    }
    for (size_t i = 0; i < n; ++i) data[i] = lut[data[i]];
}

/* ---- inverse wavelet (faithful port of OpenEXR wdec14/wdec16/wav2Decode) -- */

#define WAV_NBITS 16
#define WAV_A_OFFSET (1 << (WAV_NBITS - 1))
#define WAV_MOD_MASK ((1 << WAV_NBITS) - 1)

static void wdec14(uint16_t l, uint16_t h, uint16_t *a, uint16_t *b) {
    int hi = (int16_t)h;
    int ai = (int16_t)l + (hi & 1) + (hi >> 1);
    *a = (uint16_t)ai;
    *b = (uint16_t)(ai - hi);
}

static void wdec16(uint16_t l, uint16_t h, uint16_t *a, uint16_t *b) {
    int m = l, d = h;
    int bb = (m - (d >> 1)) & WAV_MOD_MASK;
    int aa = (d + bb - WAV_A_OFFSET) & WAV_MOD_MASK;
    *b = (uint16_t)bb;
    *a = (uint16_t)aa;
}

static void wdec16_4(uint16_t *px, uint16_t *p01, uint16_t *p10,
                     uint16_t *p11) {
    int a0, b0, a1, b1;
    int x0 = (int)*px;
    int x1 = (int)*p01;
    int y0 = (int)*p10;
    int y1 = (int)*p11;

    b0 = (x0 - (y0 >> 1)) & WAV_MOD_MASK;
    a0 = (y0 + b0 - WAV_A_OFFSET) & WAV_MOD_MASK;
    b1 = (x1 - (y1 >> 1)) & WAV_MOD_MASK;
    a1 = (y1 + b1 - WAV_A_OFFSET) & WAV_MOD_MASK;
    x0 = (a0 - (a1 >> 1)) & WAV_MOD_MASK;
    x1 = (a1 + x0 - WAV_A_OFFSET) & WAV_MOD_MASK;
    y0 = (b0 - (b1 >> 1)) & WAV_MOD_MASK;
    y1 = (b1 + y0 - WAV_A_OFFSET) & WAV_MOD_MASK;

    *px = (uint16_t)x1;
    *p01 = (uint16_t)x0;
    *p10 = (uint16_t)y1;
    *p11 = (uint16_t)y0;
}

static void wdec14_4(uint16_t *px, uint16_t *p01, uint16_t *p10,
                     uint16_t *p11) {
    int ai = (int)(int16_t)*px;
    int bi = (int)(int16_t)*p10;
    int ci = (int)(int16_t)*p01;
    int di = (int)(int16_t)*p11;
    int i00 = ai + (bi & 1) + (bi >> 1);
    int i10 = i00 - bi;
    int i01 = ci + (di & 1) + (di >> 1);
    int i11 = i01 - di;

    ai = i00 + (i01 & 1) + (i01 >> 1);
    bi = ai - i01;
    ci = i10 + (i11 & 1) + (i11 >> 1);
    di = ci - i11;
    *px = (uint16_t)ai;
    *p01 = (uint16_t)bi;
    *p10 = (uint16_t)ci;
    *p11 = (uint16_t)di;
}

static PIZ_OPT_O3 void wav2_decode(uint16_t *in, int nx, int ox, int ny,
                                   int oy, uint16_t mx) {
    int w14 = (mx < (1 << 14));
    int n = (nx > ny) ? ny : nx;
    int p = 1, p2;
    uint16_t i00;

    while (p <= n) p <<= 1;
    p >>= 1;
    p2 = p;
    p >>= 1;

    while (p >= 1) {
        uint16_t *py = in;
        uint16_t *ey = in + oy * (ny - p2);
        int oy1 = oy * p, oy2 = oy * p2, ox1 = ox * p, ox2 = ox * p2;

        for (; py <= ey; py += oy2) {
            uint16_t *px = py;
            uint16_t *ex = py + ox * (nx - p2);
            for (; px <= ex; px += ox2) {
                uint16_t *p01 = px + ox1;
                uint16_t *p10 = px + oy1;
                uint16_t *p11 = p10 + ox1;
                if (w14) {
                    wdec14_4(px, p01, p10, p11);
                } else {
                    wdec16_4(px, p01, p10, p11);
                }
            }
            if (nx & p) {
                uint16_t *p10 = px + oy1;
                if (w14)
                    wdec14(*px, *p10, &i00, p10);
                else
                    wdec16(*px, *p10, &i00, p10);
                *px = i00;
            }
        }
        if (ny & p) {
            uint16_t *px = py;
            uint16_t *ex = py + ox * (nx - p2);
            for (; px <= ex; px += ox2) {
                uint16_t *p01 = px + ox1;
                if (w14)
                    wdec14(*px, *p01, &i00, p01);
                else
                    wdec16(*px, *p01, &i00, p01);
                *px = i00;
            }
        }
        p2 = p;
        p >>= 1;
    }
}

/* ---- Huffman -------------------------------------------------------------- */

static void hgetchar(uint64_t *c, int *lc, const uint8_t **in) {
    *c = (*c << 8) | (uint64_t)(**in);
    (*in)++;
    *lc += 8;
}
static void hrefill(uint64_t *c, int *lc, const uint8_t **in, const uint8_t *e) {
    while (*lc <= 48 && *in < e) {
        *c = (*c << 8) | (uint64_t)(**in);
        (*in)++;
        *lc += 8;
    }
}
/* Bounds-aware bit reader: refills from [*in, end) and zero-fills once the
 * input is exhausted, so a crafted Huffman table cannot read past `end`. */
static uint64_t hgetbits(int nb, uint64_t *c, int *lc, const uint8_t **in,
                         const uint8_t *end) {
    while (*lc < nb) {
        if (*in < end) {
            *c = (*c << 8) | (uint64_t)(**in);
            (*in)++;
        } else {
            *c = (*c << 8); /* zero-fill past the end */
        }
        *lc += 8;
    }
    *lc -= nb;
    return (*c >> *lc) & ((UINT64_C(1) << nb) - 1u);
}

/* Only hcode[im..iM] can be non-zero (symbols outside that span have length 0);
 * the length-0 count n[0] is never used, so collecting non-zero symbols while
 * unpacking avoids walking all 65537 slots again during table construction. */
static void canonical_code_table(const uint8_t *lengths, int64_t *hcode,
                                 const uint32_t *symbols, size_t symbol_count) {
    int64_t n[59];
    size_t j;
    int i;
    int64_t c = 0;
    for (i = 0; i <= 58; ++i) n[i] = 0;
    for (j = 0; j < symbol_count; ++j)
        n[lengths[symbols[j]]]++;
    for (i = 58; i > 0; --i) {
        int64_t nc = ((c + n[i]) >> 1);
        n[i] = c;
        c = nc;
    }
    for (j = 0; j < symbol_count; ++j) {
        int symbol = (int)symbols[j];
        int l = (int)lengths[symbol];
        hcode[symbol] = l | (n[l]++ << 6);
    }
}

static void canonical_code_table64(int64_t *hcode, int im, int iM) {
    int64_t n[59];
    int i;
    int64_t c = 0;
    for (i = 0; i <= 58; ++i) n[i] = 0;
    for (i = im; i <= iM; ++i) n[hcode[i]]++;
    for (i = 58; i > 0; --i) {
        int64_t nc = ((c + n[i]) >> 1);
        n[i] = c;
        c = nc;
    }
    for (i = im; i <= iM; ++i) {
        int l = (int)hcode[i];
        if (l > 0) hcode[i] = l | (n[l]++ << 6);
    }
}

static int unpack_enc_table(const uint8_t **pcode, int ni, int im, int iM,
                            uint8_t *lengths, int64_t *hcode,
                            uint32_t *symbols, size_t symbols_capacity,
                            size_t *symbol_count) {
    const uint8_t *p = *pcode;
    const uint8_t *end = *pcode + ni;
    uint64_t c = 0;
    int lc = 0;
    size_t n_symbols = 0;
    memset(lengths + im, 0, (size_t)(iM - im + 1));
    for (; im <= iM; im++) {
        int64_t l;
        if (p - *pcode >= ni) return 0;
        l = (int64_t)hgetbits(6, &c, &lc, &p, end);
        if (l == (int64_t)LONG_ZEROCODE_RUN) {
            int zerun;
            if (p - *pcode > ni) return 0;
            zerun = (int)hgetbits(8, &c, &lc, &p, end) + SHORTEST_LONG_RUN;
            if (im + zerun > iM + 1) return 0;
            im += zerun - 1;
        } else if (l >= (int64_t)SHORT_ZEROCODE_RUN) {
            int zerun = (int)(l - SHORT_ZEROCODE_RUN + 2);
            if (im + zerun > iM + 1) return 0;
            im += zerun - 1;
        } else {
            if (l != 0) {
                if (n_symbols >= symbols_capacity) return 0;
                symbols[n_symbols++] = (uint32_t)im;
            }
            lengths[im] = (uint8_t)l;
        }
    }
    *pcode = p;
    *symbol_count = n_symbols;
    canonical_code_table(lengths, hcode, symbols, n_symbols);
    return 1;
}

static int build_dec_table(const exr_allocator *a, const int64_t *hcode,
                           uint32_t *fast, HufDec *longdec, uint32_t *counts,
                           uint32_t **long_storage, size_t *long_capacity,
                           const uint32_t *symbols, size_t symbol_count) {
    size_t total_long = 0;
    size_t j;
    int i;

    memset(counts, 0, HUF_DECSIZE * sizeof(*counts));
    memset(fast, 0, HUF_DECSIZE * sizeof(*fast));
    for (i = 0; i < HUF_DECSIZE; ++i) {
        longdec[i].lit = 0;
        longdec[i].p = NULL;
    }
    for (j = 0; j < symbol_count; ++j) {
        i = (int)symbols[j];
        uint64_t code_val = ((uint64_t)hcode[i]) >> 6;
        int l = (int)(hcode[i] & 63);
        if (l == 0) continue;
        if (code_val >> l) return 0;
        if (l > HUF_DECBITS) {
            size_t base = (size_t)(code_val >> (l - HUF_DECBITS));
            if (fast[base] || longdec[base].p) return 0;
            counts[base]++;
        } else {
            size_t base = (size_t)(code_val << (HUF_DECBITS - l));
            size_t fill = (size_t)1u << (HUF_DECBITS - l), k;
            for (k = 0; k < fill; ++k) {
                if (counts[base + k] != 0 || fast[base + k] ||
                    longdec[base + k].p) {
                    return 0;
                }
                fast[base + k] = ((uint32_t)i << 6) | (uint32_t)l;
            }
        }
    }
    for (i = 0; i < HUF_DECSIZE; ++i) {
        if (total_long > SIZE_MAX - counts[i]) return 0;
        total_long += counts[i];
    }
    if (total_long > *long_capacity) {
        size_t bytes;
        uint32_t *storage;
        if (exr_mul_ovf(total_long, sizeof(*storage), &bytes)) return 0;
        exr_free(a, *long_storage);
        storage = (uint32_t *)exr_malloc(a, bytes);
        if (!storage) {
            *long_storage = NULL;
            *long_capacity = 0;
            return -1;
        }
        *long_storage = storage;
        *long_capacity = total_long;
    }
    if (total_long > 0) {
        uint32_t *storage = *long_storage;
        for (i = 0; i < HUF_DECSIZE; ++i) {
            if (counts[i] != 0) {
                longdec[i].p = storage;
                longdec[i].lit = counts[i];
                storage += counts[i];
                counts[i] = 0;
            }
        }
    }
    for (j = 0; j < symbol_count; ++j) {
        int sym = (int)symbols[j];
        uint64_t code_val = ((uint64_t)hcode[sym]) >> 6;
        int l = (int)(hcode[sym] & 63);
        if (l > HUF_DECBITS) {
            size_t base = (size_t)(code_val >> (l - HUF_DECBITS));
            longdec[base].p[counts[base]++] = (uint32_t)sym;
        }
    }
    return 1;
}

static int get_code(int po, int rlc, uint64_t *c, int *lc, const uint8_t **in,
                    const uint8_t *ie, uint16_t **out, const uint16_t *ob,
                    const uint16_t *oe) {
    if (po == rlc) {
        uint8_t cs;
        uint16_t s;
        if (*lc < 8) {
            if (*in >= ie) return 0;
            hgetchar(c, lc, in);
        }
        *lc -= 8;
        cs = (uint8_t)((*c >> *lc) & 0xffu);
        if (*out + cs > oe) return 0;
        if ((*out - 1) < ob) return 0;
        s = (*out)[-1];
        while (cs-- > 0) *(*out)++ = s;
    } else if (*out < oe) {
        *(*out)++ = (uint16_t)po;
    } else {
        return 0;
    }
    return 1;
}

static uint64_t piz_read64be(const uint8_t *p) {
    return ((uint64_t)p[0] << 56) | ((uint64_t)p[1] << 48) |
           ((uint64_t)p[2] << 40) | ((uint64_t)p[3] << 32) |
           ((uint64_t)p[4] << 24) | ((uint64_t)p[5] << 16) |
           ((uint64_t)p[6] << 8) | (uint64_t)p[7];
}

/* Refill the OpenEXR-style two-window reader. `bits_left` counts source bits
 * not yet copied into the refill window; the final partial byte is zero-padded
 * and never read past `end`. */
static PIZ_OPT_O3 inline void piz_fast_refill(
    uint64_t *buffer, int num_bits, uint64_t *buffer_back, int *back_bits,
    const uint8_t **cur, int *bits_left, const uint8_t *end) {
    int need = num_bits;
    int consume = num_bits;
    *buffer |= *buffer_back >> (64 - num_bits);
    if (*back_bits < num_bits) {
        need = num_bits - *back_bits;
        consume = need;
        int read_bits = *bits_left;
        uint64_t next = 0;
        if (read_bits >= 64) {
            next = piz_read64be(*cur);
            *cur += 8;
            *bits_left -= 64;
        } else {
            int bytes = (read_bits + 7) / 8;
            int i;
            if (bytes > (int)(end - *cur))
                bytes = (int)(end - *cur);
            for (i = 0; i < bytes && *cur < end; ++i)
                next |= (uint64_t)*(*cur)++ << (56 - i * 8);
            *bits_left = 0;
        }
        *buffer_back = next;
        *back_bits = 64;
        *buffer |= *buffer_back >> (64 - need);
    }
    if (*back_bits <= consume) {
        *buffer_back = 0;
    } else {
        *buffer_back <<= consume;
    }
    *back_bits -= consume;
}

static PIZ_OPT_O3 int piz_fast_huf_decode(
    const uint8_t *src, size_t src_len, int nbits, const uint32_t *fast,
    const uint32_t *ids, size_t symbol_count, const uint64_t *ljbase,
    const uint64_t *ljoffset, uint64_t table_min, int max_len, uint32_t rlc,
    uint16_t *dst, size_t dst_len) {
    const uint8_t *cur, *end = src + src_len;
    uint64_t buffer, buffer_back;
    int buffer_bits = 64, back_bits = 64;
    int bits_left = nbits - 128;
    size_t out = 0;

    if (nbits < 128 || src_len < 16) return 0;
    cur = src + 16;
    buffer = piz_read64be(src);
    buffer_back = piz_read64be(src + 8);
    while (out < dst_len) {
        uint32_t packed;
        uint32_t symbol;
        int code_len;
        packed = buffer >= table_min ? fast[buffer >> (64 - HUF_DECBITS)] : 0;
        if (packed != 0) {
            code_len = (int)(packed & 63u);
            symbol = packed >> 6;
        } else {
            uint64_t id;
            if (buffer_bits < 64) {
                piz_fast_refill(&buffer, 64 - buffer_bits, &buffer_back,
                                &back_bits, &cur, &bits_left, end);
                buffer_bits = 64;
            }
            code_len = HUF_DECBITS + 1;
            while (code_len <= max_len && buffer < ljbase[code_len])
                ++code_len;
            if (code_len > max_len) return 0;
            id = ljoffset[code_len] + (buffer >> (64 - code_len));
            if (id >= symbol_count) return 0;
            symbol = ids[id];
        }
        if (code_len <= 0 || code_len > buffer_bits) return 0;
        buffer <<= code_len;
        buffer_bits -= code_len;
        if (symbol == (uint32_t)rlc) {
            uint32_t count;
            if (buffer_bits < 8) {
                piz_fast_refill(&buffer, 64 - buffer_bits, &buffer_back,
                                &back_bits, &cur, &bits_left, end);
                buffer_bits = 64;
            }
            count = (uint32_t)(buffer >> 56);
            if (count == 0 || out == 0 || count > dst_len - out) return 0;
            while (count-- != 0) {
                dst[out] = dst[out - 1];
                ++out;
            }
            buffer <<= 8;
            buffer_bits -= 8;
        } else {
            if (symbol > UINT16_MAX || out >= dst_len) return 0;
            dst[out++] = (uint16_t)symbol;
        }
        if (buffer_bits < HUF_DECBITS) {
            piz_fast_refill(&buffer, 64 - buffer_bits, &buffer_back,
                            &back_bits, &cur, &bits_left, end);
            buffer_bits = 64;
        }
    }
    return bits_left == 0;
}

static int piz_build_fast_table(const int64_t *hcode, const uint32_t *symbols,
                                size_t symbol_count, uint32_t *fast) {
    memset(fast, 0, sizeof(*fast) * HUF_DECSIZE);
    for (size_t j = 0; j < symbol_count; ++j) {
        int sym = (int)symbols[j];
        int len = (int)(hcode[sym] & 63);
        uint64_t code = (uint64_t)hcode[sym] >> 6;
        if (len <= 0) continue;
        if (code >> len) return 0;
        if (len <= HUF_DECBITS) {
            size_t base = (size_t)(code << (HUF_DECBITS - len));
            size_t fill = (size_t)1u << (HUF_DECBITS - len);
            for (size_t k = 0; k < fill; ++k) {
                if (fast[base + k] != 0) return 0;
                fast[base + k] = ((uint32_t)sym << 6) | (uint32_t)len;
            }
        }
    }
    return 1;
}

static PIZ_OPT_O3 int huf_uncompress(
    const exr_allocator *a, exr_context *context, const uint8_t *in,
    size_t in_len, uint16_t *out, size_t out_len) {
    uint32_t im_val, iM_val, nBits_val;
    int im, iM, nBits, ni, rlc;
    PizHufWorkspace local = {0};
    PizHufWorkspace *w = &local;
    void **slot;
    const uint8_t *ptr, *ie;
    size_t symbol_capacity, symbol_bytes;
    size_t symbol_count = 0;
    uint64_t c = 0;
    int lc = 0;
    uint16_t *outb, *outp, *oe;
    const uint32_t *fast;
    const HufDec *longdec;
    uint64_t ljbase[59], ljoffset[59];
    uint32_t code_count[59], code_write[59], code_pos[59];
    int max_len = 0;
    uint64_t table_min = UINT64_MAX;
    int ret = 0;

    if (out_len == 0) return in_len == 0;
    if (in_len < 20) return 0;
    memcpy(&im_val, in, 4);
    memcpy(&iM_val, in + 4, 4);
    memcpy(&nBits_val, in + 12, 4);
    im = (int)im_val;
    iM = (int)iM_val;
    nBits = (int)nBits_val;
    if (im < 0 || im >= PIZ_HUF_ENCSIZE || iM < 0 || iM >= PIZ_HUF_ENCSIZE ||
        im > iM)
        return 0;

    /* The public context is shared by reader workers. Keep the reusable
     * workspace on the serial path only; threaded decodes use the local
     * workspace below so Huffman tables cannot race between workers. */
    slot = exr_get_num_threads() <= 1 ? exr_context_piz_slot(context) : NULL;
    if (slot) {
        a = exr_context_allocator(context);
        if (!*slot) {
            *slot = exr_calloc(a, 1, sizeof(*w));
            if (!*slot) { ret = -1; goto cleanup; }
        }
        w = (PizHufWorkspace *)*slot;
    }
    if (!w->hcode)
        w->hcode = (int64_t *)exr_malloc(a, sizeof(*w->hcode) * PIZ_HUF_ENCSIZE);
    if (!w->lengths)
        w->lengths = (uint8_t *)exr_malloc(a, sizeof(*w->lengths) * PIZ_HUF_ENCSIZE);
    symbol_capacity = (size_t)(iM - im + 1);
    if (exr_mul_ovf(symbol_capacity, sizeof(*w->symbols), &symbol_bytes))
        goto cleanup;
    if (!w->symbols || w->symbols_capacity < symbol_capacity) {
        uint32_t *p = (uint32_t *)exr_malloc(a, symbol_bytes);
        if (!p) { ret = -1; goto cleanup; }
        exr_free(a, w->symbols);
        w->symbols = p;
        w->symbols_capacity = symbol_capacity;
    }
    if (!w->fast)
        w->fast = (uint32_t *)exr_malloc(a, sizeof(*w->fast) * HUF_DECSIZE);
    if (!w->longdec)
        w->longdec = (HufDec *)exr_malloc(a, sizeof(*w->longdec) * HUF_DECSIZE);
    if (!w->counts)
        w->counts = (uint32_t *)exr_malloc(a, sizeof(*w->counts) * HUF_DECSIZE);
    if (!w->hcode || !w->lengths || !w->symbols || !w->fast ||
        !w->longdec || !w->counts) {
        ret = -1; goto cleanup;
    }

    ptr = in + 20;
    ni = (int)(in_len - 20);
    if (!unpack_enc_table(&ptr, ni, im, iM, w->lengths, w->hcode,
                          w->symbols, w->symbols_capacity, &symbol_count))
        goto cleanup;

    if (!w->ids || w->ids_capacity < symbol_count) {
        uint32_t *p = (uint32_t *)exr_malloc(a, symbol_bytes);
        if (!p) { ret = -1; goto cleanup; }
        exr_free(a, w->ids);
        w->ids = p;
        w->ids_capacity = symbol_capacity;
    }

    memset(code_count, 0, sizeof(code_count));
    for (int l = 0; l <= 58; ++l) ljbase[l] = UINT64_MAX;
    for (size_t j = 0; j < symbol_count; ++j) {
        int sym = (int)w->symbols[j];
        int len = (int)(w->hcode[sym] & 63);
        uint64_t code = (uint64_t)w->hcode[sym] >> 6;
        ++code_count[len];
        if (len > max_len) max_len = len;
        if (code < ljbase[len]) ljbase[len] = code;
    }
    code_write[58] = 0;
    for (int l = 57; l >= 0; --l)
        code_write[l] = code_write[l + 1] + code_count[l + 1];
    memcpy(code_pos, code_write, sizeof(code_pos));
    for (size_t j = 0; j < symbol_count; ++j) {
        int sym = (int)w->symbols[j];
        int len = (int)(w->hcode[sym] & 63);
        w->ids[code_pos[len]++] = (uint32_t)sym;
    }
    for (int l = 0; l <= 58; ++l) {
        if (ljbase[l] != UINT64_MAX) {
            ljoffset[l] = (uint64_t)code_write[l] - ljbase[l];
            ljbase[l] <<= 64 - l;
        } else {
            ljbase[l] = UINT64_MAX;
            ljoffset[l] = 0;
        }
    }
    for (int l = HUF_DECBITS; l > 0; --l) {
        if (ljbase[l] != UINT64_MAX) {
            table_min = ljbase[l];
            break;
        }
    }
    ni = (int)(in_len - (size_t)(ptr - in));
    if (nBits < 0 || nBits > 8 * ni) goto cleanup;
    if (nBits >= 128 &&
        piz_build_fast_table(w->hcode, w->symbols, symbol_count, w->fast) &&
        piz_fast_huf_decode(ptr, in_len - (size_t)(ptr - in), nBits,
                            w->fast, w->ids, symbol_count, ljbase, ljoffset,
                            table_min, max_len, (uint32_t) iM, out, out_len)) {
        ret = 1;
        goto cleanup;
    }

    {
        int built = build_dec_table(a, w->hcode, w->fast, w->longdec,
                                   w->counts, &w->long_storage, &w->long_capacity,
                                   w->symbols, symbol_count);
        if (built <= 0) { ret = built; goto cleanup; }
    }
    /* Keep the read-only decode tables in local pointers for the symbol loop. */
    fast = w->fast;
    longdec = w->longdec;

    rlc = iM;
    outb = out;
    outp = out;
    oe = out + out_len;
    ie = ptr + (nBits + 7) / 8;

    /* The bounded two-window reader is substantially cheaper for ordinary
     * streams. Keep the original reader below as a correctness fallback for
     * unusual or malformed tables. */
    hrefill(&c, &lc, &ptr, ie);

    while (ptr < ie || lc >= HUF_DECBITS) {
        if (lc < HUF_DECBITS && ptr < ie) hrefill(&c, &lc, &ptr, ie);
        while (lc >= HUF_DECBITS) {
            uint32_t code = fast[(c >> (lc - HUF_DECBITS)) & HUF_DECMASK];
            if (code) {
                int lit = (int)(code >> 6);
                lc -= (int)(code & 63u);
                /* Hot path: most symbols are plain literals (not the run-length
                 * code), which get_code() would emit as a single store. Inline
                 * that case to avoid a 9-argument call per decoded symbol; only
                 * the actual RLE marker falls through to get_code(). */
                if (lit != rlc) {
                    if (outp >= oe) goto cleanup;
                    *outp++ = (uint16_t)lit;
                } else {
                    uint8_t cs;
                    uint16_t s;
                    if (lc < 8) {
                        if (ptr >= ie) goto cleanup;
                        hgetchar(&c, &lc, &ptr);
                    }
                    lc -= 8;
                    cs = (uint8_t)((c >> lc) & 0xffu);
                    if (outp <= outb || (size_t)(oe - outp) < (size_t)cs)
                        goto cleanup;
                    s = outp[-1];
                    while (cs-- > 0) *outp++ = s;
                }
            } else {
                uint32_t j;
                const HufDec *pl =
                    &longdec[(c >> (lc - HUF_DECBITS)) & HUF_DECMASK];
                if (!pl->p) goto cleanup;
                for (j = 0; j < pl->lit; ++j) {
                    int l = (int)(w->hcode[pl->p[j]] & 63);
                    while (lc < l && ptr < ie) hgetchar(&c, &lc, &ptr);
                    if (lc >= l) {
                        uint64_t cv = ((uint64_t)w->hcode[pl->p[j]]) >> 6;
                        if (cv == ((c >> (lc - l)) & ((UINT64_C(1) << l) - 1u))) {
                            lc -= l;
                            if (!get_code((int)pl->p[j], rlc, &c, &lc, &ptr, ie,
                                          &outp, outb, oe))
                                goto cleanup;
                            break;
                        }
                    }
                }
                if (j == pl->lit) goto cleanup;
            }
            if (lc < HUF_DECBITS && ptr < ie) hrefill(&c, &lc, &ptr, ie);
        }
    }

    {
        int i = (8 - nBits) & 7;
        c >>= i;
        lc -= i;
        while (lc > 0) {
            uint32_t code = fast[(c << (HUF_DECBITS - lc)) & HUF_DECMASK];
            if (code) {
                lc -= (int)(code & 63u);
                if (!get_code((int)(code >> 6), rlc, &c, &lc, &ptr, ie, &outp, outb,
                              oe))
                    goto cleanup;
            } else {
                const HufDec *pl =
                    &longdec[(c << (HUF_DECBITS - lc)) & HUF_DECMASK];
                if (!pl->p) goto cleanup;
                goto cleanup;
            }
        }
    }
    ret = 1;

cleanup:
    if (w == &local) {
        exr_free(a, w->long_storage);
        exr_free(a, w->counts);
        exr_free(a, w->longdec);
        exr_free(a, w->fast);
        exr_free(a, w->hcode);
        exr_free(a, w->lengths);
        exr_free(a, w->symbols);
        exr_free(a, w->ids);
    }
    return ret;
}

/* ---- orchestrator --------------------------------------------------------- */

exr_result exr_piz_decompress(const exr_codec_ctx *ctx, const uint8_t *src,
                              size_t src_size, uint8_t *dst, size_t dst_size) {
    const exr_allocator *a = ctx->alloc;
    int xmin = ctx->x, xmax = ctx->x + (ctx->width - 1);
    const uint8_t *ptr = src, *ptr_end = src + src_size;
    uint8_t bitmap[PIZ_BITMAP_SIZE];
    uint16_t *rev_lut = NULL, *tmp = NULL;
    uint16_t minNonZero, maxNonZero, maxValue;
    size_t total = 0;
    PizChan *cd = NULL;
    uint16_t *chan_ptr;
    uint32_t huf_length;
    int c, line;
    uint8_t *out;
    int *emitted = NULL;
    PizHufWorkspace local = {0};
    PizHufWorkspace *scratch = &local;
    void **slot = NULL;
    exr_result rc = EXR_SUCCESS;

    if (ctx->num_channels <= 0 || ctx->num_channels > 1024)
        return EXR_ERROR_CORRUPT;
    if (src_size < 4) return EXR_ERROR_CORRUPT;

    minNonZero = exr_rd_u16(ptr);
    maxNonZero = exr_rd_u16(ptr + 2);
    ptr += 4;
    memset(bitmap, 0, sizeof(bitmap));
    if (maxNonZero >= PIZ_BITMAP_SIZE) return EXR_ERROR_CORRUPT;
    if (minNonZero <= maxNonZero) {
        size_t blen = (size_t)(maxNonZero - minNonZero + 1);
        if ((size_t)(ptr_end - ptr) < blen) return EXR_ERROR_CORRUPT;
        if ((size_t)minNonZero + blen > PIZ_BITMAP_SIZE) return EXR_ERROR_CORRUPT;
        memcpy(bitmap + minNonZero, ptr, blen);
        ptr += blen;
    } else if (!(minNonZero == (PIZ_BITMAP_SIZE - 1) && maxNonZero == 0)) {
        return EXR_ERROR_CORRUPT;
    }

    /* Reader workers share the public context, so only the serial path may
     * reuse its PIZ scratch. Threaded decodes use a private workspace. */
    slot = exr_get_num_threads() <= 1 ? exr_context_piz_slot(ctx->context) : NULL;
    if (slot) {
        a = exr_context_allocator(ctx->context);
        if (!*slot) {
            *slot = exr_calloc(a, 1, sizeof(*scratch));
            if (!*slot) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
        }
        scratch = (PizHufWorkspace *)*slot;
    }
    if (!scratch->rev_lut)
        scratch->rev_lut = (uint16_t *)exr_malloc(
            a, sizeof(uint16_t) * PIZ_USHORT_RANGE);
    if (!scratch->rev_lut) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
    if (!scratch->bitmap)
        scratch->bitmap = (uint8_t *)exr_malloc(a, PIZ_BITMAP_SIZE);
    if (!scratch->bitmap) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
    rev_lut = scratch->rev_lut;
    if (scratch->bitmap_valid &&
        memcmp(scratch->bitmap, bitmap, PIZ_BITMAP_SIZE) == 0) {
        maxValue = scratch->bitmap_max;
    } else {
        maxValue = reverse_lut_from_bitmap(bitmap, rev_lut);
        memcpy(scratch->bitmap, bitmap, PIZ_BITMAP_SIZE);
        scratch->bitmap_max = maxValue;
        scratch->bitmap_valid = 1;
    }

    /* total uint16 samples across channels (FLOAT/UINT = 2 lanes, HALF = 1) */
    for (c = 0; c < ctx->num_channels; ++c) {
        int xs = ctx->channels[c].x_sampling, ys = ctx->channels[c].y_sampling;
        int nx, ny, lanes;
        size_t s;
        if (xs <= 0 || ys <= 0) { rc = EXR_ERROR_CORRUPT; goto done; }
        nx = exr_num_samples(xmin, xmax, xs);
        ny = exr_num_samples(ctx->y, (int64_t)ctx->y + ctx->num_lines - 1, ys);
        if (nx < 0) nx = 0;
        if (ny < 0) ny = 0;
        lanes = (ctx->channels[c].pixel_type == EXR_PIXEL_HALF) ? 1 : 2;
        if (exr_mul_ovf((size_t)nx * (size_t)ny, (size_t)lanes, &s)) {
            rc = EXR_ERROR_CORRUPT;
            goto done;
        }
        s = (size_t)nx * (size_t)ny * (size_t)lanes;
        if (exr_add_ovf(total, s, &total)) { rc = EXR_ERROR_CORRUPT; goto done; }
    }
    if (total == 0 || total > SIZE_MAX / sizeof(uint16_t)) {
        rc = EXR_ERROR_CORRUPT;
        goto done;
    }

    if (total > scratch->tmp_capacity) {
        size_t bytes;
        uint16_t *p;
        if (exr_mul_ovf(total, sizeof(uint16_t), &bytes)) {
            rc = EXR_ERROR_CORRUPT;
            goto done;
        }
        p = (uint16_t *)exr_malloc(a, bytes);
        if (!p) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
        exr_free(a, scratch->tmp);
        scratch->tmp = p;
        scratch->tmp_capacity = total;
    }
    tmp = scratch->tmp;

    if ((size_t)ctx->num_channels > scratch->channels_capacity) {
        size_t bytes;
        PizChan *p;
        if (exr_mul_ovf((size_t)ctx->num_channels, sizeof(PizChan), &bytes)) {
            rc = EXR_ERROR_CORRUPT;
            goto done;
        }
        p = (PizChan *)exr_malloc(a, bytes);
        if (!p) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
        exr_free(a, scratch->channels);
        scratch->channels = p;
        scratch->channels_capacity = (size_t)ctx->num_channels;
    }
    cd = scratch->channels;
    for (c = 0; c < ctx->num_channels; ++c) {
        int xs = ctx->channels[c].x_sampling, ys = ctx->channels[c].y_sampling;
        int nx = exr_num_samples(xmin, xmax, xs);
        int ny = exr_num_samples(ctx->y, (int64_t)ctx->y + ctx->num_lines - 1, ys);
        if (nx < 0) nx = 0;
        if (ny < 0) ny = 0;
        cd[c].start = NULL;
        cd[c].nx = nx;
        cd[c].ny = ny;
        cd[c].size = (ctx->channels[c].pixel_type == EXR_PIXEL_HALF) ? 1 : 2;
    }

    if ((size_t)ctx->num_channels > scratch->emitted_capacity) {
        size_t bytes;
        int *p;
        if (exr_mul_ovf((size_t)ctx->num_channels, sizeof(int), &bytes)) {
            rc = EXR_ERROR_CORRUPT;
            goto done;
        }
        p = (int *)exr_malloc(a, bytes);
        if (!p) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
        exr_free(a, scratch->emitted);
        scratch->emitted = p;
        scratch->emitted_capacity = (size_t)ctx->num_channels;
    }
    emitted = scratch->emitted;
    memset(emitted, 0, (size_t)ctx->num_channels * sizeof(*emitted));

    if ((size_t)(ptr_end - ptr) < 4) { rc = EXR_ERROR_CORRUPT; goto done; }
    huf_length = exr_rd_u32(ptr);
    ptr += 4;
    if ((size_t)(ptr_end - ptr) < (size_t)huf_length) {
        rc = EXR_ERROR_CORRUPT;
        goto done;
    }
    {
        int decoded = huf_uncompress(a, ctx->context, ptr, huf_length, tmp, total);
        if (decoded <= 0) {
            rc = decoded < 0 ? EXR_ERROR_OUT_OF_MEMORY : EXR_ERROR_CORRUPT;
            goto done;
        }
    }

    chan_ptr = tmp;
    for (c = 0; c < ctx->num_channels; ++c) {
        cd[c].start = chan_ptr;
        chan_ptr += (size_t)cd[c].nx * cd[c].ny * cd[c].size;
    }
    for (c = 0; c < ctx->num_channels; ++c) {
        int lane;
        for (lane = 0; lane < cd[c].size; ++lane)
            wav2_decode(cd[c].start + lane, cd[c].nx, cd[c].size, cd[c].ny,
                        cd[c].nx * cd[c].size, maxValue);
    }
    apply_lut(rev_lut, tmp, total);

    /* emit canonical block layout (per line, per sampled channel, dense) */
    out = dst;
    for (line = 0; line < ctx->num_lines; ++line) {
        int yy = ctx->y + line;
        for (c = 0; c < ctx->num_channels; ++c) {
            int ys = ctx->channels[c].y_sampling;
            int row, line_samples;
            const uint16_t *ld;
            if ((yy % ys) != 0) continue;
            row = emitted[c]++;
            if (row >= cd[c].ny) { rc = EXR_ERROR_CORRUPT; goto done; }
            line_samples = cd[c].nx * cd[c].size;
            ld = cd[c].start + (size_t)row * line_samples;
            if (out + (size_t)line_samples * 2 > dst + dst_size) {
                rc = EXR_ERROR_CORRUPT;
                goto done;
            }
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
            /* The decoded samples are native uint16_t values.  EXR's byte
             * layout is little-endian, so copy a complete row on the common
             * host instead of repacking every sample one byte at a time. */
            memcpy(out, ld, (size_t)line_samples * 2);
            out += (size_t)line_samples * 2;
#else
            for (int x = 0; x < line_samples; ++x) {
                out[0] = (uint8_t)(ld[x] & 0xff);
                out[1] = (uint8_t)(ld[x] >> 8);
                out += 2;
            }
#endif
        }
    }
    if ((size_t)(out - dst) != dst_size) rc = EXR_ERROR_CORRUPT;

done:
    if (scratch == &local) {
        exr_free(a, scratch->emitted);
        exr_free(a, scratch->channels);
        exr_free(a, scratch->tmp);
        exr_free(a, scratch->rev_lut);
        exr_free(a, scratch->bitmap);
    }
    return rc;
}

/* ===========================================================================
 * PIZ encode (forward wavelet + range LUT + canonical Huffman).
 * Ported from the legacy single-header tinyexr (OpenEXR-derived). The STL heap
 * in hufBuildEncTable is reimplemented as a plain C index min-heap.
 * ========================================================================= */

static void wenc14(uint16_t a, uint16_t b, uint16_t *l, uint16_t *h) {
    int16_t as = (int16_t)a, bs = (int16_t)b;
    *l = (uint16_t)(int16_t)((as + bs) >> 1);
    *h = (uint16_t)(int16_t)(as - bs);
}
static void wenc16(uint16_t a, uint16_t b, uint16_t *l, uint16_t *h) {
    int ao = (a + WAV_A_OFFSET) & WAV_MOD_MASK;
    int m = (ao + b) >> 1;
    int d = ao - b;
    if (d < 0) m = (m + WAV_A_OFFSET) & WAV_MOD_MASK;
    d &= WAV_MOD_MASK;
    *l = (uint16_t)m;
    *h = (uint16_t)d;
}

static PIZ_OPT_O3 void wav2_encode(uint16_t *in, int nx, int ox, int ny,
                                   int oy, uint16_t mx) {
    int w14 = (mx < (1 << 14));
    int n = (nx > ny) ? ny : nx;
    int p = 1, p2 = 2;
    uint16_t i00, i01, i10, i11;
    while (p2 <= n) {
        uint16_t *py = in;
        uint16_t *ey = in + oy * (ny - p2);
        int oy1 = oy * p, oy2 = oy * p2, ox1 = ox * p, ox2 = ox * p2;
        for (; py <= ey; py += oy2) {
            uint16_t *px = py;
            uint16_t *ex = py + ox * (nx - p2);
            for (; px <= ex; px += ox2) {
                uint16_t *p01 = px + ox1, *p10 = px + oy1, *p11 = p10 + ox1;
                if (w14) {
                    wenc14(*px, *p01, &i00, &i01);
                    wenc14(*p10, *p11, &i10, &i11);
                    wenc14(i00, i10, px, p10);
                    wenc14(i01, i11, p01, p11);
                } else {
                    wenc16(*px, *p01, &i00, &i01);
                    wenc16(*p10, *p11, &i10, &i11);
                    wenc16(i00, i10, px, p10);
                    wenc16(i01, i11, p01, p11);
                }
            }
            if (nx & p) {
                uint16_t *p10 = px + oy1;
                if (w14) wenc14(*px, *p10, &i00, p10);
                else wenc16(*px, *p10, &i00, p10);
                *px = i00;
            }
        }
        if (ny & p) {
            uint16_t *px = py;
            uint16_t *ex = py + ox * (nx - p2);
            for (; px <= ex; px += ox2) {
                uint16_t *p01 = px + ox1;
                if (w14) wenc14(*px, *p01, &i00, p01);
                else wenc16(*px, *p01, &i00, p01);
                *px = i00;
            }
        }
        p = p2;
        p2 <<= 1;
    }
}

static void bitmap_from_data(const uint16_t *data, size_t n, uint8_t *bitmap,
                             uint16_t *minNZ, uint16_t *maxNZ) {
    size_t i;
    int mn = PIZ_BITMAP_SIZE - 1, mx = 0;
    memset(bitmap, 0, PIZ_BITMAP_SIZE);
    for (i = 0; i < n; ++i) bitmap[data[i] >> 3] |= (uint8_t)(1 << (data[i] & 7));
    bitmap[0] &= (uint8_t)~1; /* zero never explicitly stored */
    for (i = 0; i < PIZ_BITMAP_SIZE; ++i)
        if (bitmap[i]) {
            if (mn > (int)i) mn = (int)i;
            if (mx < (int)i) mx = (int)i;
        }
    *minNZ = (uint16_t)mn;
    *maxNZ = (uint16_t)mx;
}

static uint16_t forward_lut_from_bitmap(const uint8_t *bitmap, uint16_t *lut) {
    int i, k = 0;
    for (i = 0; i < PIZ_USHORT_RANGE; ++i) {
        if (i == 0 || (bitmap[i >> 3] & (1 << (i & 7))))
            lut[i] = (uint16_t)k++;
        else
            lut[i] = 0;
    }
    return (uint16_t)(k - 1);
}

/* MSB-first bit writer for the PIZ Huffman stream. */
typedef struct {
    uint8_t *p;
    uint64_t c;
    int lc;
} pizbw;
static void piz_outbits(pizbw *w, int nbits, uint64_t bits) {
    w->c <<= nbits;
    w->lc += nbits;
    w->c |= bits;
    while (w->lc >= 8) *w->p++ = (uint8_t)(w->c >> (w->lc -= 8));
}

/* index min-heap keyed on frq[idx] */
static void heap_sift_down(int *heap, int n, int i, const int64_t *frq) {
    for (;;) {
        int l = 2 * i + 1, r = 2 * i + 2, s = i, t;
        if (l < n && frq[heap[l]] < frq[heap[s]]) s = l;
        if (r < n && frq[heap[r]] < frq[heap[s]]) s = r;
        if (s == i) break;
        t = heap[i]; heap[i] = heap[s]; heap[s] = t;
        i = s;
    }
}
static void heap_sift_up(int *heap, int i, const int64_t *frq) {
    while (i > 0) {
        int parent = (i - 1) / 2, t;
        if (frq[heap[parent]] <= frq[heap[i]]) break;
        t = heap[i]; heap[i] = heap[parent]; heap[parent] = t;
        i = parent;
    }
}

static int huf_build_enc_table(const exr_allocator *a, int64_t *frq, int *pim,
                               int *piM) {
    int *hlink = (int *)exr_malloc(a, sizeof(int) * PIZ_HUF_ENCSIZE);
    int *heap = (int *)exr_malloc(a, sizeof(int) * PIZ_HUF_ENCSIZE);
    int64_t *scode = (int64_t *)exr_calloc(a, PIZ_HUF_ENCSIZE, sizeof(int64_t));
    int im = 0, iM = 0, nf = 0, i, k;
    int ret = 0;
    if (!hlink || !heap || !scode) goto done;

    while (im < PIZ_HUF_ENCSIZE && !frq[im]) im++;
    if (im >= PIZ_HUF_ENCSIZE) goto done;
    for (i = im; i < PIZ_HUF_ENCSIZE; ++i) {
        hlink[i] = i;
        if (frq[i]) { heap[nf++] = i; iM = i; }
    }
    iM++;
    frq[iM] = 1;
    heap[nf++] = iM;

    for (k = nf / 2 - 1; k >= 0; --k) heap_sift_down(heap, nf, k, frq);

    while (nf > 1) {
        int mm = heap[0];
        int m, j;
        heap[0] = heap[--nf];
        heap_sift_down(heap, nf, 0, frq);
        m = heap[0];
        heap[0] = heap[--nf];
        heap_sift_down(heap, nf, 0, frq);
        frq[m] += frq[mm];
        heap[nf] = m;
        heap_sift_up(heap, nf, frq);
        nf++;

        for (j = m;; j = hlink[j]) {
            scode[j]++;
            if (scode[j] > 58) goto done;
            if (hlink[j] == j) { hlink[j] = mm; break; }
        }
        for (j = mm;; j = hlink[j]) {
            scode[j]++;
            if (scode[j] > 58) goto done;
            if (hlink[j] == j) break;
        }
    }

    canonical_code_table64(scode, im, iM);
    memcpy(frq, scode, sizeof(int64_t) * PIZ_HUF_ENCSIZE);
    *pim = im;
    *piM = iM;
    ret = 1;
done:
    exr_free(a, hlink);
    exr_free(a, heap);
    exr_free(a, scode);
    return ret;
}

static int64_t huf_length(int64_t code) { return code & 63; }
static int64_t huf_code(int64_t code) { return code >> 6; }

static void huf_pack_enc_table(const int64_t *hcode, int im, int iM,
                               uint8_t **pcode) {
    pizbw w;
    w.p = *pcode;
    w.c = 0;
    w.lc = 0;
    for (; im <= iM; ++im) {
        int l = (int)huf_length(hcode[im]);
        if (l == 0) {
            int zerun = 1;
            while ((im < iM) && (zerun < 255 + SHORTEST_LONG_RUN)) {
                if (huf_length(hcode[im + 1]) > 0) break;
                ++im;
                ++zerun;
            }
            if (zerun >= 2) {
                if (zerun >= SHORTEST_LONG_RUN) {
                    piz_outbits(&w, 6, LONG_ZEROCODE_RUN);
                    piz_outbits(&w, 8, (uint64_t)(zerun - SHORTEST_LONG_RUN));
                } else {
                    piz_outbits(&w, 6, (uint64_t)(SHORT_ZEROCODE_RUN + zerun - 2));
                }
                continue;
            }
        }
        piz_outbits(&w, 6, (uint64_t)l);
    }
    if (w.lc > 0) *w.p++ = (uint8_t)(w.c << (8 - w.lc));
    *pcode = w.p;
}

static void huf_output_code(pizbw *w, int64_t code) {
    piz_outbits(w, (int)huf_length(code), (uint64_t)huf_code(code));
}
static void huf_send_code(pizbw *w, int64_t sCode, int runCount, int64_t rCode) {
    if (huf_length(sCode) + huf_length(rCode) + 8 < huf_length(sCode) * runCount) {
        huf_output_code(w, sCode);
        huf_output_code(w, rCode);
        piz_outbits(w, 8, (uint64_t)runCount);
    } else {
        while (runCount-- >= 0) huf_output_code(w, sCode);
    }
}

static PIZ_OPT_O3 int huf_encode(const int64_t *hcode, const uint16_t *in,
                                 int ni, int rlc, uint8_t *out) {
    pizbw w;
    int s = in[0], cs = 0, i;
    w.p = out;
    w.c = 0;
    w.lc = 0;
    for (i = 1; i < ni; ++i) {
        if (s == in[i] && cs < 255) {
            cs++;
        } else {
            huf_send_code(&w, hcode[s], cs, hcode[rlc]);
            cs = 0;
        }
        s = in[i];
    }
    huf_send_code(&w, hcode[s], cs, hcode[rlc]);
    if (w.lc) *w.p = (uint8_t)((w.c << (8 - w.lc)) & 0xff);
    return (int)((w.p - out) * 8 + w.lc);
}

/* Compress nRaw uint16 values; returns total bytes written to `out`. */
static PIZ_OPT_O3 int huf_compress(const exr_allocator *a,
                                   const uint16_t *raw, int nRaw,
                                   uint8_t *out, int *err) {
    int64_t *freq;
    int im = 0, iM = 0;
    uint8_t *tableStart, *tableEnd, *dataStart;
    int tableLength, nBits, data_length, i;

    *err = 0;
    if (nRaw == 0) return 0;
    freq = (int64_t *)exr_calloc(a, PIZ_HUF_ENCSIZE, sizeof(int64_t));
    if (!freq) { *err = 1; return 0; }
    for (i = 0; i < nRaw; ++i) freq[raw[i]]++;

    if (!huf_build_enc_table(a, freq, &im, &iM)) {
        exr_free(a, freq);
        *err = 1;
        return 0;
    }

    tableStart = out + 20;
    tableEnd = tableStart;
    huf_pack_enc_table(freq, im, iM, &tableEnd);
    tableLength = (int)(tableEnd - tableStart);

    dataStart = tableEnd;
    nBits = huf_encode(freq, raw, nRaw, iM, dataStart);
    data_length = (nBits + 7) / 8;

    exr_wr_u32(out, (uint32_t)im);
    exr_wr_u32(out + 4, (uint32_t)iM);
    exr_wr_u32(out + 8, (uint32_t)tableLength);
    exr_wr_u32(out + 12, (uint32_t)nBits);
    exr_wr_u32(out + 16, 0);

    exr_free(a, freq);
    return (int)(dataStart + data_length - out);
}

exr_result exr_piz_compress(const exr_codec_ctx *ctx, const uint8_t *block,
                            size_t n, uint8_t **out_data, size_t *out_size) {
    const exr_allocator *a = ctx->alloc;
    int xmin = ctx->x, xmax = ctx->x + (ctx->width - 1);
    size_t total = n / 2;
    uint16_t *tmp = NULL, *lut = NULL;
    uint8_t bitmap[PIZ_BITMAP_SIZE];
    uint16_t minNZ, maxNZ, maxValue;
    PizChan *cd = NULL;
    uint16_t *chan_ptr;
    int *emitted = NULL;
    uint8_t *out = NULL;
    size_t cap, pos;
    int c, line, herr = 0, hlen;
    exr_result rc = EXR_SUCCESS;

    *out_data = NULL;
    *out_size = 0;
    if (ctx->num_channels <= 0 || ctx->num_channels > 1024 || (n & 1))
        return EXR_ERROR_INVALID_ARGUMENT;

    tmp = (uint16_t *)exr_calloc(a, total ? total : 1, sizeof(uint16_t));
    lut = (uint16_t *)exr_malloc(a, sizeof(uint16_t) * PIZ_USHORT_RANGE);
    cd = (PizChan *)exr_calloc(a, (size_t)ctx->num_channels, sizeof(PizChan));
    emitted = (int *)exr_calloc(a, (size_t)ctx->num_channels, sizeof(int));
    if (!tmp || !lut || !cd || !emitted) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }

    /* per-channel planar layout */
    for (c = 0; c < ctx->num_channels; ++c) {
        int xs = ctx->channels[c].x_sampling, ys = ctx->channels[c].y_sampling;
        int nx = exr_num_samples(xmin, xmax, xs);
        int ny = exr_num_samples(ctx->y, (int64_t)ctx->y + ctx->num_lines - 1, ys);
        if (nx < 0) nx = 0;
        if (ny < 0) ny = 0;
        cd[c].nx = nx;
        cd[c].ny = ny;
        cd[c].size = (ctx->channels[c].pixel_type == EXR_PIXEL_HALF) ? 1 : 2;
    }
    chan_ptr = tmp;
    for (c = 0; c < ctx->num_channels; ++c) {
        cd[c].start = chan_ptr;
        chan_ptr += (size_t)cd[c].nx * cd[c].ny * cd[c].size;
    }

    /* reorganize the canonical block (dense per line/channel) into planar tmp */
    {
        const uint8_t *bp = block;
        const uint8_t *bend = block + n;
        for (line = 0; line < ctx->num_lines; ++line) {
            int yy = ctx->y + line;
            for (c = 0; c < ctx->num_channels; ++c) {
                int ys = ctx->channels[c].y_sampling;
                int row, ls = cd[c].nx * cd[c].size, x;
                uint16_t *dstp;
                if ((yy % ys) != 0) continue;
                row = emitted[c]++;
                if (row >= cd[c].ny) { rc = EXR_ERROR_CORRUPT; goto done; }
                if (bp + (size_t)ls * 2 > bend) { rc = EXR_ERROR_CORRUPT; goto done; }
                dstp = cd[c].start + (size_t)row * ls;
                for (x = 0; x < ls; ++x) {
                    dstp[x] = exr_rd_u16(bp);
                    bp += 2;
                }
            }
        }
    }

    bitmap_from_data(tmp, total, bitmap, &minNZ, &maxNZ);
    maxValue = forward_lut_from_bitmap(bitmap, lut);
    apply_lut(lut, tmp, total);

    for (c = 0; c < ctx->num_channels; ++c) {
        int lane;
        for (lane = 0; lane < cd[c].size; ++lane)
            wav2_encode(cd[c].start + lane, cd[c].nx, cd[c].size, cd[c].ny,
                        cd[c].nx * cd[c].size, maxValue);
    }

    /* output: minNZ(2) maxNZ(2) bitmap[min..max] hufLength(4) hufdata */
    cap = 4 + PIZ_BITMAP_SIZE + 4 + total * 2 + PIZ_HUF_ENCSIZE * 2 + 256;
    out = (uint8_t *)exr_malloc(a, cap);
    if (!out) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
    exr_wr_u16(out, minNZ);
    exr_wr_u16(out + 2, maxNZ);
    pos = 4;
    if (minNZ <= maxNZ) {
        size_t blen = (size_t)(maxNZ - minNZ + 1);
        memcpy(out + pos, bitmap + minNZ, blen);
        pos += blen;
    }
    hlen = huf_compress(a, tmp, (int)total, out + pos + 4, &herr);
    if (herr) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
    exr_wr_u32(out + pos, (uint32_t)hlen);
    pos += 4 + (size_t)hlen;

    if (pos >= n) { /* PIZ did not help: store the canonical block raw */
        exr_free(a, out);
        out = (uint8_t *)exr_malloc(a, n ? n : 1);
        if (!out) { rc = EXR_ERROR_OUT_OF_MEMORY; goto done; }
        memcpy(out, block, n);
        *out_data = out;
        *out_size = n;
        out = NULL;
        goto done;
    }
    *out_data = out;
    *out_size = pos;
    out = NULL;

done:
    exr_free(a, tmp);
    exr_free(a, lut);
    exr_free(a, cd);
    exr_free(a, emitted);
    exr_free(a, out);
    return rc;
}
