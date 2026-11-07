/*
 * TinyEXR - DEFLATE: inflate (decode) for ZIP/ZIPS/PXR24. The DEFLATE encoder
 * is added in Phase 8.
 *
 * The inflate core is a compact, self-contained pure-C11 implementation with a
 * 12-bit fast Huffman table. It originated in TinyEXR's own deflate decoder.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "exr_internal.h"

#if defined(__GNUC__) || defined(__clang__)
#define DFL_LIKELY(x) __builtin_expect(!!(x), 1)
#define DFL_UNLIKELY(x) __builtin_expect(!!(x), 0)
#define DFL_INLINE __attribute__((always_inline)) static inline
#else
#define DFL_LIKELY(x) (x)
#define DFL_UNLIKELY(x) (x)
#define DFL_INLINE static inline
#endif

#define DFL_MAX_BITS 15
#define DFL_LITLEN_CODES 288
#define DFL_DIST_CODES 32
#define DFL_CODELEN_CODES 19
#define DFL_FAST_BITS 11
#define DFL_FAST_SIZE (1 << DFL_FAST_BITS)
#define DFL_DIST_FAST_BITS 8
#define DFL_DIST_FAST_SIZE (1 << DFL_DIST_FAST_BITS)
#define DFL_LONG_SLOT_BITS (DFL_MAX_BITS - DFL_FAST_BITS)
#define DFL_LONG_SLOT_SIZE (1 << DFL_LONG_SLOT_BITS)
#define DFL_LONG_TABLE_SIZE (320 * DFL_LONG_SLOT_SIZE)
#define DFL_ENTRY_VALID UINT32_C(0x80000000)
#define DFL_ENTRY_LITERAL UINT32_C(0x40000000)

static const uint8_t dfl_codelen_order[DFL_CODELEN_CODES] = {
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};

static const uint16_t dfl_length_base[29] = {
    3,  4,  5,  6,   7,   8,   9,   10,  11,  13,  15,  17, 19, 23, 27,
    31, 35, 43, 51,  59,  67,  83,  99,  115, 131, 163, 195, 227, 258};
static const uint8_t dfl_length_extra[29] = {
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2,
    2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};

static const uint16_t dfl_dist_base[30] = {
    1,    2,    3,    4,    5,    7,     9,     13,    17,   25,
    33,   49,   65,   97,   129,  193,   257,   385,   513,  769,
    1025, 1537, 2049, 3073, 4097, 6145,  8193,  12289, 16385, 24577};
static const uint8_t dfl_dist_extra[30] = {
    0, 0, 0,  0,  1,  1,  2,  2,  3,  3,  4,  4,  5,  5,  6,
    6, 7, 7,  8,  8,  9,  9, 10, 10, 11, 11, 12, 12, 13, 13};

typedef struct {
    uint64_t bits;
    int count;
    const uint8_t *ptr;
    const uint8_t *end;
} dfl_br;

DFL_INLINE void br_init(dfl_br *br, const uint8_t *data, size_t size) {
    br->bits = 0;
    br->count = 0;
    br->ptr = data;
    br->end = data + size;
}
DFL_INLINE void br_refill(dfl_br *br) {
    while (br->count <= 56 && br->ptr < br->end) {
        br->bits |= (uint64_t)(*br->ptr++) << br->count;
        br->count += 8;
    }
}
DFL_INLINE void br_refill_fast(dfl_br *br) {
    if (DFL_LIKELY((size_t)(br->end - br->ptr) >= 8)) {
        uint64_t nb;
        memcpy(&nb, br->ptr, 8);
        br->bits |= nb << br->count;
        {
            int adv = (64 - br->count) / 8;
            br->ptr += adv;
            br->count += adv * 8;
        }
    } else {
        br_refill(br);
    }
}
DFL_INLINE void br_refill_fast_state(uint64_t *bits, int *count,
                                     const uint8_t **ptr,
                                     const uint8_t *end) {
    if (*count > 56) return;
    if (DFL_LIKELY((size_t)(end - *ptr) >= 8)) {
        uint64_t nb;
        int adv;
        memcpy(&nb, *ptr, 8);
        *bits |= nb << *count;
        adv = (64 - *count) / 8;
        *ptr += adv;
        *count += adv * 8;
    } else {
        while (*count <= 56 && *ptr < end) {
            *bits |= (uint64_t)(*(*ptr)++) << *count;
            *count += 8;
        }
    }
}
/* In the guarded fast loop, only the low byte of count is meaningful.  Keep
 * the remaining bits available for refill state, while consuming the packed
 * entry's low-byte bit count explicitly. */
DFL_INLINE void br_refill_fast_meta(uint64_t *bits, uint32_t *count,
                                    const uint8_t **ptr,
                                    const uint8_t *end) {
    uint32_t c = *count & 0xFFu;
    if (c >= 56) return;
    if (DFL_LIKELY((size_t)(end - *ptr) >= 8)) {
        uint64_t nb;
        memcpy(&nb, *ptr, 8);
        *bits |= nb << c;
        *ptr += 7 - ((c >> 3) & 7);
        *count |= 56u;
    } else {
        while (c < 56 && *ptr < end) {
            *bits |= (uint64_t)(*(*ptr)++) << c;
            c += 8;
        }
        *count = (*count & ~UINT32_C(0xFF)) | c;
    }
}
DFL_INLINE uint32_t br_peek(const dfl_br *br, int n) {
    return (uint32_t)(br->bits & ((1ULL << n) - 1));
}
DFL_INLINE void br_consume(dfl_br *br, int n) {
    br->bits >>= n;
    br->count -= n;
}
DFL_INLINE uint32_t br_read(dfl_br *br, int n) {
    uint32_t r = br_peek(br, n);
    br_consume(br, n);
    return r;
}
DFL_INLINE void br_align(dfl_br *br) { br_consume(br, br->count & 7); }

typedef struct {
    uint32_t fast_table[DFL_FAST_SIZE]; /* metadata-bearing decode entries */
    /* Distance codes are much smaller than literal/length codes.  An eight-bit
     * primary table covers the common case without a larger 15-bit table. */
    uint32_t dist_fast_table[DFL_DIST_FAST_SIZE];
    /* Each occupied 11-bit prefix owns sixteen entries for the remaining
     * 4 bits.  Only 12--15 bit codes need this table; the scalar list below
     * remains available for truncated final buffers and malformed streams. */
    uint16_t long_index[DFL_FAST_SIZE];
    uint16_t long_table[DFL_LONG_TABLE_SIZE];
    int long_count;
    uint32_t distance_info[30]; /* base | (extra << 15) */
    uint16_t slow_table[640];
    int slow_count;
    int max_bits;
    int kind; /* 0=codelen, 1=litlen, 2=distance */
} dfl_huff;

static uint32_t dfl_fast_entry(int sym, int len, int kind) {
    int extra = 0;
    uint32_t entry = DFL_ENTRY_VALID | ((uint32_t)sym << 8) |
                     (uint32_t)len;
    if (kind == 1 && sym < 256) entry |= DFL_ENTRY_LITERAL;
    if (kind == 1 && sym >= 257 && sym <= 285) {
        int i = sym - 257;
        extra = dfl_length_extra[i];
        entry |= (uint32_t)dfl_length_base[i] << 18;
        entry |= (uint32_t)extra << 27;
    } else if (kind == 2 && sym < 30) {
        extra = dfl_dist_extra[sym];
        entry |= (uint32_t)extra << 27;
    }
    entry = (entry & ~UINT32_C(0xFF)) |
            (uint32_t)(len + extra);
    return entry;
}

DFL_INLINE int dfl_entry_sym(uint32_t entry) {
    return (int)((entry >> 8) & 0x1FF);
}
DFL_INLINE int dfl_entry_code_len(uint32_t entry,
                                  const dfl_huff *table) {
    int sym = dfl_entry_sym(entry);
    int extra = 0;
    if (table->kind == 1 && sym >= 257 && sym <= 285)
        extra = dfl_length_extra[sym - 257];
    else if (table->kind == 2 && sym < 30)
        extra = dfl_dist_extra[sym];
    return (int)(entry & 0xFF) - extra;
}

DFL_INLINE int dfl_lookup_litlen(const dfl_huff *table, uint64_t bits,
                                 int count, uint32_t *entry) {
    uint32_t idx = (uint32_t)(bits & (DFL_FAST_SIZE - 1));
    *entry = table->fast_table[idx];
    if (DFL_LIKELY(*entry & DFL_ENTRY_VALID)) return 1;
    if (count < DFL_MAX_BITS) return 0;
    {
        uint16_t offset = table->long_index[idx];
        uint16_t long_entry;
        if (offset == 0) return 0;
        long_entry = table->long_table[
            (offset - 1) |
            ((bits >> DFL_FAST_BITS) & (DFL_LONG_SLOT_SIZE - 1))];
        if (!(long_entry & 0x8000)) return 0;
        *entry = dfl_fast_entry((long_entry >> 4) & 0x7FF,
                                long_entry & 0xF, table->kind);
        return 1;
    }
}

DFL_INLINE int dfl_lookup_dist(const dfl_huff *table, uint64_t bits,
                               int count, uint32_t *entry) {
    uint32_t idx = (uint32_t)(bits & (DFL_DIST_FAST_SIZE - 1));
    *entry = table->dist_fast_table[idx];
    if (DFL_LIKELY(*entry & DFL_ENTRY_VALID)) return 1;
    idx = (uint32_t)(bits & (DFL_FAST_SIZE - 1));
    *entry = table->fast_table[idx];
    if (DFL_LIKELY(*entry & DFL_ENTRY_VALID)) return 1;
    if (count < DFL_MAX_BITS) return 0;
    {
        uint16_t offset = table->long_index[idx];
        uint16_t long_entry;
        if (offset == 0) return 0;
        long_entry = table->long_table[
            (offset - 1) |
            ((bits >> DFL_FAST_BITS) & (DFL_LONG_SLOT_SIZE - 1))];
        if (!(long_entry & 0x8000)) return 0;
        *entry = dfl_fast_entry((long_entry >> 4) & 0x7FF,
                                long_entry & 0xF, table->kind);
        return 1;
    }
}

static void ht_fixed_litlen(dfl_huff *t) {
    int sym;
    t->kind = 1;
    t->max_bits = 9;
    t->slow_count = 0;
    t->long_count = 0;
    memset(t->distance_info, 0, sizeof(t->distance_info));
    memset(t->fast_table, 0, sizeof(t->fast_table));
    memset(t->dist_fast_table, 0, sizeof(t->dist_fast_table));
    memset(t->long_index, 0, sizeof(t->long_index));
    memset(t->long_table, 0, sizeof(t->long_table));
    memset(t->slow_table, 0, sizeof(t->slow_table));
    for (sym = 0; sym <= 287; sym++) {
        int len, code, rev = 0, i, fill;
        if (sym <= 143) { len = 8; code = 0x30 + sym; }
        else if (sym <= 255) { len = 9; code = 0x190 + (sym - 144); }
        else if (sym <= 279) { len = 7; code = sym - 256; }
        else { len = 8; code = 0xC0 + (sym - 280); }
        for (i = 0; i < len; i++) rev = (rev << 1) | ((code >> i) & 1);
        fill = 1 << (DFL_FAST_BITS - len);
        for (i = 0; i < fill; i++) {
            int idx = rev | (i << len);
            if (idx < DFL_FAST_SIZE)
                t->fast_table[idx] = dfl_fast_entry(sym, len, 1);
        }
    }
}
static void ht_fixed_dist(dfl_huff *t) {
    int sym;
    t->kind = 2;
    t->max_bits = 5;
    t->slow_count = 0;
    t->long_count = 0;
    memset(t->distance_info, 0, sizeof(t->distance_info));
    memset(t->fast_table, 0, sizeof(t->fast_table));
    memset(t->dist_fast_table, 0, sizeof(t->dist_fast_table));
    memset(t->long_index, 0, sizeof(t->long_index));
    memset(t->long_table, 0, sizeof(t->long_table));
    memset(t->slow_table, 0, sizeof(t->slow_table));
    for (sym = 0; sym < 30; ++sym)
        t->distance_info[sym] =
            (uint32_t)dfl_dist_base[sym] |
            ((uint32_t)dfl_dist_extra[sym] << 15);
    for (sym = 0; sym < 32; sym++) {
        int rev = 0, i, fill;
        for (i = 0; i < 5; i++) rev = (rev << 1) | ((sym >> i) & 1);
        fill = 1 << (DFL_FAST_BITS - 5);
        for (i = 0; i < fill; i++) {
            int idx = rev | (i << 5);
            if (idx < DFL_FAST_SIZE)
                t->fast_table[idx] = dfl_fast_entry(sym, 5, 2);
        }
        fill = 1 << (DFL_DIST_FAST_BITS - 5);
        for (i = 0; i < fill; i++)
            t->dist_fast_table[rev | (i << 5)] = dfl_fast_entry(sym, 5, 2);
    }
}
static int reverse_bits(int code, int len) {
    int rev = 0, i;
    for (i = 0; i < len; i++) rev = (rev << 1) | ((code >> i) & 1);
    return rev;
}

/* kind: 0 = code-length, 1 = literal/length, 2 = distance. It must be passed
 * explicitly: a distance alphabet may legally have exactly 19 codes (HDIST=18),
 * the same count as the code-length alphabet, and inferring the kind from the
 * count then decoded every distance of such a block wrongly. */
static int ht_build(dfl_huff *table, const uint8_t *lens, int count, int kind) {
    int bl_count[DFL_MAX_BITS + 1] = {0};
    int next_code[DFL_MAX_BITS + 1] = {0};
    int max_len = 0, i, code, sym, bits;
    uint16_t slow_codes[320], slow_syms[320];
    uint8_t slow_lens[320];
    uint16_t slow_counts[DFL_MAX_BITS + 1] = {0};
    uint16_t slow_offsets[DFL_MAX_BITS + 1] = {0};
    uint16_t slow_write[DFL_MAX_BITS + 1] = {0};
    int slow_total = 0;

    for (i = 0; i < count; i++) {
        if (lens[i] > 0) {
            bl_count[lens[i]]++;
            if (lens[i] > max_len) max_len = lens[i];
        }
    }
    table->max_bits = max_len;
    table->kind = kind;
    table->slow_count = 0;
    table->long_count = 0;
    memset(table->distance_info, 0, sizeof(table->distance_info));
    memset(table->fast_table, 0, sizeof(table->fast_table));
    memset(table->dist_fast_table, 0, sizeof(table->dist_fast_table));
    memset(table->long_index, 0, sizeof(table->long_index));
    memset(table->long_table, 0, sizeof(table->long_table));

    code = 0;
    for (bits = 1; bits <= max_len; bits++) {
        code = (code + bl_count[bits - 1]) << 1;
        next_code[bits] = code;
    }

    for (sym = 0; sym < count; sym++) {
        int len = lens[sym], code_val, rev;
        if (len == 0) continue;
        code_val = next_code[len]++;
        rev = reverse_bits(code_val, len);
        if (len <= DFL_FAST_BITS) {
            uint32_t entry = dfl_fast_entry(sym, len, table->kind);
            int fill = 1 << (DFL_FAST_BITS - len), k;
            for (k = 0; k < fill; k++) table->fast_table[rev | (k << len)] = entry;
            if (kind == 2 && len <= DFL_DIST_FAST_BITS) {
                int dist_fill = 1 << (DFL_DIST_FAST_BITS - len);
                for (k = 0; k < dist_fill; k++)
                    table->dist_fast_table[rev | (k << len)] = entry;
            }
        } else {
            if (len <= DFL_MAX_BITS) {
                int prefix = rev & (DFL_FAST_SIZE - 1);
                int extra = len - DFL_FAST_BITS;
                int suffix = (rev >> DFL_FAST_BITS) &
                             (DFL_LONG_SLOT_SIZE - 1);
                int fill = 1 << (DFL_LONG_SLOT_BITS - extra);
                uint16_t entry = (uint16_t)((sym << 4) | len | 0x8000);
                uint16_t offset;
                int k;

                if (table->long_index[prefix] == 0) {
                    if (table->long_count >
                        DFL_LONG_TABLE_SIZE - DFL_LONG_SLOT_SIZE)
                        return 0;
                    offset = (uint16_t)table->long_count;
                    table->long_index[prefix] = (uint16_t)(offset + 1);
                    table->long_count += DFL_LONG_SLOT_SIZE;
                } else {
                    offset = (uint16_t)(table->long_index[prefix] - 1);
                }
                for (k = 0; k < fill; ++k) {
                    uint16_t *slot = &table->long_table[offset + suffix +
                                                        (k << extra)];
                    if (*slot != 0) return 0;
                    *slot = entry;
                }
            }
            if (slow_total < 320) {
                slow_codes[slow_total] = (uint16_t)rev;
                slow_syms[slow_total] = (uint16_t)sym;
                slow_lens[slow_total] = (uint8_t)len;
                slow_counts[len]++;
                slow_total++;
            }
        }
    }

    if (kind == 2) {
        for (i = 0; i < 30 && i < count; ++i)
            table->distance_info[i] =
                (uint32_t)dfl_dist_base[i] |
                ((uint32_t)dfl_dist_extra[i] << 15);
    }

    {
        uint16_t *slow_ptr = table->slow_table;
        for (bits = DFL_FAST_BITS + 1;
             bits <= max_len && bits <= DFL_MAX_BITS; ++bits) {
            slow_offsets[bits] = (uint16_t)(slow_ptr - table->slow_table);
            slow_write[bits] = slow_offsets[bits] + 1;
            if ((size_t)(slow_ptr - table->slow_table) +
                    1 + 2 * slow_counts[bits] >
                sizeof(table->slow_table) / sizeof(table->slow_table[0]))
                return 0;
            *slow_ptr++ = slow_counts[bits];
            slow_ptr += 2 * slow_counts[bits];
            table->slow_count += slow_counts[bits];
        }
    }
    for (i = 0; i < slow_total; ++i) {
        int len = slow_lens[i];
        uint16_t pos;
        if (len <= DFL_FAST_BITS || len > DFL_MAX_BITS) continue;
        pos = slow_write[len];
        table->slow_table[pos++] = slow_codes[i];
        table->slow_table[pos] = slow_syms[i];
        slow_write[len] = pos + 1;
    }
    return 1;
}

static int decode_symbol_slow(dfl_br *reader, const dfl_huff *table) {
    const uint16_t *ptr = table->slow_table;
    int bits;
    if (reader->count < 15) br_refill(reader);
    for (bits = DFL_FAST_BITS + 1; bits <= table->max_bits && bits <= 15; bits++) {
        uint16_t cnt = *ptr++;
        uint32_t mask = (1u << bits) - 1;
        uint32_t peeked = br_peek(reader, bits) & mask;
        uint16_t i;
        for (i = 0; i < cnt; i++) {
            if (peeked == ptr[i * 2]) {
                br_consume(reader, bits);
                return (int)ptr[i * 2 + 1];
            }
        }
        ptr += cnt * 2;
    }
    return -1;
}

DFL_INLINE int decode_symbol(dfl_br *reader, const dfl_huff *table) {
    uint32_t idx;
    uint32_t entry;
    if (DFL_UNLIKELY(reader->count < 15)) br_refill_fast(reader);
    idx = br_peek(reader, DFL_FAST_BITS);
    entry = table->fast_table[idx];
    if (DFL_LIKELY(entry & DFL_ENTRY_VALID)) {
        br_consume(reader, dfl_entry_code_len(entry, table));
        return dfl_entry_sym(entry);
    }
    if (reader->count >= DFL_MAX_BITS) {
        uint16_t offset = table->long_index[idx];
        if (offset != 0) {
            uint16_t long_entry = table->long_table[
                (offset - 1) |
                ((reader->bits >> DFL_FAST_BITS) & (DFL_LONG_SLOT_SIZE - 1))];
            if (DFL_LIKELY(long_entry & 0x8000)) {
                uint32_t full = dfl_fast_entry((long_entry >> 4) & 0x7FF,
                                                long_entry & 0xF,
                                                table->kind);
                br_consume(reader, dfl_entry_code_len(full, table));
                return (long_entry >> 4) & 0x7FF;
            }
        }
    }
    return decode_symbol_slow(reader, table);
}

DFL_INLINE void copy_match(uint8_t *dst, const uint8_t *src, int length,
                           int distance) {
    (void)src;
    if (DFL_UNLIKELY(length <= 0)) return;
    src = dst - distance;
    if (distance == 1) {
        memset(dst, *src, (size_t)length);
        return;
    }
    if (distance >= length) {
        switch (length) {
            case 1: dst[0] = src[0]; return;
            case 2: dst[0] = src[0]; dst[1] = src[1]; return;
            case 3: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; return;
            case 4: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; dst[3] = src[3]; return;
            case 5: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; dst[3] = src[3];
                    dst[4] = src[4]; return;
            case 6: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; dst[3] = src[3];
                    dst[4] = src[4]; dst[5] = src[5]; return;
            case 7: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; dst[3] = src[3];
                    dst[4] = src[4]; dst[5] = src[5];
                    dst[6] = src[6]; return;
            case 8: dst[0] = src[0]; dst[1] = src[1];
                    dst[2] = src[2]; dst[3] = src[3];
                    dst[4] = src[4]; dst[5] = src[5];
                    dst[6] = src[6]; dst[7] = src[7]; return;
            default: break;
        }
        memcpy(dst, src, (size_t)length);
        return;
    }
    /* When distance >= 8 the 8-byte source window is fully written already, so
     * even self-overlapping LZ copies can advance a word at a time. */
    if (distance >= 8) {
        while (length >= 8) {
            memcpy(dst, src, 8);
            dst += 8;
            src += 8;
            length -= 8;
        }
    }
    while (length-- > 0) *dst++ = *src++;
}

/* The ZIP codec's private scratch buffer has a small validated tail slack.
 * Use it to round the final word copy, avoiding the scalar tail that is
 * otherwise needed for exact-size caller buffers. */
DFL_INLINE void copy_match_slack(uint8_t *dst, int length, int distance) {
    const uint8_t *src = dst - distance;
    size_t rounded = ((size_t)length + 7u) & ~(size_t)7u;

    if (distance == 1) {
        memset(dst, *src, (size_t)length);
        return;
    }
    if (distance < 8) {
        copy_match(dst, src, length, distance);
        return;
    }
    while (rounded >= 40) {
        memcpy(dst, src, 8);
        memcpy(dst + 8, src + 8, 8);
        memcpy(dst + 16, src + 16, 8);
        memcpy(dst + 24, src + 24, 8);
        memcpy(dst + 32, src + 32, 8);
        dst += 40;
        src += 40;
        rounded -= 40;
    }
    while (rounded >= 8) {
        memcpy(dst, src, 8);
        dst += 8;
        src += 8;
        rounded -= 8;
    }
}

static int decode_dynamic_tables(dfl_br *reader, dfl_huff *litlen,
                                 dfl_huff *dist) {
    int hlit, hdist, hclen, total, i;
    uint8_t codelen_lens[DFL_CODELEN_CODES] = {0};
    uint8_t all_lens[DFL_LITLEN_CODES + DFL_DIST_CODES] = {0};
    dfl_huff codelen_table;

    br_refill(reader);
    hlit = (int)br_read(reader, 5) + 257;
    hdist = (int)br_read(reader, 5) + 1;
    hclen = (int)br_read(reader, 4) + 4;
    if (hlit > DFL_LITLEN_CODES || hdist > DFL_DIST_CODES) return 0;

    for (i = 0; i < hclen; i++) {
        if (reader->count < 3) br_refill(reader);
        codelen_lens[dfl_codelen_order[i]] = (uint8_t)br_read(reader, 3);
    }
    if (!ht_build(&codelen_table, codelen_lens, DFL_CODELEN_CODES, 0)) return 0;

    total = hlit + hdist;
    i = 0;
    while (i < total) {
        int sym;
        br_refill(reader);
        sym = decode_symbol(reader, &codelen_table);
        if (sym < 0) return 0;
        if (sym < 16) {
            all_lens[i++] = (uint8_t)sym;
        } else if (sym == 16) {
            int repeat;
            uint8_t prev;
            if (i == 0) return 0;
            repeat = (int)br_read(reader, 2) + 3;
            prev = all_lens[i - 1];
            while (repeat-- > 0 && i < total) all_lens[i++] = prev;
        } else if (sym == 17) {
            int repeat = (int)br_read(reader, 3) + 3;
            while (repeat-- > 0 && i < total) all_lens[i++] = 0;
        } else if (sym == 18) {
            int repeat = (int)br_read(reader, 7) + 11;
            while (repeat-- > 0 && i < total) all_lens[i++] = 0;
        } else {
            return 0;
        }
    }
    if (!ht_build(litlen, all_lens, hlit, 1)) return 0;
    if (!ht_build(dist, all_lens + hlit, hdist, 2)) return 0;
    return 1;
}

/* Fast loop for blocks with enough output room for the longest match.  The
 * exact loop below remains responsible for the final tail and all malformed
 * or truncated cases. */
static int decode_block_fast(dfl_br *reader, const dfl_huff *litlen_t,
                             const dfl_huff *dist_t, uint8_t **out,
                             uint8_t *out_start, uint8_t *out_end) {
    uint64_t bits = reader->bits;
    uint32_t count = (uint32_t)reader->count;
    const uint8_t *ptr = reader->ptr;
    uint8_t *op = *out;
    uint32_t entry;
    int have_entry = 0;
    uint64_t saved_bits = bits;
    uint32_t saved_count = count;
    const uint8_t *saved_ptr = ptr;
    uint8_t *saved_op = op;

    if ((size_t)(out_end - op) < 258) return 2;
    for (;;) {
        int sym, length, extra, dist_sym, distance;
        int consume, code_len;
        uint64_t saved_symbol_bits;
        uint32_t dentry;

        if (!have_entry) {
            br_refill_fast_meta(&bits, &count, &ptr, reader->end);
            if ((uint8_t)count < 15 || (size_t)(out_end - op) < 258) break;
        }
        saved_bits = bits;
        saved_count = count;
        saved_ptr = ptr;
        saved_op = op;
        if (!have_entry &&
            !dfl_lookup_litlen(litlen_t, bits, (uint8_t)count, &entry))
            break;
        have_entry = 0;

        if (entry & DFL_ENTRY_LITERAL) {
            bits >>= entry & 0xFF;
            count -= entry & 0xFF;
            *op++ = (uint8_t)dfl_entry_sym(entry);
            if ((uint8_t)count >= 15) {
                uint32_t next;
                if (!dfl_lookup_litlen(litlen_t, bits, (uint8_t)count, &next))
                    goto fallback;
                if ((next & (DFL_ENTRY_VALID | DFL_ENTRY_LITERAL)) ==
                    (DFL_ENTRY_VALID | DFL_ENTRY_LITERAL)) {
                    bits >>= next & 0xFF;
                    count -= next & 0xFF;
                    *op++ = (uint8_t)dfl_entry_sym(next);
                    if ((uint8_t)count >= 15) {
                        uint32_t next2;
                        if (!dfl_lookup_litlen(litlen_t, bits, (uint8_t)count,
                                               &next2))
                            goto fallback;
                        if ((next2 & (DFL_ENTRY_VALID | DFL_ENTRY_LITERAL)) ==
                            (DFL_ENTRY_VALID | DFL_ENTRY_LITERAL)) {
                            bits >>= next2 & 0xFF;
                            count -= next2 & 0xFF;
                            *op++ = (uint8_t)dfl_entry_sym(next2);
                        } else {
                            entry = next2;
                            have_entry = 1;
                        }
                    }
                } else {
                    entry = next;
                    have_entry = 1;
                }
            }
            continue;
        }
        sym = dfl_entry_sym(entry);
        consume = entry & 0xFF;
        extra = (int)((entry >> 27) & 0x7);
        code_len = consume - extra;
        if ((uint8_t)count < consume)
            br_refill_fast_meta(&bits, &count, &ptr, reader->end);
        if ((uint8_t)count < consume) goto fallback;
        saved_symbol_bits = bits;
        bits >>= consume;
        count -= (uint32_t)consume;
        if (sym == 256) {
            reader->bits = bits;
            reader->count = (int)(uint8_t)count;
            reader->ptr = ptr;
            *out = op;
            return 1;
        }
        if (sym < 257 || sym > 285) break;

        length = (int)((entry >> 18) & 0x1FF);
        if (extra != 0)
            length += (int)((saved_symbol_bits >> code_len) &
                            ((1ULL << extra) - 1));
        if ((uint8_t)count < 15)
            br_refill_fast_meta(&bits, &count, &ptr, reader->end);
        if ((uint8_t)count < 15) goto fallback;
        if (!dfl_lookup_dist(dist_t, bits, (uint8_t)count, &dentry)) goto fallback;
        dist_sym = dfl_entry_sym(dentry);
        if (dist_sym < 0 || dist_sym >= 30) goto fallback;
        {
            uint32_t info = dist_t->distance_info[dist_sym];
            distance = (int)(info & 0x7FFF);
            extra = (int)(info >> 15);
        }
        consume = dentry & 0xFF;
        code_len = consume - extra;
        if (code_len <= 0) goto fallback;
        if ((uint8_t)count < consume)
            br_refill_fast_meta(&bits, &count, &ptr, reader->end);
        if ((uint8_t)count < consume) goto fallback;
        saved_symbol_bits = bits;
        bits >>= consume;
        count -= (uint32_t)consume;
        if (extra != 0)
            distance += (int)((saved_symbol_bits >> code_len) &
                              ((1ULL << extra) - 1));
        if (op - out_start < distance) goto fallback;
        if ((size_t)(out_end - op) < (size_t)length) goto fallback;
        br_refill_fast_meta(&bits, &count, &ptr, reader->end);
        /* Preload the next literal/length entry before starting the match
         * copy.  Its table-load latency can overlap the memory traffic, as in
         * libdeflate's fast loop.  If the tail is too short, leave the exact
         * loop to perform the normal refill and lookup. */
        if ((size_t)(out_end - op) >= 258 && (uint8_t)count >= 15 &&
            dfl_lookup_litlen(litlen_t, bits, (uint8_t)count, &entry))
            have_entry = 1;
        if ((size_t)(out_end - op) >=
            (((size_t)length + 7u) & ~(size_t)7u))
            copy_match_slack(op, length, distance);
        else
            copy_match(op, op - distance, length, distance);
        op += length;
    }

fallback:
    reader->bits = saved_bits;
    reader->count = (int)(uint8_t)saved_count;
    reader->ptr = saved_ptr;
    *out = saved_op;
    return 2;
}

static int decode_block(dfl_br *reader, const dfl_huff *litlen_t,
                        const dfl_huff *dist_t, uint8_t **out,
                        uint8_t *out_start, uint8_t *out_end) {
    /* Keep the hot symbol loop in registers. The reader object is synchronized
     * only when a long-code fallback needs the generic decoder or at block end. */
    uint64_t bits = reader->bits;
    int count = reader->count;
    const uint8_t *ptr = reader->ptr;
    uint8_t *op = *out;
    uint32_t entry;

    for (;;) {
        br_refill_fast_state(&bits, &count, &ptr, reader->end);
        entry = litlen_t->fast_table[
            (uint32_t)(bits & (DFL_FAST_SIZE - 1))];
        while (DFL_LIKELY(count >= 15)) {
            int sym, length, extra, dist_sym, distance, length_sym;
            int code_len;
            const uint8_t *match;
            uint32_t didx;
            uint32_t dentry;

            if (DFL_UNLIKELY(!(entry & DFL_ENTRY_VALID))) break;
            code_len = dfl_entry_code_len(entry, litlen_t);
            bits >>= code_len;
            count -= code_len;
            if (DFL_LIKELY(entry & DFL_ENTRY_LITERAL)) {
                int have_next = 0;
                if (DFL_UNLIKELY(op >= out_end)) return 0;
                *op++ = (uint8_t)dfl_entry_sym(entry);
                /* Literal runs are common after the EXR predictor. Decode one
                 * more fast literal without paying the outer-loop branch and
                 * refill checks. Leave a match/end marker for the normal path. */
                if (DFL_LIKELY(count >= 15)) {
                    uint32_t next = litlen_t->fast_table[
                        (uint32_t)(bits & (DFL_FAST_SIZE - 1))];
                    if (DFL_LIKELY((next & (DFL_ENTRY_VALID |
                                           DFL_ENTRY_LITERAL)) ==
                                   (DFL_ENTRY_VALID | DFL_ENTRY_LITERAL))) {
                        code_len = dfl_entry_code_len(next, litlen_t);
                        bits >>= code_len;
                        count -= code_len;
                        if (DFL_UNLIKELY(op >= out_end)) return 0;
                        *op++ = (uint8_t)dfl_entry_sym(next);
                        if (DFL_LIKELY(count >= 15)) {
                            uint32_t next2 = litlen_t->fast_table[
                                (uint32_t)(bits & (DFL_FAST_SIZE - 1))];
                            if (DFL_LIKELY((next2 & (DFL_ENTRY_VALID |
                                                     DFL_ENTRY_LITERAL)) ==
                                           (DFL_ENTRY_VALID |
                                            DFL_ENTRY_LITERAL))) {
                                code_len = dfl_entry_code_len(next2, litlen_t);
                                bits >>= code_len;
                                count -= code_len;
                                if (DFL_UNLIKELY(op >= out_end)) return 0;
                                *op++ = (uint8_t)dfl_entry_sym(next2);
                            } else {
                                entry = next2;
                                have_next = 1;
                            }
                        }
                    } else {
                        entry = next;
                        have_next = 1;
                    }
                }
                if (DFL_LIKELY(count >= 15) && !have_next)
                    entry = litlen_t->fast_table[
                        (uint32_t)(bits & (DFL_FAST_SIZE - 1))];
                continue;
            }
            sym = dfl_entry_sym(entry);
            if (sym == 256) {
                reader->bits = bits;
                reader->count = count;
                reader->ptr = ptr;
                *out = op;
                return 1;
            }
            length_sym = sym - 257;
            if (DFL_UNLIKELY(length_sym >= 29)) return 0;
            {
                length = (entry >> 18) & 0x1FF;
                extra = (entry >> 27) & 0x7;
            }
            if (extra > 0) {
                if (DFL_UNLIKELY(count < extra))
                    br_refill_fast_state(&bits, &count, &ptr, reader->end);
                length += (int)(bits & ((1ULL << extra) - 1));
                bits >>= extra;
                count -= extra;
            }
            if (DFL_UNLIKELY(count < 15))
                br_refill_fast_state(&bits, &count, &ptr, reader->end);
            didx = (uint32_t)(bits & (DFL_DIST_FAST_SIZE - 1));
            dentry = dist_t->dist_fast_table[didx];
            if (DFL_LIKELY(dentry & DFL_ENTRY_VALID)) {
                dist_sym = dfl_entry_sym(dentry);
                code_len = dfl_entry_code_len(dentry, dist_t);
                bits >>= code_len;
                count -= code_len;
            } else {
                reader->bits = bits;
                reader->count = count;
                reader->ptr = ptr;
                dist_sym = decode_symbol(reader, dist_t);
                bits = reader->bits;
                count = reader->count;
                ptr = reader->ptr;
            }
            if (DFL_UNLIKELY(dist_sym < 0 || dist_sym >= 30)) return 0;
            {
                uint32_t info = dist_t->distance_info[dist_sym];
                distance = info & 0x7FFF;
                extra = (int)(info >> 15);
            }
            if (extra > 0) {
                if (DFL_UNLIKELY(count < extra))
                    br_refill_fast_state(&bits, &count, &ptr, reader->end);
                distance += (int)(bits & ((1ULL << extra) - 1));
                bits >>= extra;
                count -= extra;
            }
            if (DFL_UNLIKELY((size_t)(out_end - op) < (size_t)length))
                return 0;
            if (DFL_UNLIKELY(op - out_start < distance)) return 0;
            match = op - distance;
            br_refill_fast_state(&bits, &count, &ptr, reader->end);
            entry = litlen_t->fast_table[
                (uint32_t)(bits & (DFL_FAST_SIZE - 1))];
            if ((size_t)(out_end - op) >=
                (((size_t)length + 7u) & ~(size_t)7u))
                copy_match_slack(op, length, distance);
            else
                copy_match(op, match, length, distance);
            op += length;
        }

        {
            reader->bits = bits;
            reader->count = count;
            reader->ptr = ptr;
            int sym = decode_symbol(reader, litlen_t);
            bits = reader->bits;
            count = reader->count;
            ptr = reader->ptr;
            if (sym < 0) return 0;
            if (sym < 256) {
                if (DFL_UNLIKELY(op >= out_end)) return 0;
                *op++ = (uint8_t)sym;
            } else if (sym == 256) {
                *out = op;
                return 1;
            } else {
                int length_sym = sym - 257, length, extra, dist_sym, distance;
                const uint8_t *match;
                if (length_sym >= 29) return 0;
                length = dfl_length_base[length_sym];
                extra = dfl_length_extra[length_sym];
                if (extra > 0) {
                    if (count < extra)
                        br_refill_fast_state(&bits, &count, &ptr, reader->end);
                    length += (int)(bits & ((1ULL << extra) - 1));
                    bits >>= extra;
                    count -= extra;
                }
                reader->bits = bits;
                reader->count = count;
                reader->ptr = ptr;
                dist_sym = decode_symbol(reader, dist_t);
                bits = reader->bits;
                count = reader->count;
                ptr = reader->ptr;
                if (dist_sym < 0 || dist_sym >= 30) return 0;
                distance = dfl_dist_base[dist_sym];
                extra = dfl_dist_extra[dist_sym];
                if (extra > 0) {
                    if (count < extra)
                        br_refill_fast_state(&bits, &count, &ptr, reader->end);
                    distance += (int)(bits & ((1ULL << extra) - 1));
                    bits >>= extra;
                    count -= extra;
                }
                if (DFL_UNLIKELY((size_t)(out_end - op) < (size_t)length))
                    return 0;
                if (DFL_UNLIKELY(op - out_start < distance)) return 0;
                match = op - distance;
                copy_match(op, match, length, distance);
                op += length;
            }
        }
    }
}

static int inflate_raw(const uint8_t *src, size_t src_len, uint8_t *dst,
                       size_t *dst_len) {
    dfl_br reader;
    dfl_huff fixed_litlen, fixed_dist;
    int fixed_ready = 0;
    uint8_t *out = dst, *out_end = dst + *dst_len;
    int final_block = 0;

    br_init(&reader, src, src_len);
    /* The fixed Huffman tables are built lazily: zlib emits dynamic-Huffman
     * blocks almost exclusively, so building these on every call (and every
     * block) was pure overhead. Construct them only when a BTYPE=1 block is
     * actually encountered, then reuse for the rest of the stream. */

    while (!final_block) {
        int block_type;
        br_refill(&reader);
        final_block = br_read(&reader, 1) != 0;
        block_type = (int)br_read(&reader, 2);

        if (block_type == 0) {
            uint16_t len, nlen;
            int i;
            br_align(&reader);
            if (reader.count < 32) br_refill(&reader);
            len = (uint16_t)br_read(&reader, 16);
            nlen = (uint16_t)br_read(&reader, 16);
            if ((len ^ nlen) != 0xFFFF) return 0;
            if (out + len > out_end) return 0;
            for (i = 0; i < len; i++) {
                if (reader.count < 8) br_refill(&reader);
                if (reader.count < 8) return 0;
                *out++ = (uint8_t)br_read(&reader, 8);
            }
        } else if (block_type == 1) {
            if (!fixed_ready) {
                ht_fixed_litlen(&fixed_litlen);
                ht_fixed_dist(&fixed_dist);
                fixed_ready = 1;
            }
            {
                int fast = decode_block_fast(&reader, &fixed_litlen,
                                             &fixed_dist, &out, dst, out_end);
                if (fast == 0) return 0;
                if (fast == 2 &&
                    !decode_block(&reader, &fixed_litlen, &fixed_dist, &out,
                                  dst, out_end))
                    return 0;
            }
        } else if (block_type == 2) {
            dfl_huff dyn_litlen, dyn_dist;
            if (!decode_dynamic_tables(&reader, &dyn_litlen, &dyn_dist)) return 0;
            {
                int fast = decode_block_fast(&reader, &dyn_litlen, &dyn_dist,
                                             &out, dst, out_end);
                if (fast == 0) return 0;
                if (fast == 2 &&
                    !decode_block(&reader, &dyn_litlen, &dyn_dist, &out, dst,
                                  out_end))
                    return 0;
            }
        } else {
            return 0;
        }
    }
    *dst_len = (size_t)(out - dst);
    return 1;
}

exr_result exr_inflate_zlib(const uint8_t *src, size_t src_size, uint8_t *dst,
                            size_t dst_cap, size_t *out_size) {
    uint8_t cmf, flg;
    size_t len;
    uint32_t expected;
    if (out_size) *out_size = 0;
    if (src_size < 6) return EXR_ERROR_CORRUPT;
    cmf = src[0];
    flg = src[1];
    if ((cmf & 0x0F) != 8 || (cmf >> 4) > 7) return EXR_ERROR_CORRUPT;
    if ((((uint32_t)cmf << 8) | flg) % 31 != 0) return EXR_ERROR_CORRUPT;
    /* No dictionary is supplied by the EXR codecs. */
    if (flg & 0x20) return EXR_ERROR_CORRUPT;
    len = dst_cap;
    if (!inflate_raw(src + 2, src_size - 6, dst, &len))
        return EXR_ERROR_CORRUPT;
    expected = ((uint32_t)src[src_size - 4] << 24) |
               ((uint32_t)src[src_size - 3] << 16) |
               ((uint32_t)src[src_size - 2] << 8) |
               (uint32_t)src[src_size - 1];
    if (exr_adler32(dst, len, 1) != expected) return EXR_ERROR_CORRUPT;
    if (out_size) *out_size = len;
    return EXR_SUCCESS;
}

/* ===========================================================================
 * DEFLATE encoder
 *
 * The Huffman table construction and dynamic-block header emission are ported
 * from fpng (Richard Geldreich, Jr.) - public domain / Unlicense; those routines
 * in turn derive from the 2011 public-domain miniz and the minimum-redundancy
 * code-length function by Alistair Moffat & Jyrki Katajainen (1996, public
 * domain). The LZ77 match finder and the generic (non-PNG) token emitter are
 * original to TinyEXR. See the top-level NOTICE file.
 * ========================================================================= */


uint32_t exr_adler32(const uint8_t *data, size_t n, uint32_t adler) {
    uint32_t s1 = adler & 0xffff, s2 = (adler >> 16) & 0xffff;
    while (n) {
        size_t block = n > 5552 ? 5552 : n;
        n -= block;
        while (block--) {
            s1 += *data++;
            s2 += s1;
        }
        s1 %= 65521;
        s2 %= 65521;
    }
    return (s2 << 16) | s1;
}

/* --- bit writer (LSB-first) --- */
typedef struct {
    uint8_t *dst;
    size_t cap, ofs;
    uint64_t buf;
    int bits;
    int err;
} bitw;

static void bw_put(bitw *w, uint32_t val, int n) {
    w->buf |= ((uint64_t)val) << w->bits;
    w->bits += n;
    while (w->bits >= 8) {
        if (w->ofs >= w->cap) { w->err = 1; w->bits = 0; return; }
        w->dst[w->ofs++] = (uint8_t)w->buf;
        w->buf >>= 8;
        w->bits -= 8;
    }
}
static void bw_flush(bitw *w) {
    while (w->bits > 0) {
        if (w->ofs >= w->cap) { w->err = 1; return; }
        w->dst[w->ofs++] = (uint8_t)w->buf;
        w->buf >>= 8;
        w->bits -= 8;
    }
    w->bits = 0;
    w->buf = 0;
}

/* --- fpng Huffman table construction --- */
#define DEFL_MAX_HUFF_TABLES 3
#define DEFL_MAX_HUFF_SYMBOLS 288
#define DEFL_MAX_HUFF_SYMBOLS_0 288
#define DEFL_MAX_HUFF_SYMBOLS_1 32
#define DEFL_MAX_HUFF_SYMBOLS_2 19
#define DEFL_MAX_SUPPORTED_HUFF_CODESIZE 32

typedef struct {
    uint16_t count[DEFL_MAX_HUFF_TABLES][DEFL_MAX_HUFF_SYMBOLS];
    uint16_t codes[DEFL_MAX_HUFF_TABLES][DEFL_MAX_HUFF_SYMBOLS];
    uint8_t sizes[DEFL_MAX_HUFF_TABLES][DEFL_MAX_HUFF_SYMBOLS];
} defl_huff;

typedef struct {
    uint16_t key;
    uint16_t sym;
} sym_freq;

static sym_freq *radix_sort_syms(uint32_t num, sym_freq *a, sym_freq *b) {
    uint32_t passes = 2, shift, pass, i, hist[256 * 2];
    sym_freq *cur = a, *nw = b;
    memset(hist, 0, sizeof(hist));
    for (i = 0; i < num; ++i) {
        uint32_t f = a[i].key;
        hist[f & 0xff]++;
        hist[256 + ((f >> 8) & 0xff)]++;
    }
    while ((passes > 1) && (num == hist[(passes - 1) * 256])) passes--;
    for (shift = 0, pass = 0; pass < passes; pass++, shift += 8) {
        const uint32_t *ph = &hist[pass << 8];
        uint32_t ofs[256], cofs = 0;
        sym_freq *t;
        for (i = 0; i < 256; ++i) { ofs[i] = cofs; cofs += ph[i]; }
        for (i = 0; i < num; ++i) nw[ofs[(cur[i].key >> shift) & 0xff]++] = cur[i];
        t = cur; cur = nw; nw = t;
    }
    return cur;
}

static void calc_min_redundancy(sym_freq *A, int n) {
    int root, leaf, next, avbl, used, dpth;
    if (n == 0) return;
    if (n == 1) { A[0].key = 1; return; }
    A[0].key = (uint16_t)(A[0].key + A[1].key);
    root = 0; leaf = 2;
    for (next = 1; next < n - 1; ++next) {
        if (leaf >= n || A[root].key < A[leaf].key) {
            A[next].key = A[root].key;
            A[root++].key = (uint16_t)next;
        } else
            A[next].key = A[leaf++].key;
        if (leaf >= n || (root < next && A[root].key < A[leaf].key)) {
            A[next].key = (uint16_t)(A[next].key + A[root].key);
            A[root++].key = (uint16_t)next;
        } else
            A[next].key = (uint16_t)(A[next].key + A[leaf++].key);
    }
    A[n - 2].key = 0;
    for (next = n - 3; next >= 0; --next) A[next].key = (uint16_t)(A[A[next].key].key + 1);
    avbl = 1; used = dpth = 0; root = n - 2; next = n - 1;
    while (avbl > 0) {
        while (root >= 0 && (int)A[root].key == dpth) { used++; root--; }
        while (avbl > used) { A[next--].key = (uint16_t)dpth; avbl--; }
        avbl = 2 * used; dpth++; used = 0;
    }
}

static void enforce_max_code_size(int *num_codes, int len, int max_size) {
    int i;
    uint32_t total = 0;
    if (len <= 1) return;
    for (i = max_size + 1; i <= DEFL_MAX_SUPPORTED_HUFF_CODESIZE; ++i)
        num_codes[max_size] += num_codes[i];
    for (i = max_size; i > 0; --i) total += ((uint32_t)num_codes[i]) << (max_size - i);
    while (total != (1UL << max_size)) {
        num_codes[max_size]--;
        for (i = max_size - 1; i > 0; --i)
            if (num_codes[i]) { num_codes[i]--; num_codes[i + 1] += 2; break; }
        total--;
    }
}

static void optimize_huffman_table(defl_huff *d, int tab, int tlen, int limit,
                                   int static_table) {
    int i, j, l, num_codes[1 + DEFL_MAX_SUPPORTED_HUFF_CODESIZE];
    uint32_t next_code[DEFL_MAX_SUPPORTED_HUFF_CODESIZE + 1];
    memset(num_codes, 0, sizeof(num_codes));
    if (static_table) {
        for (i = 0; i < tlen; ++i) num_codes[d->sizes[tab][i]]++;
    } else {
        sym_freq syms0[DEFL_MAX_HUFF_SYMBOLS], syms1[DEFL_MAX_HUFF_SYMBOLS], *ps;
        int used = 0;
        for (i = 0; i < tlen; ++i)
            if (d->count[tab][i]) {
                syms0[used].key = d->count[tab][i];
                syms0[used++].sym = (uint16_t)i;
            }
        ps = radix_sort_syms((uint32_t)used, syms0, syms1);
        calc_min_redundancy(ps, used);
        for (i = 0; i < used; ++i) num_codes[ps[i].key]++;
        enforce_max_code_size(num_codes, used, limit);
        memset(d->sizes[tab], 0, sizeof(d->sizes[tab]));
        memset(d->codes[tab], 0, sizeof(d->codes[tab]));
        for (i = 1, j = used; i <= limit; ++i)
            for (l = num_codes[i]; l > 0; --l) d->sizes[tab][ps[--j].sym] = (uint8_t)i;
    }
    next_code[1] = 0;
    for (j = 0, i = 2; i <= limit; ++i) next_code[i] = j = ((j + num_codes[i - 1]) << 1);
    for (i = 0; i < tlen; ++i) {
        uint32_t rev = 0, code, cs;
        if ((cs = d->sizes[tab][i]) == 0) continue;
        code = next_code[cs]++;
        for (l = cs; l > 0; --l, code >>= 1) rev = (rev << 1) | (code & 1);
        d->codes[tab][i] = (uint16_t)rev;
    }
}

static const uint8_t g_swizzle[19] = {16, 17, 18, 0, 8, 7, 9,  6, 10, 5,
                                      11, 4, 12, 3, 13, 2, 14, 1, 15};

/* Emit BTYPE=dynamic header + packed code lengths. Returns 1 on success. */
static int start_dynamic_block(defl_huff *d, bitw *w) {
    int num_lit, num_dist, num_bl, i;
    uint8_t cstp[DEFL_MAX_HUFF_SYMBOLS_0 + DEFL_MAX_HUFF_SYMBOLS_1];
    uint8_t packed[DEFL_MAX_HUFF_SYMBOLS_0 + DEFL_MAX_HUFF_SYMBOLS_1];
    int total, npacked = 0, rle_z = 0, rle_r = 0, prev = 0xff, idx;

    d->count[0][256] = 1;
    optimize_huffman_table(d, 0, DEFL_MAX_HUFF_SYMBOLS_0, 12, 0);
    optimize_huffman_table(d, 1, DEFL_MAX_HUFF_SYMBOLS_1, 12, 0);

    for (num_lit = 286; num_lit > 257; --num_lit) if (d->sizes[0][num_lit - 1]) break;
    for (num_dist = 30; num_dist > 1; --num_dist) if (d->sizes[1][num_dist - 1]) break;

    memcpy(cstp, &d->sizes[0][0], (size_t)num_lit);
    memcpy(cstp + num_lit, &d->sizes[1][0], (size_t)num_dist);
    total = num_lit + num_dist;
    memset(&d->count[2][0], 0, sizeof(uint16_t) * DEFL_MAX_HUFF_SYMBOLS_2);

#define RLE_PREV()                                                            \
    do {                                                                      \
        if (rle_r) {                                                          \
            if (rle_r < 3) {                                                  \
                d->count[2][prev] = (uint16_t)(d->count[2][prev] + rle_r);    \
                while (rle_r--) packed[npacked++] = (uint8_t)prev;            \
            } else {                                                          \
                d->count[2][16]++;                                            \
                packed[npacked++] = 16;                                       \
                packed[npacked++] = (uint8_t)(rle_r - 3);                     \
            }                                                                 \
            rle_r = 0;                                                        \
        }                                                                     \
    } while (0)
#define RLE_ZERO()                                                            \
    do {                                                                      \
        if (rle_z) {                                                          \
            if (rle_z < 3) {                                                  \
                d->count[2][0] = (uint16_t)(d->count[2][0] + rle_z);          \
                while (rle_z--) packed[npacked++] = 0;                        \
            } else if (rle_z <= 10) {                                         \
                d->count[2][17]++;                                            \
                packed[npacked++] = 17;                                       \
                packed[npacked++] = (uint8_t)(rle_z - 3);                     \
            } else {                                                          \
                d->count[2][18]++;                                            \
                packed[npacked++] = 18;                                       \
                packed[npacked++] = (uint8_t)(rle_z - 11);                    \
            }                                                                 \
            rle_z = 0;                                                        \
        }                                                                     \
    } while (0)

    for (i = 0; i < total; ++i) {
        uint8_t cs = cstp[i];
        if (!cs) {
            RLE_PREV();
            if (++rle_z == 138) RLE_ZERO();
        } else {
            RLE_ZERO();
            if (cs != prev) {
                RLE_PREV();
                d->count[2][cs]++;
                packed[npacked++] = cs;
            } else if (++rle_r == 6) {
                RLE_PREV();
            }
        }
        prev = cs;
    }
    if (rle_r) RLE_PREV(); else RLE_ZERO();
#undef RLE_PREV
#undef RLE_ZERO

    optimize_huffman_table(d, 2, DEFL_MAX_HUFF_SYMBOLS_2, 7, 0);

    bw_put(w, 2, 2); /* BTYPE = 2 (dynamic); BFINAL emitted by caller */
    bw_put(w, (uint32_t)(num_lit - 257), 5);
    bw_put(w, (uint32_t)(num_dist - 1), 5);

    for (num_bl = 18; num_bl >= 0; --num_bl)
        if (d->sizes[2][g_swizzle[num_bl]]) break;
    num_bl = (num_bl + 1 < 4) ? 4 : (num_bl + 1);
    bw_put(w, (uint32_t)(num_bl - 4), 4);
    for (i = 0; i < num_bl; ++i) bw_put(w, d->sizes[2][g_swizzle[i]], 3);

    for (idx = 0; idx < npacked;) {
        uint32_t code = packed[idx++];
        bw_put(w, d->codes[2][code], d->sizes[2][code]);
        if (code >= 16) {
            static const int ex[3] = {2, 3, 7};
            bw_put(w, packed[idx++], ex[code - 16]);
        }
    }
    return !w->err;
}

/* --- LZ77 (greedy hash-chain) --- */
#define ENC_MIN_MATCH 3
#define ENC_MAX_MATCH 258
#define ENC_WIN 32768
#define ENC_HASH_SIZE (1 << 15)
/* Hash-chain probe depth and "good enough" match length. These trade ratio for
 * speed; the values below target libdeflate level-4-ish throughput (the codec
 * still emits valid DEFLATE, so correctness is unaffected). */
#define ENC_MAX_CHAIN 6
#define ENC_NICE_LEN 32

/* Length of the common prefix of s1[0..maxlen) and s2[0..maxlen), compared a
 * machine word at a time (the dominant cost of the LZ parse). */
DFL_INLINE size_t enc_match_len(const uint8_t *s1, const uint8_t *s2,
                                size_t maxlen) {
    size_t l = 0;
#if defined(__GNUC__) || defined(__clang__)
    while (l + 8 <= maxlen) {
        uint64_t a, b, z;
        memcpy(&a, s1 + l, 8);
        memcpy(&b, s2 + l, 8);
        z = a ^ b;
        if (z) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
            return l + (size_t)(__builtin_clzll(z) >> 3);
#else
            return l + (size_t)(__builtin_ctzll(z) >> 3);
#endif
        }
        l += 8;
    }
#endif
    while (l < maxlen && s1[l] == s2[l]) ++l;
    return l;
}

static int len_code(int L) {
    if (L < 11) return L - 3;
    if (L < 19) return 8 + ((L - 11) >> 1);
    if (L < 35) return 12 + ((L - 19) >> 2);
    if (L < 67) return 16 + ((L - 35) >> 3);
    if (L < 131) return 20 + ((L - 67) >> 4);
    if (L < 258) return 24 + ((L - 131) >> 5);
    return 28;
}
static int dist_code(int D) {
    int msb;
    if (D < 5) return D - 1;
#if defined(__GNUC__) || defined(__clang__)
    msb = 31 - __builtin_clz((unsigned int)D);
#else
    msb = 0;
    while ((1u << (msb + 1)) <= (unsigned int)D) ++msb;
#endif
    {
        int base = 1 << msb;
        if (D == base) return (msb << 1) - 1;
        return (msb << 1) + (D > base + (base >> 1));
    }
}

typedef struct {
    uint16_t len; /* 0 => literal */
    uint16_t dist;
} tok;

/* 4-byte multiplicative hash -> top `hbits` bits (Fibonacci hashing). Higher
 * quality than the old 3-byte xor, so fewer chain probes are wasted. */
DFL_INLINE uint32_t enc_hash(const uint8_t *p, int shift) {
    uint32_t v;
    memcpy(&v, p, 4);
    return (v * 2654435761u) >> shift;
}

/* Produce token list for src[0..n). Returns token count, or (size_t)-1. */
static size_t lz_parse(const exr_allocator *a, const uint8_t *src, size_t n,
                       tok *toks) {
    int32_t *head = NULL, *prev = NULL;
    size_t i = 0, ntok = 0;
    int32_t k;
    /* Size the hash table to the block (avoids memset'ing a full table for the
     * tiny blocks ZIPS produces). hbits in [10,17]; shift selects the top bits. */
    int hbits = 10;
    size_t hsize;
    int shift;
    while (hbits < 17 && ((size_t)1 << hbits) < n) ++hbits;
    hsize = (size_t)1 << hbits;
    shift = 32 - hbits;

    head = (int32_t *)exr_malloc(a, sizeof(int32_t) * hsize);
    prev = (int32_t *)exr_malloc(a, sizeof(int32_t) * (n ? n : 1));
    if (!head || !prev) {
        exr_free(a, head);
        exr_free(a, prev);
        return (size_t)-1;
    }
    for (k = 0; k < (int32_t)hsize; ++k) head[k] = -1;

    while (i < n) {
        size_t best_len = 0, best_dist = 0;
        if (i + 4 <= n) {
            uint32_t h = enc_hash(src + i, shift);
            int32_t cand = head[h];
            int chain = ENC_MAX_CHAIN;
            size_t maxlen = n - i;
            if (maxlen > ENC_MAX_MATCH) maxlen = ENC_MAX_MATCH;
            while (cand >= 0 && chain-- > 0) {
                size_t d = i - (size_t)cand;
                if (d > ENC_WIN) break;
                /* quick reject: only extend when the byte past the current best
                 * match already agrees (cheap filter before the word compare). */
                if (src[(size_t)cand + best_len] == src[i + best_len]) {
                    size_t l = enc_match_len(src + (size_t)cand, src + i, maxlen);
                    if (l > best_len) {
                        best_len = l;
                        best_dist = d;
                        if (l >= maxlen || l >= ENC_NICE_LEN) break;
                    }
                }
                cand = prev[cand];
            }
            /* insert current position */
            prev[i] = head[h];
            head[h] = (int32_t)i;
        }

        if (best_len >= ENC_MIN_MATCH) {
            toks[ntok].len = (uint16_t)best_len;
            toks[ntok].dist = (uint16_t)best_dist;
            ntok++;
            /* insert hashes for the covered bytes (skip the first, inserted) */
            {
                size_t j;
                for (j = 1; j < best_len; ++j) {
                    if (i + j + 4 <= n) {
                        uint32_t h2 = enc_hash(src + i + j, shift);
                        prev[i + j] = head[h2];
                        head[h2] = (int32_t)(i + j);
                    }
                }
            }
            i += best_len;
        } else {
            toks[ntok].len = 0;
            toks[ntok].dist = src[i];
            ntok++;
            i++;
        }
    }
    exr_free(a, head);
    exr_free(a, prev);
    return ntok;
}

exr_result exr_deflate_zlib(const exr_allocator *a, const uint8_t *src,
                            size_t n, uint8_t **out_data, size_t *out_size) {
    tok *toks = NULL;
    size_t ntok, t, cap;
    defl_huff *d = NULL;
    bitw w;
    uint8_t *out = NULL;
    uint32_t adler;

    *out_data = NULL;
    *out_size = 0;

    /* worst case: literals + headers + zlib framing */
    cap = n + n / 2 + 512;
    out = (uint8_t *)exr_malloc(a, cap);
    toks = (tok *)exr_malloc(a, sizeof(tok) * (n ? n : 1));
    d = (defl_huff *)exr_calloc(a, 1, sizeof(defl_huff));
    if (!out || !toks || !d) {
        exr_free(a, out);
        exr_free(a, toks);
        exr_free(a, d);
        return EXR_ERROR_OUT_OF_MEMORY;
    }

    ntok = lz_parse(a, src, n, toks);
    if (ntok == (size_t)-1) {
        exr_free(a, out);
        exr_free(a, toks);
        exr_free(a, d);
        return EXR_ERROR_OUT_OF_MEMORY;
    }

    /* frequency counts */
    for (t = 0; t < ntok; ++t) {
        if (toks[t].len == 0) {
            d->count[0][toks[t].dist]++;
        } else {
            d->count[0][257 + len_code(toks[t].len)]++;
            d->count[1][dist_code(toks[t].dist)]++;
        }
    }
    /* guarantee at least one distance code so the header is always valid */
    {
        int any = 0, c;
        for (c = 0; c < 30; ++c) if (d->count[1][c]) { any = 1; break; }
        if (!any) d->count[1][0] = 1;
    }

    /* zlib header */
    out[0] = 0x78;
    out[1] = 0x01;
    w.dst = out;
    w.cap = cap;
    w.ofs = 2;
    w.buf = 0;
    w.bits = 0;
    w.err = 0;

    bw_put(&w, 1, 1); /* BFINAL = 1 (single block) */
    if (!start_dynamic_block(d, &w)) goto fail;

    for (t = 0; t < ntok; ++t) {
        if (toks[t].len == 0) {
            int s = toks[t].dist;
            bw_put(&w, d->codes[0][s], d->sizes[0][s]);
        } else {
            int L = toks[t].len, D = toks[t].dist;
            int lc = len_code(L), dc = dist_code(D);
            int s = 257 + lc;
            bw_put(&w, d->codes[0][s], d->sizes[0][s]);
            if (dfl_length_extra[lc])
                bw_put(&w, (uint32_t)(L - dfl_length_base[lc]), dfl_length_extra[lc]);
            bw_put(&w, d->codes[1][dc], d->sizes[1][dc]);
            if (dfl_dist_extra[dc])
                bw_put(&w, (uint32_t)(D - dfl_dist_base[dc]), dfl_dist_extra[dc]);
        }
        if (w.err) goto fail;
    }
    bw_put(&w, d->codes[0][256], d->sizes[0][256]); /* EOB */
    bw_flush(&w);
    if (w.err) goto fail;

    adler = exr_adler32(src, n, 1);
    if (w.ofs + 4 > cap) goto fail;
    out[w.ofs++] = (uint8_t)(adler >> 24);
    out[w.ofs++] = (uint8_t)(adler >> 16);
    out[w.ofs++] = (uint8_t)(adler >> 8);
    out[w.ofs++] = (uint8_t)(adler);

    exr_free(a, toks);
    exr_free(a, d);
    *out_data = out;
    *out_size = w.ofs;
    return EXR_SUCCESS;

fail:
    exr_free(a, out);
    exr_free(a, toks);
    exr_free(a, d);
    return EXR_ERROR_CORRUPT;
}
