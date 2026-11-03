/*
 * TinyEXR - bounded range input and resumable source operations.
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include "exr_internal.h"

#define INPUT_REQUEST_MAX 65536u

static exr_result input_reserve(exr_reader *r, exr_input_buffer *b, size_t n) {
    uint8_t *p;
    if (n <= b->capacity) return EXR_SUCCESS;
    if (r->have_pending && r->pending_buffer == b)
        return EXR_ERROR_INVALID_ARGUMENT;
    if (b == &r->prefix) {
        size_t cap = b->capacity ? b->capacity : 4096;
        uint64_t limit = exr_context_max_header_bytes(r->context);
        while (cap < n && cap <= SIZE_MAX / 2) cap *= 2;
        if (cap < n) cap = n;
        if (limit && (uint64_t)cap > limit) cap = (size_t)limit;
        if ((uint64_t)cap > r->file_size) cap = (size_t)r->file_size;
        n = cap;
    }
    p = (uint8_t *)exr_malloc(&r->alloc, n ? n : 1);
    if (!p) return EXR_ERROR_OUT_OF_MEMORY;
    if (b->size) memcpy(p, b->data, b->size);
    exr_free(&r->alloc, b->data);
    b->data = p; b->capacity = n;
    return EXR_SUCCESS;
}

static exr_result input_fill(exr_reader *r, exr_input_buffer *b, size_t n) {
    exr_result rc;
    if (r->have_pending) return r->pending_buffer == b ? EXR_WOULD_BLOCK
                                                       : EXR_ERROR_INVALID_ARGUMENT;
    if (b->offset > r->file_size || (uint64_t)n > r->file_size - b->offset)
        return EXR_ERROR_CORRUPT;
    rc = input_reserve(r, b, n ? n : 1);
    if (rc != EXR_SUCCESS) return rc;
    b->target = n;
    while (b->size < n) {
        size_t len = n - b->size;
        if (len > INPUT_REQUEST_MAX) len = INPUT_REQUEST_MAX;
        rc = r->src.read(r->src.user, b->offset + b->size, len, b->data + b->size);
        if (rc == EXR_WOULD_BLOCK) {
            r->have_pending = 1; r->pending_buffer = b;
            r->pending.offset = b->offset + b->size; r->pending.size = len;
            return rc;
        }
        if (rc != EXR_SUCCESS) return rc;
        b->size += len;
    }
    return EXR_SUCCESS;
}

exr_result exr_source_prefix(exr_reader *r, size_t needed) {
    exr_result rc;
    uint64_t limit = exr_context_max_header_bytes(r->context);
    size_t target = needed;
    if (limit && (uint64_t)needed > limit) return EXR_ERROR_LIMIT_EXCEEDED;
    if ((uint64_t)needed > r->file_size) return EXR_ERROR_CORRUPT;
    if (r->have_pending && r->pending_buffer == &r->prefix) return EXR_WOULD_BLOCK;
    if (r->prefix.size >= needed) return EXR_SUCCESS;
    /* Read ahead only a small metadata window, never a file-sized allocation. */
    if (needed <= SIZE_MAX - 4095u) target = (needed + 4095u) & ~(size_t)4095u;
    if ((uint64_t)target > r->file_size) target = (size_t)r->file_size;
    if (limit && (uint64_t)target > limit) target = (size_t)limit;
    rc = input_fill(r, &r->prefix, target);
    r->mem = r->prefix.data; r->mem_size = r->prefix.size;
    return rc;
}

exr_result exr_source_headers(exr_reader *r) {
    exr_result rc;
    for (;;) {
        size_t need = r->scan_pos;
        uint8_t c;
        if (r->scan_state == 6) return EXR_SUCCESS;
        if (r->scan_state == 0) need = 8;
        else if (r->scan_state == 3) {
            if (exr_add_ovf(need, 4, &need)) return EXR_ERROR_CORRUPT;
        } else if (r->scan_state == 4) {
            if (exr_add_ovf(need, r->scan_payload, &need)) return EXR_ERROR_CORRUPT;
        } else if (exr_add_ovf(need, 1, &need)) return EXR_ERROR_CORRUPT;
        rc = exr_source_prefix(r, need);
        if (rc != EXR_SUCCESS) return rc;
        if (r->scan_state == 0) {
            uint32_t ver = exr_rd_u32(r->mem + 4);
            if (exr_rd_u32(r->mem) != EXR_MAGIC || !(ver & 255u))
                return EXR_ERROR_INVALID_FILE;
            if ((ver & 255u) > EXR_VERSION_NUMBER ||
                (ver & ~(255u | EXR_VERSION_FLAG_TILED | EXR_VERSION_FLAG_LONG_NAMES |
                         EXR_VERSION_FLAG_NON_IMAGE | EXR_VERSION_FLAG_MULTIPART)))
                return EXR_ERROR_UNSUPPORTED;
            r->is_multipart = !!(ver & EXR_VERSION_FLAG_MULTIPART);
            r->scan_pos = 8; r->scan_state = 1; r->scan_length = 0;
        } else if (r->scan_state == 3) {
            int32_t sz = exr_rd_i32(r->mem + r->scan_pos);
            if (sz < 0 || (uint32_t)sz > EXR_MAX_ATTR_SIZE) return EXR_ERROR_CORRUPT;
            r->scan_payload = (uint32_t)sz; r->scan_pos += 4; r->scan_state = 4;
        } else if (r->scan_state == 4) {
            r->scan_pos = need; r->scan_state = 1; r->scan_length = 0;
        } else {
            c = r->mem[r->scan_pos++];
            if (r->scan_state == 5) {
                if (!c) r->scan_state = 6;
                else { r->scan_state = 1; r->scan_length = 1; }
            } else if (c) {
                if (++r->scan_length >= EXR_MAX_NAME) return EXR_ERROR_CORRUPT;
            } else if (r->scan_state == 1) {
                r->scan_state = r->scan_length ? 2 : (r->is_multipart ? 5 : 6);
                r->scan_length = 0;
            } else {
                if (!r->scan_length) return EXR_ERROR_CORRUPT;
                r->scan_state = 3; r->scan_length = 0;
            }
        }
    }
}

exr_result exr_source_select(exr_reader *r, int32_t part, uint32_t index) {
    int i;
    if (r->kind != EXR_SRC_CALLBACK) return EXR_SUCCESS;
    if (r->active_chunk && r->active_part == part && r->active_index == index)
        return EXR_SUCCESS;
    if (r->have_pending) return EXR_ERROR_INVALID_ARGUMENT;
    for (i = 0; i < 3; ++i) {
        r->ranges[i].size = 0; r->ranges[i].target = 0; r->ranges[i].stamp = 0;
    }
    r->active_chunk = 1; r->active_part = part; r->active_index = index;
    return EXR_SUCCESS;
}

exr_result exr_reader_fetch(exr_reader *r, uint64_t offset, size_t size,
                            void *scratch, const uint8_t **out_ptr) {
    exr_input_buffer *b = NULL;
    exr_result rc;
    int i;
    (void)scratch;
    if (!r || !out_ptr) return EXR_ERROR_INVALID_ARGUMENT;
    if (offset > r->file_size || (uint64_t)size > r->file_size - offset)
        return EXR_ERROR_CORRUPT;
    if (r->kind == EXR_SRC_CHUNK) {
        if (offset < r->source_base || offset - r->source_base > r->mem_size ||
            size > r->mem_size - (size_t)(offset - r->source_base))
            return EXR_ERROR_CORRUPT;
        *out_ptr = r->mem + (size_t)(offset - r->source_base);
        return EXR_SUCCESS;
    }
    if (r->kind == EXR_SRC_MEMORY) {
        *out_ptr = r->mem + (size_t)offset; return EXR_SUCCESS;
    }
    for (i = 0; i < 3; ++i) {
        exr_input_buffer *v = &r->ranges[i];
        if (v->stamp && v->offset == offset && v->target == size) { b = v; break; }
    }
    if (!b) {
        if (r->have_pending) return EXR_ERROR_INVALID_ARGUMENT;
        b = &r->ranges[0];
        for (i = 1; i < 3; ++i)
            if (r->ranges[i].stamp < b->stamp) b = &r->ranges[i];
        b->offset = offset; b->size = 0; b->target = size;
    }
    b->stamp = ++r->input_clock;
    if (b->size < size || !b->data) {
        rc = input_fill(r, b, size);
        if (rc != EXR_SUCCESS) return rc;
    }
    *out_ptr = b->data;
    return EXR_SUCCESS;
}

exr_result exr_reader_pending(const exr_reader *r, exr_pending_read *out) {
    if (!r || !out) return EXR_ERROR_INVALID_ARGUMENT;
    if (r->parse_done && r->parse_rc != EXR_SUCCESS) return r->parse_rc;
    if (!r->have_pending) return EXR_ERROR_INVALID_ARGUMENT;
    *out = r->pending; return EXR_SUCCESS;
}

exr_result exr_reader_supply(exr_reader *r, uint64_t offset,
                             const void *data, size_t size) {
    exr_input_buffer *b;
    if (!r || !data || !size) return EXR_ERROR_INVALID_ARGUMENT;
    if (r->parse_done && r->parse_rc != EXR_SUCCESS) return r->parse_rc;
    if (!r->have_pending || offset != r->pending.offset || size > r->pending.size)
        return EXR_ERROR_INVALID_ARGUMENT;
    b = r->pending_buffer;
    if (!b || b->size > b->capacity || size > b->capacity - b->size)
        return EXR_ERROR_INVALID_ARGUMENT;
    memcpy(b->data + b->size, data, size); b->size += size;
    r->pending.offset += size; r->pending.size -= size;
    if (!r->pending.size) { r->have_pending = 0; r->pending_buffer = NULL; }
    if (b == &r->prefix) { r->mem = b->data; r->mem_size = b->size; }
    return EXR_SUCCESS;
}

void exr_source_free(exr_reader *r) {
    int i;
    exr_free(&r->alloc, r->prefix.data);
    for (i = 0; i < 3; ++i) exr_free(&r->alloc, r->ranges[i].data);
}

/* Reuse a completed batch buffer. No worker or pending request refers to it
 * here; retaining at most the three range slots keeps the input bound intact. */
void exr_source_recycle(exr_reader *r, uint8_t *data, size_t size) {
    exr_input_buffer *b = NULL;
    int i;
    for (i = 0; i < 3; ++i) {
        exr_input_buffer *candidate = &r->ranges[i];
        if (candidate == r->pending_buffer) continue;
        if (!b || candidate->capacity < b->capacity) b = candidate;
    }
    if (!b || b->capacity > size) { exr_free(&r->alloc, data); return; }
    exr_free(&r->alloc, b->data);
    memset(b, 0, sizeof(*b)); b->data = data; b->capacity = size;
}

/* Transfer a complete chunk (or its count prefix) into a private batch job. */
exr_result exr_source_chunk(exr_reader *r, int32_t part, uint32_t index,
                             int counts_only, uint8_t **data, size_t *size) {
    const exr_header *h = &r->parts[part].header;
    int deep = h->part_type == EXR_PART_DEEP_SCANLINE || h->part_type == EXR_PART_DEEP_TILED;
    size_t hsz = deep ? (h->tiled ? 40u : 28u) : (h->tiled ? 20u : 8u);
    uint64_t off = r->parts[part].offsets[index], n, samples = 0;
    const uint8_t *hdr;
    exr_result rc;
    int i;
    if (r->is_multipart) hsz += 4;
    rc = exr_source_select(r, part, index);
    if (rc != EXR_SUCCESS) return rc;
    rc = exr_reader_fetch(r, off, hsz, NULL, &hdr);
    if (rc != EXR_SUCCESS) return rc;
    rc = exr_reader_check_chunk(r, part, index, hdr);
    if (rc != EXR_SUCCESS) return rc;
    if (r->is_multipart) hdr += 4;
    if (deep) {
        n = exr_rd_u64(hdr + (h->tiled ? 16 : 4));
        if (!counts_only) samples = exr_rd_u64(hdr + (h->tiled ? 24 : 12));
    } else {
        int32_t sz = exr_rd_i32(hdr + (h->tiled ? 16 : 4));
        if (sz < 0) return EXR_ERROR_CORRUPT;
        n = (uint32_t)sz;
    }
    if (n > UINT64_MAX - hsz || samples > UINT64_MAX - n - hsz)
        return EXR_ERROR_CORRUPT;
    n += hsz + samples;
    if (off > r->file_size || n > r->file_size - off)
        return EXR_ERROR_CORRUPT;
    if (n > SIZE_MAX) return EXR_ERROR_LIMIT_EXCEEDED;
    /* Preserve the already-read header and append only its payload. This keeps
     * sequential file reads sequential and avoids reading each header twice. */
    {
        exr_input_buffer *buffer = NULL;
        for (i = 0; i < 3; ++i)
            if (r->ranges[i].stamp && r->ranges[i].offset == off &&
                r->ranges[i].target == (size_t)n) { buffer = &r->ranges[i]; break; }
        if (!buffer) {
            if (r->have_pending) return EXR_ERROR_INVALID_ARGUMENT;
            for (i = 0; i < 3; ++i) {
                exr_input_buffer *candidate = &r->ranges[i];
                if (candidate->data == hdr - (r->is_multipart ? 4 : 0)) continue;
                if (!buffer || candidate->stamp < buffer->stamp) buffer = candidate;
            }
            if (!buffer) return EXR_ERROR_CORRUPT;
            buffer->size = 0; buffer->offset = off; buffer->target = (size_t)n;
            rc = input_reserve(r, buffer, (size_t)n);
            if (rc != EXR_SUCCESS) return rc;
            memcpy(buffer->data, hdr - (r->is_multipart ? 4 : 0), hsz);
            buffer->size = hsz;
        }
        buffer->stamp = ++r->input_clock;
        rc = input_fill(r, buffer, (size_t)n);
        if (rc != EXR_SUCCESS) return rc;
        *data = buffer->data; *size = (size_t)n;
        memset(buffer, 0, sizeof(*buffer));
        return EXR_SUCCESS;
    }
}
