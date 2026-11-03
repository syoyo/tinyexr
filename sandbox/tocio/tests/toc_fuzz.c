/*
 * tocio - libFuzzer target over the hostile-input surface: YAML config parse,
 * introspection, processor build (colorspace pair and display/view), CPU
 * apply, the JIT, AOT-C / GLSL / Metal codegen, and every LUT file loader
 * (served to FileTransform through the reader hook).
 *
 * Input layout:  [flags:1] [YAML config ...] [0x00] [LUT file bytes ...]
 *   flags bits 0-2: LUT name extension (.cube .spi1d .spi3d .clf .csp none)
 *   flags bit  3  : also build the first display/view processor
 *   flags bit  4  : also JIT-compile and run the op list
 *   flags bits 5-7: allocation number to fail (0 = none), for OOM paths
 *
 *   make tocio-fuzz
 *   ./build/toc_fuzz -max_total_time=600 build/toc-fuzz-corpus
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "tocio.h"

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Budgeted, failure-injecting allocator: a hostile config may not take more
 * than this, and a chosen allocation fails to exercise error paths. */
#define FUZZ_BUDGET ((size_t)64u << 20)

typedef union fz_hdr {
    max_align_t align;
    size_t size;
} fz_hdr;

typedef struct fz_state {
    size_t live, calls, fail_at;
} fz_state;

static void *fz_alloc(void *user, size_t size) {
    fz_state *s = (fz_state *)user;
    fz_hdr *h;
    if (++s->calls == s->fail_at || size > FUZZ_BUDGET - s->live ||
        size > SIZE_MAX - sizeof(*h))
        return NULL;
    h = (fz_hdr *)malloc(sizeof(*h) + size);
    if (!h) return NULL;
    h->size = size;
    s->live += size;
    return h + 1;
}

static void fz_free(void *user, void *ptr) {
    fz_state *s = (fz_state *)user;
    fz_hdr *h;
    if (!ptr) return;
    h = ((fz_hdr *)ptr) - 1;
    s->live -= h->size;
    free(h);
}

typedef struct fz_lut {
    const uint8_t *data;
    size_t size;
} fz_lut;

/* Serve the LUT bytes for every FileTransform, deliberately without a NUL
 * terminator so parsers must honour the length. */
static toc_result fz_reader(void *user, const char *name, const toc_allocator *a,
                            char **data, size_t *len) {
    const fz_lut *l = (const fz_lut *)user;
    char *buf;
    (void)name;
    buf = (char *)a->alloc(a->user, l->size ? l->size : 1);
    if (!buf) return TOC_ERROR_OUT_OF_MEMORY;
    if (l->size) memcpy(buf, l->data, l->size);
    *data = buf;
    *len = l->size;
    return TOC_SUCCESS;
}

static void fz_backends(const toc_op_list *ops, const toc_allocator *a,
                        int jit) {
    float px[4 * 8];
    int i;
    char *src = NULL;
    size_t n = 0;
    toc_shader sh;
    for (i = 0; i < 4 * 8; ++i) {
        static const float probe[8] = {0.0f, 0.18f, 1.0f, -0.5f,
                                       4.0f, 1e-6f, 65504.0f, -1e30f};
        px[i] = probe[i % 8];
    }
    (void)toc_apply(ops, px, 8, 4);
    (void)toc_apply(ops, px, 8, 3);
    if (TOC_OK(toc_emit_c(ops, NULL, a, &src, &n)) && src) a->free(a->user, src);
    memset(&sh, 0, sizeof(sh));
    if (TOC_OK(toc_emit_glsl(ops, TOC_GLSL_330, a, &sh))) toc_shader_free(&sh);
    memset(&sh, 0, sizeof(sh));
    if (TOC_OK(toc_emit_metal(ops, a, &sh))) toc_shader_free(&sh);
    if (jit) {
        toc_jit *j = NULL;
        if (TOC_OK(toc_jit_compile(ops, 4, a, &j)) && j) {
            toc_jit_fn fn = toc_jit_func(j);
            if (fn) fn(px, 8);
            toc_jit_destroy(j);
        }
    }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    static const char *ext[8] = {"l.cube", "l.spi1d", "l.spi3d", "l.clf",
                                 "l.csp",  "l",       "l.CUBE",  "l.CLF"};
    fz_state st;
    toc_allocator a;
    toc_config *cfg = NULL;
    toc_op_list *ops = NULL;
    fz_lut lut;
    const uint8_t *nul;
    size_t ylen;
    uint8_t flags;
    int i, ncs;

    if (size < 1) return 0;
    flags = data[0];
    ++data; --size;
    memset(&st, 0, sizeof(st));
    st.fail_at = (size_t)(flags >> 5) * 7u; /* 0 disables injection */
    a.user = &st;
    a.alloc = fz_alloc;
    a.free = fz_free;

    nul = (const uint8_t *)memchr(data, 0, size);
    ylen = nul ? (size_t)(nul - data) : size;
    lut.data = nul ? nul + 1 : data + size;
    lut.size = nul ? size - ylen - 1 : 0;

    /* 1. Direct LUT loaders on the LUT bytes, by name and by sniffing. */
    if (lut.size) {
        char *cfgtxt = NULL;
        static const char cfg_head[] =
            "ocio_profile_version: 2\ncolorspaces:\n"
            "  - !<ColorSpace>\n    name: a\n"
            "    to_reference: !<FileTransform> {src: ";
        static const char cfg_tail[] =
            "}\n  - !<ColorSpace>\n    name: b\n";
        const char *nm = ext[flags & 7u];
        size_t hl = sizeof(cfg_head) - 1, nl = strlen(nm), tl = sizeof(cfg_tail) - 1;
        cfgtxt = (char *)malloc(hl + nl + tl);
        if (cfgtxt) {
            memcpy(cfgtxt, cfg_head, hl);
            memcpy(cfgtxt + hl, nm, nl);
            memcpy(cfgtxt + hl + nl, cfg_tail, tl);
            if (TOC_OK(toc_config_parse(cfgtxt, hl + nl + tl, &a, &cfg))) {
                toc_config_set_file_reader(cfg, fz_reader, &lut);
                if (TOC_OK(toc_processor_from_colorspaces(cfg, "a", "b", &a, &ops))) {
                    fz_backends(ops, &a, (flags >> 4) & 1);
                    toc_op_list_free(ops);
                }
                ops = NULL;
                toc_config_free(cfg);
                cfg = NULL;
            }
            free(cfgtxt);
        }
    }

    /* 2. The fuzzed config itself. */
    if (!TOC_OK(toc_config_parse((const char *)data, ylen, &a, &cfg)) || !cfg)
        return 0;
    toc_config_set_file_reader(cfg, fz_reader, &lut);

    ncs = toc_config_num_colorspaces(cfg);
    for (i = 0; i < ncs && i < 64; ++i) (void)toc_config_colorspace_name(cfg, i);
    (void)toc_config_role(cfg, "scene_linear");
    for (i = 0; i < toc_config_num_displays(cfg) && i < 16; ++i) {
        const char *d = toc_config_display_name(cfg, i);
        int v, nv = toc_config_num_views(cfg, d);
        for (v = 0; v < nv && v < 16; ++v) (void)toc_config_view_name(cfg, d, v);
    }
    for (i = 0; i < toc_config_num_view_transforms(cfg) && i < 16; ++i)
        (void)toc_config_view_transform_name(cfg, i);
    for (i = 0; i < toc_config_num_looks(cfg) && i < 16; ++i)
        (void)toc_config_look_name(cfg, i);
    for (i = 0; i < toc_config_num_active_displays(cfg) && i < 16; ++i)
        (void)toc_config_active_display_name(cfg, i);
    for (i = 0; i < toc_config_num_active_views(cfg) && i < 16; ++i)
        (void)toc_config_active_view_name(cfg, i);

    /* Build processors for a few colorspace pairs. */
    if (ncs > 0) {
        int pairs[3][2] = {{0, ncs - 1}, {ncs - 1, 0}, {ncs / 2, 0}};
        int k;
        for (k = 0; k < 3; ++k) {
            const char *s = toc_config_colorspace_name(cfg, pairs[k][0]);
            const char *d = toc_config_colorspace_name(cfg, pairs[k][1]);
            if (!s || !d) continue;
            ops = NULL;
            if (TOC_OK(toc_processor_from_colorspaces(cfg, s, d, &a, &ops)) && ops) {
                fz_backends(ops, &a, (flags >> 4) & 1);
                toc_op_list_free(ops);
            }
        }
    }
    /* Display/view processor. */
    if (((flags >> 3) & 1) && ncs > 0 && toc_config_num_displays(cfg) > 0) {
        const char *d = toc_config_display_name(cfg, 0);
        const char *v = d ? toc_config_view_name(cfg, d, 0) : NULL;
        const char *s = toc_config_colorspace_name(cfg, 0);
        ops = NULL;
        if (d && v && s &&
            TOC_OK(toc_processor_from_display_view(cfg, s, d, v, &a, &ops)) && ops) {
            fz_backends(ops, &a, (flags >> 4) & 1);
            toc_op_list_free(ops);
        }
    }
    toc_config_free(cfg);
    return 0;
}
