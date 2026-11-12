/* DDS/KTX/ASTC container vectors: C writer output vs the Lean model.
 *
 * Emits, per line:
 *   dds  <width> <height> <dxgi> <blockBytes> | <148+ hex bytes>
 *   ktx  <width> <height> <internal> <base> <payload> | <68+ hex bytes>
 *   astc <bx> <by> <width> <height> <v> <outsize> | <16+ hex bytes>
 *        (v = 0: full-file compare; v = 1: writer rejected the call, so the
 *        record carries the verdict only — the Lean side must agree)
 *   E dds  <width> <height> <blockBytes> <outsize> <v>   (verdict only)
 *   E ktx  <width> <height> <payload>    <outsize> <v>   (verdict only)
 *   E astc <bx> <by> <width> <height> <outsize> <v>      (verdict only)
 * where v = 0 means TC_SUCCESS and v = 1 means TC_ERROR_INVALID_ARGUMENT.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"

#define BLOCK_BYTES 256u

static void print_bytes(FILE *out, const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) fprintf(out, "%02x", p[i]);
}

/* Read back a little-endian u32 from the written header, so the vector
 * records what the C writer actually emitted (not what the test assumed). */
/* Deterministic payload byte, reproduced independently by the Lean checker. */
static uint8_t pat(size_t i) { return (uint8_t)((i * 37u + 11u) & 0xffu); }

static void fill_pat(uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) p[i] = pat(i);
}

static uint32_t rd32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }

    /* DDS: all public BC writers share tc_dds_write_bc_memory. */
    for (int ci = 0; ci < 10; ci++) {
        uint32_t w = 1u + (uint32_t)(ci * 7) % 97u;
        uint32_t h = 1u + (uint32_t)(ci * 13) % 53u;
        uint32_t block = (ci == 2 || ci == 3) ? 8u : 16u;
        size_t bx = (w + 3u) / 4u, by = (h + 3u) / 4u;
        size_t bc_size = bx * by * block;
        size_t need = 148u + bc_size;
        uint8_t *buf = (uint8_t *)malloc(need);
        uint8_t *bc = (uint8_t *)calloc(bc_size, 1);
        fill_pat(bc, bc_size);
        tc_result rc = TC_ERROR_UNSUPPORTED;
        if (!buf || !bc) return 1;
        if (ci == 0 || ci == 1) {
            tc_bc7_options o; tc_bc7_options_init(&o); o.srgb = ci & 1;
            rc = tc_dds_write_bc7_memory(bc, w, h, &o, buf, need);
        } else if (ci == 2 || ci == 3) {
            tc_bc1_options o; tc_bc1_options_init(&o); o.srgb = ci & 1;
            rc = tc_dds_write_bc1_memory(bc, w, h, &o, buf, need);
        } else if (ci == 4 || ci == 5) {
            tc_bc3_options o; tc_bc3_options_init(&o); o.srgb = ci & 1;
            rc = tc_dds_write_bc3_memory(bc, w, h, &o, buf, need);
        } else if (ci == 6 || ci == 7) {
            tc_bc5_options o; tc_bc5_options_init(&o); o.snorm = (ci & 1) ? 1 : 0;
            rc = tc_dds_write_bc5_memory(bc, w, h, &o, buf, need);
        } else {
            tc_bc6h_options o; tc_bc6h_options_init(&o);
            rc = tc_dds_write_bc6h_memory(bc, w, h, &o, buf, need);
        }
        if (rc != TC_SUCCESS) {
            fprintf(stderr, "dds case %d failed (%d)\n", ci, (int)rc);
            free(buf); free(bc);
            continue;
        }
        fprintf(out, "dds %u %u %u %u | ", rd32(buf + 16), rd32(buf + 12),
                rd32(buf + 112), rd32(buf + 20) / (((w + 3u) / 4u) ? ((w + 3u) / 4u) : 1u));
        print_bytes(out, buf, need);
        fprintf(out, "\n");
        free(buf);
        free(bc);
    }

    /* KTX: ETC2 / EAC writers share tc_ktx_write_compressed_memory. */
    for (int ci = 0; ci < 4; ci++) {
        uint32_t w = 1u + (uint32_t)(ci * 5) % 65u;
        uint32_t h = 1u + (uint32_t)(ci * 3) % 33u;
        size_t bx = (w + 3u) / 4u, by = (h + 3u) / 4u;
        size_t payload = bx * by * 16u;
        size_t need = 68u + payload;
        uint8_t *buf = (uint8_t *)malloc(need);
        uint8_t *etc = (uint8_t *)calloc(payload, 1);
        fill_pat(etc, payload);
        tc_result rc;
        if (!buf || !etc) return 1;
        if (ci & 1) {
            rc = tc_ktx_write_eac_memory(etc, w, h, ci == 3, buf, need);
        } else {
            tc_etc2_options o;
            tc_etc2_options_init(&o);
            o.srgb = (ci == 2) ? 1 : 0;
            rc = tc_ktx_write_etc2_memory(etc, w, h, &o, buf, need);
        }
        if (rc != TC_SUCCESS) {
            fprintf(stderr, "ktx case %d failed (%d)\n", ci, (int)rc);
            free(buf); free(etc);
            continue;
        }
        fprintf(out, "ktx %u %u %u %u %u | ", rd32(buf + 36), rd32(buf + 40),
                rd32(buf + 28), rd32(buf + 32), rd32(buf + 64));
        /* EAC R11 stores 8 bytes per block, so the writer's real payload can
         * be smaller than `payload`: print exactly what the header declares. */
        print_bytes(out, buf, 68u + (size_t)rd32(buf + 64));
        fprintf(out, "\n");
        free(buf);
        free(etc);
    }

    /* KTX ETC2 RGBA (alpha): internal 0x9278 (sRGB 0x9279), base 0x1908,
     * 16 bytes per block. */
    for (int ci = 0; ci < 4; ci++) {
        uint32_t w = 3u + (uint32_t)(ci * 11) % 61u;
        uint32_t h = 5u + (uint32_t)(ci * 7) % 29u;
        size_t bx = (w + 3u) / 4u, by = (h + 3u) / 4u;
        size_t payload = bx * by * 16u; /* = tc_etc2_rgba_compressed_size */
        size_t need = 68u + payload;
        uint8_t *buf = (uint8_t *)malloc(need);
        uint8_t *etc = (uint8_t *)calloc(payload, 1);
        tc_etc2_options o;
        tc_result rc;
        fill_pat(etc, payload);
        tc_etc2_options_init(&o);
        o.alpha = 1;
        o.srgb = ci & 1;
        rc = tc_ktx_write_etc2_memory(etc, w, h, &o, buf, need);
        if (rc != TC_SUCCESS) {
            fprintf(stderr, "ktx alpha case %d failed (%d)\n", ci, (int)rc);
            free(buf); free(etc);
            continue;
        }
        fprintf(out, "ktx %u %u %u %u %u | ", rd32(buf + 36), rd32(buf + 40),
                rd32(buf + 28), rd32(buf + 32), rd32(buf + 64));
        print_bytes(out, buf, 68u + (size_t)rd32(buf + 64));
        fprintf(out, "\n");
        free(buf);
        free(etc);
    }

    /* ASTC file container: every valid block footprint with partial-block
     * (odd) extents, exercised through tc_astc_write_file_memory. */
    {
        static const uint32_t vbp[][2] = {
            {4, 4}, {5, 4}, {5, 5}, {6, 5}, {6, 6}, {8, 5}, {8, 6},
            {8, 8}, {10, 5}, {10, 6}, {10, 8}, {10, 10}, {12, 10}, {12, 12}
        };
        for (size_t ci = 0; ci < sizeof(vbp) / sizeof(vbp[0]); ci++) {
            uint32_t bx = vbp[ci][0], by = vbp[ci][1];
            uint32_t w = bx * 2u + 1u; /* two full blocks + one partial */
            uint32_t h = by * 2u + 1u;
            tc_astc_options o;
            size_t payload, need;
            uint8_t *bc, *buf;
            tc_result rc;
            tc_astc_options_init(&o);
            o.block_x = bx;
            o.block_y = by;
            payload = tc_astc_compressed_size(w, h, &o);
            need = tc_astc_file_size(w, h, &o);
            bc = (uint8_t *)calloc(payload ? payload : 1u, 1);
            buf = (uint8_t *)malloc(need ? need : 1u);
            fill_pat(bc, payload);
            rc = tc_astc_write_file_memory(bc, w, h, &o, buf, need);
            if (rc != TC_SUCCESS) {
                fprintf(stderr, "astc case %zu failed (%d)\n", ci, (int)rc);
                free(bc); free(buf);
                continue;
            }
            fprintf(out, "astc %u %u %u %u 0 %zu | ", bx, by, w, h, need);
            print_bytes(out, buf, need);
            fprintf(out, "\n");
            free(bc);
            free(buf);
        }

        /* Invalid footprints: the writer must reject them. Record the
         * verdict only (v=1, empty payload hex). */
        {
            static const uint32_t ibp[][2] = {
                {3, 4}, {4, 5}, {7, 7}, {6, 8}, {13, 13}, {10, 4}, {8, 7},
                {12, 11}, {5, 6}, {2, 2}
            };
            for (size_t ci = 0; ci < sizeof(ibp) / sizeof(ibp[0]); ci++) {
                uint32_t bx = ibp[ci][0], by = ibp[ci][1];
                uint32_t w = bx * 2u + 3u, h = by * 2u + 3u;
                tc_astc_options o;
                tc_astc_options_init(&o);
                o.block_x = bx;
                o.block_y = by;
                {
                    uint8_t in[BLOCK_BYTES];
                    uint8_t *buf = (uint8_t *)malloc(1024);
                    tc_result rc;
                    memset(in, 0, sizeof(in));
                    rc = tc_astc_write_file_memory(in, w, h, &o, buf, 1024u);
                    fprintf(out, "astc %u %u %u %u %d 1024 | \n", bx, by, w, h,
                            rc == TC_SUCCESS ? 0 : 1);
                    free(buf);
                }
            }
        }

        /* Verdict-only records: `E astc <bx> <by> <w> <h> <outsize> <v>`
         * with v = 0 (TC_SUCCESS) or 1 (TC_ERROR_INVALID_ARGUMENT). */
        {
            tc_astc_options o;
            size_t payload, need;
            uint8_t *bc, *buf;
            tc_result rc;
            tc_astc_options_init(&o);
            o.block_x = 5;
            o.block_y = 4;
            payload = tc_astc_compressed_size(5, 4, &o);
            need = tc_astc_file_size(5, 4, &o);
            bc = (uint8_t *)calloc(payload, 1);
            buf = (uint8_t *)malloc(need);
            fill_pat(bc, payload);
            /* exact-size buffer: success */
            rc = tc_astc_write_file_memory(bc, 5, 4, &o, buf, need);
            fprintf(out, "E astc 5 4 5 4 %zu %d\n", need,
                    rc == TC_SUCCESS ? 0 : 1);
            /* one byte short: rejected */
            rc = tc_astc_write_file_memory(bc, 5, 4, &o, buf, need - 1u);
            fprintf(out, "E astc 5 4 5 4 %zu %d\n", need - 1u,
                    rc == TC_SUCCESS ? 0 : 1);
            /* zero width: rejected */
            rc = tc_astc_write_file_memory(bc, 0, 4, &o, buf, need);
            fprintf(out, "E astc 5 4 0 4 %zu %d\n", need,
                    rc == TC_SUCCESS ? 0 : 1);
            /* zero height: rejected */
            rc = tc_astc_write_file_memory(bc, 5, 0, &o, buf, need);
            fprintf(out, "E astc 5 4 5 0 %zu %d\n", need,
                    rc == TC_SUCCESS ? 0 : 1);
            free(bc);
            free(buf);
        }
    }

    /* Verdict-only records for the DDS and KTX writers:
     * `E dds <w> <h> <block> <outsize> <v>` and
     * `E ktx <w> <h> <payload> <outsize> <v>`. */
    {
        /* DDS via tc_dds_write_bc7_memory (16 B/block) ... */
        {
            uint32_t w = 9u, h = 5u;
            size_t bc_size = ((w + 3u) / 4u) * ((h + 3u) / 4u) * 16u;
            size_t need = 148u + bc_size;
            uint8_t *bc = (uint8_t *)calloc(bc_size, 1);
            uint8_t *buf = (uint8_t *)malloc(need);
            tc_bc7_options o;
            tc_result rc;
            fill_pat(bc, bc_size);
            tc_bc7_options_init(&o);
            rc = tc_dds_write_bc7_memory(bc, w, h, &o, buf, need);
            fprintf(out, "E dds %u %u 16 %zu %d\n", w, h, need,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_dds_write_bc7_memory(bc, w, h, &o, buf, need - 1u);
            fprintf(out, "E dds %u %u 16 %zu %d\n", w, h, need - 1u,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_dds_write_bc7_memory(bc, 0, h, &o, buf, need);
            fprintf(out, "E dds 0 %u 16 %zu %d\n", h, need,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_dds_write_bc7_memory(bc, w, 0, &o, buf, need);
            fprintf(out, "E dds %u 0 16 %zu %d\n", w, need,
                    rc == TC_SUCCESS ? 0 : 1);
            free(bc);
            free(buf);
        }
        /* ... and tc_dds_write_bc1_memory (8 B/block). */
        {
            uint32_t w = 9u, h = 5u;
            size_t bc_size = ((w + 3u) / 4u) * ((h + 3u) / 4u) * 8u;
            size_t need = 148u + bc_size;
            uint8_t *bc = (uint8_t *)calloc(bc_size, 1);
            uint8_t *buf = (uint8_t *)malloc(need);
            tc_bc1_options o;
            tc_result rc;
            fill_pat(bc, bc_size);
            tc_bc1_options_init(&o);
            rc = tc_dds_write_bc1_memory(bc, w, h, &o, buf, need);
            fprintf(out, "E dds %u %u 8 %zu %d\n", w, h, need,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_dds_write_bc1_memory(bc, w, h, &o, buf, need - 1u);
            fprintf(out, "E dds %u %u 8 %zu %d\n", w, h, need - 1u,
                    rc == TC_SUCCESS ? 0 : 1);
            free(bc);
            free(buf);
        }
        /* KTX via tc_ktx_write_etc2_memory with alpha (the options-init
         * default): 16 B/block, payload = tc_etc2_rgba_compressed_size. */
        {
            uint32_t w = 7u, h = 3u;
            size_t payload = tc_etc2_rgba_compressed_size(w, h);
            size_t need = 68u + payload;
            uint8_t *etc = (uint8_t *)calloc(payload, 1);
            uint8_t *buf = (uint8_t *)malloc(need);
            tc_etc2_options o;
            tc_result rc;
            fill_pat(etc, payload);
            tc_etc2_options_init(&o);
            rc = tc_ktx_write_etc2_memory(etc, w, h, &o, buf, need);
            fprintf(out, "E ktx %u %u %zu %zu %d\n", w, h, payload, need,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_ktx_write_etc2_memory(etc, w, h, &o, buf, need - 1u);
            fprintf(out, "E ktx %u %u %zu %zu %d\n", w, h, payload, need - 1u,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_ktx_write_etc2_memory(etc, 0, h, &o, buf, need);
            fprintf(out, "E ktx 0 %u %zu %zu %d\n", h, payload, need,
                    rc == TC_SUCCESS ? 0 : 1);
            rc = tc_ktx_write_etc2_memory(etc, w, 0, &o, buf, need);
            fprintf(out, "E ktx %u 0 %zu %zu %d\n", w, payload, need,
                    rc == TC_SUCCESS ? 0 : 1);
            free(etc);
            free(buf);
        }
    }

    fclose(out);
    return 0;
}
