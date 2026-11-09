/* DDS/KTX header byte-layout vectors: C writer output vs the Lean model.
 *
 * Emits, per line:
 *   dds <width> <height> <dxgi> <blockBytes> | <148 hex bytes>
 *   ktx <width> <height> <internal> <base> <payload> | <68 hex bytes>
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "texcomp.h"

static void print_bytes(FILE *out, const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) fprintf(out, "%02x", p[i]);
}

/* Read back a little-endian u32 from the written header, so the vector
 * records what the C writer actually emitted (not what the test assumed). */
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
        print_bytes(out, buf, 148);
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
        print_bytes(out, buf, 68);
        fprintf(out, "\n");
        free(buf);
        free(etc);
    }

    fclose(out);
    return 0;
}
