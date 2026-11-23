/*
 * JPH wrapper differential vectors: independent marker/geometry reader.
 *
 * For each fixture we locate the HTJ2K codestream (SOC followed by SIZ),
 * walk the marker segments with their declared lengths, and emit the marker
 * sequence plus SIZ/COD/QCD geometry. This is deliberately a small,
 * standalone reader: it does not call into src/exr_jph.c.
 *
 * Output: <name> <marker-codes-separated-by-comma> <xsiz> <ysiz> <csiz>
 *         <xtsiz> <ytsiz> <ntiles> <ndecomp> <qcdcount> <valid 0|1>
 *
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static uint16_t be16(const uint8_t *p) { return (uint16_t)((p[0] << 8) | p[1]); }
static uint32_t be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
           ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

static int next_marker(const uint8_t *d, size_t n, size_t p, uint16_t *code,
                       size_t *after) {
    while (p < n) {
        if (d[p] != 0xff) { p++; continue; }
        p++;
        while (p < n && d[p] == 0xff) p++;
        if (p >= n) return 0;
        if (d[p] == 0x00) { p++; continue; }
        *code = (uint16_t)(0xff00u | d[p]);
        *after = p + 1;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int fi;
    for (fi = 1; fi < argc; ++fi) {
        FILE *f = fopen(argv[fi], "rb");
        uint8_t *d;
        long sz;
        size_t n, soc = (size_t)-1, p, i;
        uint16_t code;
        size_t q;
        uint16_t len, rsiz = 0, csiz = 0;
        uint32_t xsiz = 0, ysiz = 0, xosiz = 0, yosiz = 0;
        uint32_t xtsiz = 0, ytsiz = 0, xtosiz = 0, ytosiz = 0;
        unsigned ndecomp = 0, qcdn = 0;
        int sawcod = 0, sawqcd = 0, sots = 0, sodd = 0, valid;
        if (!f) continue;
        fseek(f, 0, SEEK_END); sz = ftell(f); fseek(f, 0, SEEK_SET);
        if (sz < 4) { fclose(f); continue; }
        d = (uint8_t *)malloc((size_t)sz);
        if (fread(d, 1, (size_t)sz, f) != (size_t)sz) { free(d); fclose(f); continue; }
        fclose(f);
        n = (size_t)sz;
        for (i = 0; i + 3 < n; ++i)
            if (d[i] == 0xff && d[i + 1] == 0x4f && d[i + 2] == 0xff &&
                d[i + 3] == 0x51) { soc = i; break; }
        if (soc == (size_t)-1) { free(d); continue; }
        p = soc + 2;
        if (!next_marker(d, n, p, &code, &q) || code != 0xff51) { free(d); continue; }
        if (q + 2 > n) { free(d); continue; }
        len = be16(d + q);
        if (len < 38 || q + len > n) { free(d); continue; }
        rsiz = be16(d + q + 2);
        xsiz = be32(d + q + 4); ysiz = be32(d + q + 8);
        xosiz = be32(d + q + 12); yosiz = be32(d + q + 16);
        xtsiz = be32(d + q + 20); ytsiz = be32(d + q + 24);
        xtosiz = be32(d + q + 28); ytosiz = be32(d + q + 32);
        csiz = be16(d + q + 36);
        if (csiz == 0 || len - 38 != (uint16_t)(csiz * 3u)) { free(d); continue; }
        p = q + len;

        printf("%s ff4f ff51", argv[fi]);
        while (next_marker(d, n, p, &code, &q)) {
            printf(" %04x", code);
            p = q;
            if (code == 0xffd9) break;
            if (code == 0xff52) { /* COD */
                if (p + 12 > n) break;
                len = be16(d + p);
                if (len < 12 || p + len > n) break;
                ndecomp = d[p + 7];
                sawcod = 1;
                p += len;
            } else if (code == 0xff5c) { /* QCD */
                if (p + 3 > n) break;
                len = be16(d + p);
                if (len < 3 || p + len > n) break;
                {
                    unsigned sq = d[p + 2], style = sq & 0x1f;
                    if (style == 1) qcdn = (len - 3) / 2;
                    else if (style == 0 || style == 2) qcdn = len - 3;
                    sawqcd = 1;
                }
                p += len;
            } else if (code == 0xff90) { /* SOT */
                sots = 1;
                if (p + 10 > n) break;
                len = be16(d + p);
                if (len < 10 || p + len > n) break;
                p += len;
                while (next_marker(d, n, p, &code, &q)) {
                    printf(" %04x", code);
                    p = q;
                    if (code == 0xff93) { sodd = 1; break; }
                    if (code == 0xff58 || code == 0xff64 || code == 0xff85 ||
                        code == 0xff88 || code == 0xff89 || code == 0xff5f) {
                        if (p + 2 > n) break;
                        len = be16(d + p);
                        if (len < 2 || p + len > n) break;
                        p += len;
                    } else break;
                }
                /* entropy data: scan to EOC */
                while (next_marker(d, n, p, &code, &q)) {
                    p = q;
                    if (code == 0xffd9) { printf(" %04x", code); goto done; }
                }
            } else {
                if (p + 2 > n) break;
                len = be16(d + p);
                if (len < 2 || p + len > n) break;
                p += len;
            }
        }
    done:
        {
            uint32_t nx = xtsiz ? (xsiz - xtosiz + xtsiz - 1) / xtsiz : 0;
            uint32_t ny = ytsiz ? (ysiz - ytosiz + ytsiz - 1) / ytsiz : 0;
            valid = sawcod && sawqcd && sots && sodd && (rsiz & 0x4000) &&
                    !xosiz && !yosiz && !xtosiz && !ytosiz &&
                    xtsiz == xsiz && ytsiz == ysiz &&
                    qcdn == 1u + 3u * ndecomp;
            printf(" %u %u %u %u %u %u %u %u %d\n",
                   xsiz, ysiz, csiz, xtsiz, ytsiz, nx * ny, ndecomp, qcdn, valid);
        }
        free(d);
    }
    return 0;
}
