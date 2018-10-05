/* noc_packer library
 *
 * Copyright (c) 2018 Guillaume Chereau <guillaume@noctua-software.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

/*
 * A simple library that allows to compress tabular data with better
 * performances than a direct DEFLATE compression.
 */

/*
 * Type: noc_packer_column
 * Define a single column of the table.
 *
 * Attributes:
 *   id         - Uniq id for this column.
 *   type       - One of:
 *                  'f' - floating point value.
 *                  'd' - integer.
 *                  's' - string.
 *   size       - Size of the column data in bytes.
 *   ofs        - Offset of the column data
 *   precision  - For floating point columns: how many bits of precision do
 *                we keep.
 */

struct noc_packer_column {
    char id[4];
    char type;
    int ofs;
    int size;
    int precision;
};

int noc_packer_compress(
        const char *data, int size, int row_size,
        const struct noc_packer_column *columns,
        char **out);

int noc_packer_uncompress(
        const char *data, int size, int row_size,
        const struct noc_packer_column *columns,
        char **out);

#ifdef NOC_PACKER_IMPLEMENTATION

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>

// In place shuffle of the data bytes for optimized compression.
static void noc_shuffle_bytes(uint8_t *data, int nb, int size)
{
    int i, j;
    uint8_t *buf = (uint8_t*)malloc(nb * size);
    memcpy(buf, data, nb * size);
    for (j = 0; j < size; j++) {
        for (i = 0; i < nb; i++) {
            data[j * nb + i] = buf[i * size + j];
        }
    }
    free(buf);
}

// Zero out bits from a float value.
static float float_trunc(float x, int zerobits)
{
    // A float is represented in binary like this:
    // seeeeeeeefffffffffffffffffffffff
    uint32_t mask = -(1L << zerobits);
    uint32_t floatbits = (*((uint32_t*)(&x)));
    floatbits &= mask;
    x = *((float*)(&floatbits));
    return x;
}

static void noc_write_header(char *out, int comp_size,
                             const struct noc_packer_column *columns,
                             int nb_columns, int nb_row, int row_size)
{
    int i;
    memcpy(out + 0, &comp_size, 4);
    memcpy(out + 4, &row_size, 4);
    memcpy(out + 8, &nb_columns, 4);
    memcpy(out + 12, &nb_row, 4);
    for (i = 0; i < nb_columns; i++) {
        memcpy(out + 16 + 0, columns[i].id, 4);
        memcpy(out + 16 + 4, &columns[i].type, 1);
        memset(out + 16 + 5, 0, 3);
        memcpy(out + 16 + 8, &columns[i].ofs, 4);
        memcpy(out + 16 + 12, &columns[i].size, 4);
    }
}

static void noc_write_row(char *out, int i, const char *data, int row_size,
                          int out_row_size, int nb_columns,
                          const struct noc_packer_column *col_in,
                          const struct noc_packer_column *col_out)
{
    int c;
    float f;
    out += i * out_row_size;
    data += i * row_size;
    for (c = 0; c < nb_columns; c++) {
        memcpy(out + col_out[c].ofs, data + col_in[c].ofs, col_out[c].size);
        if (col_out[c].type == 'f' && col_out[c].precision) {
            memcpy(&f, out + col_out[c].ofs, 4);
            f = float_trunc(f, 23 - col_out[c].precision);
            memcpy(out + col_out[c].ofs, &f, 4);
        }
    }
}

int noc_packer_compress(
        const char *data, int size, int row_size,
        const struct noc_packer_column *columns,
        char **out)
{
    const struct noc_packer_column *col;
    struct noc_packer_column *col2;
    int i, nb, out_row_size = 0, nb_columns = 0, header_size;
    char *buf;
    uLongf comp_size;

    assert(size % row_size == 0);
    nb = size / row_size;
    for (col = columns; *col->id; col++) {
        assert(col->size);
        nb_columns++;
        out_row_size += col->size;
    }
    col2 = (struct noc_packer_column*)malloc(nb_columns * sizeof(*col2));
    for (i = 0; i < nb_columns; i++) {
        col2[i] = columns[i];
        col2[i].ofs = i ? col2[i - 1].ofs + col2[i - 1].size : 0;
    }
    header_size = 16 + nb_columns * 16;
    comp_size = compressBound(nb * out_row_size);
    *out = (char*)malloc(comp_size + header_size);
    buf = (char*)malloc(nb * out_row_size);
    for (i = 0; i < nb; i++) {
        noc_write_row(buf, i, data, row_size, out_row_size,
                      nb_columns, columns, col2);
    }
    noc_shuffle_bytes((uint8_t*)buf, nb, out_row_size);
    compress((Bytef*)(*out + header_size), &comp_size, (Bytef*)buf,
             nb * out_row_size);
    noc_write_header(*out, comp_size, col2, nb_columns, nb, out_row_size);
    free(buf);
    free(col2);
    return comp_size + header_size;
}

static int noc_read_header(const char *data, int size, int *data_ofs,
                           struct noc_packer_column *columns,
                           int nb_columns,
                           int *comp_size,
                           int *row_size)
{
    int nb_col, nb_row, i, j;
    char id[4], type;
    data += *data_ofs;
    memcpy(comp_size, data + 0, 4);
    memcpy(row_size, data + 4, 4);
    memcpy(&nb_col, data + 8, 4);
    memcpy(&nb_row, data + 12, 4);
    for (i = 0; i < nb_col; i++) {
        memcpy(id, data + 16 + i * 16, 4);
        memcpy(&type, data + 16 + i * 16 + 4, 1);
        for (j = 0; j < nb_columns; j++) {
            if (strncmp(columns[j].id, id, 4) == 0) break;
        }
        if (j == nb_columns) continue;
        if (columns[j].type != type) return -1;
        memcpy(&columns[j].ofs,  data + 16 + i * 16 + 8, 4);
        memcpy(&columns[j].size, data + 16 + i * 16 + 12, 4);
    }
    *data_ofs += 16 + nb_col * 16;
    return nb_row;
}

int noc_packer_uncompress(
        const char *data, int size, int row_size,
        const struct noc_packer_column *columns,
        char **out)
{
    struct noc_packer_column *cols_in;
    const struct noc_packer_column *col;
    int nb_columns = 0, nb_rows, i, j, comp_size, in_row_size;
    int data_ofs = 0;
    char *buf;
    unsigned long size_l;

    for (col = columns; *col->id; col++) nb_columns++;
    cols_in = (struct noc_packer_column*)malloc(nb_columns * sizeof(*cols_in));
    memcpy(cols_in, columns, nb_columns * sizeof(*cols_in));
    // Read the header.
    nb_rows = noc_read_header(data, size, &data_ofs, cols_in, nb_columns,
                              &comp_size, &in_row_size);
    if (nb_rows < 0) return -1;
    size_l = in_row_size * nb_rows;
    buf = (char*)malloc(size_l);
    if (uncompress((Bytef*)buf, &size_l, (const Bytef*)(data + data_ofs),
                   comp_size) != Z_OK) {
        nb_rows = -1;
        goto end;
    }
    noc_shuffle_bytes((uint8_t*)buf, in_row_size, nb_rows);

    *out = (char*)calloc(nb_rows, row_size);
    for (i = 0; i < nb_rows; i++) {
        for (j = 0; j < nb_columns; j++) {
            memcpy(*out + i * row_size + columns[j].ofs,
                   buf + i * in_row_size + cols_in[j].ofs,
                   cols_in[j].size);
        }
    }
end:
    free(buf);
    free(cols_in);
    return nb_rows * row_size;
}

#endif // NOC_PACKER_IMPLEMENTATION
