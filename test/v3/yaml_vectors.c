/* YAML config-parser differential vectors: C toc_yaml_parse vs the Lean
 * model (Tocio/YamlEngine.lean).
 *
 * For each embedded document the generator emits:
 *   ydoc <id> | <hex of the document text>
 *   y <id> <v> | <tree dump>
 * where v = 0 means TOC_SUCCESS (dump = the canonical node tree) and
 * v = 1 means TOC_ERROR_PARSE (empty dump). The Lean checker decodes the
 * hex, parses the document with the model parser, pretty-prints its tree
 * with the same discipline, and must match the C dump byte-for-byte.
 *
 * Dump grammar: s(text) for scalars, S(a,b,...) for sequences,
 * M(k=v,...) for mappings; within dumped text the characters
 * \ ( ) , = are backslash-escaped. The first slice covers the C parser's
 * block + flow surface *without* !<Tag> handling: comments, blank lines,
 * --- / ... markers, tab-indent rejection, quote-aware comment and colon
 * scanning, quoted/escaped scalars, flow seqs/maps, dash sequences with
 * map items, block scalars (| and >), bare scalar lines, anchors/aliases
 * as parse errors, trailing-content rejection and the depth cap.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tocio.h"
#include "toc_internal.h"

static void print_hex(FILE *out, const char *p, size_t n) {
    for (size_t i = 0; i < n; i++) fprintf(out, "%02x", (unsigned char)p[i]);
}

static void dump_text(toc_sb *sb, const char *s) {
    for (const char *p = s ? s : ""; *p; ++p) {
        char c = *p;
        if (c == '\\') {
            toc_sb_putc(sb, '\\');
            toc_sb_putc(sb, '\\');
        } else if (c == '\n') {
            toc_sb_puts(sb, "\\n");
        } else if (c == '(' || c == ')' || c == ',' || c == '=') {
            toc_sb_putc(sb, '\\');
            toc_sb_putc(sb, c);
        } else {
            toc_sb_putc(sb, c);
        }
    }
}

static void dump_node(toc_sb *sb, const toc_node *n) {
    if (!n) {
        toc_sb_puts(sb, "?");
        return;
    }
    switch (n->kind) {
    case TOC_NODE_SCALAR:
        toc_sb_puts(sb, "s(");
        dump_text(sb, n->scalar);
        toc_sb_putc(sb, ')');
        break;
    case TOC_NODE_SEQ:
        toc_sb_puts(sb, "S(");
        for (size_t i = 0; i < n->n_items; i++) {
            if (i) toc_sb_putc(sb, ',');
            dump_node(sb, n->items[i]);
        }
        toc_sb_putc(sb, ')');
        break;
    case TOC_NODE_MAP:
        toc_sb_puts(sb, "M(");
        for (size_t i = 0; i < n->n_pairs; i++) {
            if (i) toc_sb_putc(sb, ',');
            dump_text(sb, n->keys[i]);
            toc_sb_putc(sb, '=');
            dump_node(sb, n->vals[i]);
        }
        toc_sb_putc(sb, ')');
        break;
    }
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }

    static const char *docs[] = {
        /* 0: minimal map with a flow sequence */
        "names: [r, g, b]\ncount: 3\n",
        /* 1: comments (quote-aware '#'), quoted scalars */
        "# leading comment\n\nkey: value  # trailing comment\n"
        "other: \"quoted # hash\"\nplain: it's fine\n",
        /* 2: nested maps, empty value at the end */
        "outer:\n  inner:\n    leaf: 1\n  other: 2\nempty:\n",
        /* 3: dash sequence of scalars */
        "- a\n- b\n- c\n",
        /* 4: dash sequence of maps (multi-key items) */
        "- name: raw\n  desc: first\n- name: ci\n  desc: second\n",
        /* 5: flow seq with quoted/escaped scalars, nested flow maps */
        "pts: [1, 2.5, -3, \"x,y\", 'a''b']\n"
        "m: {r: 1, g: 2, deep: {z: 9}, e: []}\n",
        /* 6: block scalar */
        "text: |\n  line one\n  line two\nafter: 1\n",
        /* 7: plain ':' inside scalars (no space after) */
        "k: ocio:lin_ciexyzd65_display\nu: \"a: b\"\n",
        /* 8: --- start and ... terminator */
        "---\ncount: 1\n...\ntrailing: 1\n",
        /* 9: bare scalar document */
        "just a scalar\n",
        /* 10: empty document -> empty map */
        "",
        /* 11: comment-only document -> empty map */
        "# nothing here\n",
        /* 12: tab in indentation -> parse error */
        "k:\n\tbad: 1\n",
        /* 13: anchor -> parse error */
        "k: &anchor v\n",
        /* 14: alias -> parse error */
        "k: *alias\n",
        /* 15: trailing unparsed content -> parse error */
        "a: 1\n  bad indent: 2\n",
        /* 16: unclosed flow sequence -> accepted as-is */
        "k: [1, 2\n",
        /* 17: empty dash item, then a scalar item */
        "- \n- x\n",
        /* 18: '=' in a key (escaped in the dump) */
        "a=b: 1\n",
        /* 19: sequence nested inside a map nested inside a sequence */
        "top:\n  - - x\n    - y\n  end: 1\n",
        /* 20: quoted keys and single-quoted values with escapes */
        "\"k ey\": 'a\\'b'\n'x': plain\n",
        /* 21: block scalar '>' folded-style marker (concatenated too) */
        "fold: >\n  f1\n  f2\nnext: 2\n",
    };

    size_t ndocs = sizeof(docs) / sizeof(docs[0]);
    for (size_t id = 0; id < ndocs; id++) {
        const char *text = docs[id];
        size_t len = strlen(text);
        toc_allocator alloc = *toc_default_allocator();
        toc_arena ar;
        toc_node *root = NULL;
        int err_line = 0;
        toc_sb sb;
        toc_result rc;

        fprintf(out, "ydoc %zu | ", id);
        print_hex(out, text, len);
        fprintf(out, "\n");

        toc_arena_init(&ar, &alloc);
        rc = toc_yaml_parse(text, len, &ar, &root, &err_line);
        if (rc == TOC_SUCCESS) {
            toc_sb_init(&sb, &alloc);
            dump_node(&sb, root);
            fprintf(out, "y %zu 0 | %s\n", id, sb.buf ? sb.buf : "");
            toc_sb_free(&sb);
        } else {
            fprintf(out, "y %zu 1 | \n", id);
        }
        toc_arena_free(&ar);
    }

    /* Deep nested map (30 levels) built programmatically. */
    {
        char text[4096];
        size_t off = 0;
        for (int lvl = 0; lvl < 30; lvl++) {
            for (int sp = 0; sp < lvl * 2; sp++) text[off++] = ' ';
            off += (size_t)snprintf(text + off, sizeof(text) - off, "k%d:\n", lvl);
        }
        for (int sp = 0; sp < 60; sp++) text[off++] = ' ';
        off += (size_t)snprintf(text + off, sizeof(text) - off, "leaf: 1\n");
        text[off] = 0;

        fprintf(out, "ydoc %zu | ", ndocs);
        print_hex(out, text, off);
        fprintf(out, "\n");
        toc_allocator alloc = *toc_default_allocator();
        toc_arena ar;
        toc_node *root = NULL;
        int err_line = 0;
        toc_sb sb;
        toc_arena_init(&ar, &alloc);
        if (toc_yaml_parse(text, off, &ar, &root, &err_line) == TOC_SUCCESS) {
            toc_sb_init(&sb, &alloc);
            dump_node(&sb, root);
            fprintf(out, "y %zu 0 | %s\n", ndocs, sb.buf ? sb.buf : "");
            toc_sb_free(&sb);
        } else {
            fprintf(out, "y %zu 1 | \n", ndocs);
        }
        toc_arena_free(&ar);
    }

    /* Depth-cap probe: 200-level nested map must fail on both sides. */
    {
        size_t cap = 131072;
        char *text = (char *)malloc(cap);
        size_t off = 0;
        int ok = text != NULL;
        for (int lvl = 0; lvl < 200 && ok; lvl++) {
            int n = snprintf(text + off, cap - off, "k%d:\n", lvl);
            if (n < 0 || (size_t)n >= cap - off) { ok = 0; break; }
            off += (size_t)n;
            for (int sp = 0; sp < (lvl + 1) * 2; sp++) {
                if (off + 1 >= cap) { ok = 0; break; }
                text[off++] = ' ';
            }
        }
        if (ok) {
            size_t id2 = ndocs + 1;
            fprintf(out, "ydoc %zu | ", id2);
            print_hex(out, text, off);
            fprintf(out, "\n");
            toc_allocator alloc = *toc_default_allocator();
            toc_arena ar;
            toc_node *root = NULL;
            int err_line = 0;
            toc_arena_init(&ar, &alloc);
            if (toc_yaml_parse(text, off, &ar, &root, &err_line) == TOC_SUCCESS) {
                fprintf(out, "y %zu 0 | ", id2);
                toc_sb sb;
                toc_sb_init(&sb, &alloc);
                dump_node(&sb, root);
                fprintf(out, "%s\n", sb.buf ? sb.buf : "");
                toc_sb_free(&sb);
            } else {
                fprintf(out, "y %zu 1 | \n", id2);
            }
            toc_arena_free(&ar);
        }
        free(text);
    }

    if (out != stdout) fclose(out);
    return 0;
}
