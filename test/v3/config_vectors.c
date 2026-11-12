/* Config-query differential vectors: C `toc_config.c` lookups vs the Lean
 * model (`Tocio/ConfigQuery.lean`).
 *
 * For each embedded config document the generator emits:
 *   cdoc <id> | <hex of the document text>
 *   c <id> <v> | <query transcript>
 * where v = 0 means TOC_SUCCESS and v = 1 means a YAML parse error (empty
 * transcript). The transcript is a `;`-separated list of `key=value`
 * entries (values escaped: `\\`, `;`, `=`, `|`, newline; `~` means NULL)
 * covering the public query surface: colorspace counts/names, name and
 * alias lookups, family/encoding/isdata, display-section membership,
 * role resolution, per-colorspace transform attribute choice + invert
 * flag, display/view enumeration, per-view looks lists, view transforms
 * + default, looks, and active displays/views.
 *
 * Query enumeration is content-derived (sequence/map order), so the Lean
 * checker builds the identical transcript from its own parse tree.
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

/* Escape a transcript value; NULL renders as `~`. */
static void qesc(toc_sb *sb, const char *s) {
    if (!s) {
        toc_sb_putc(sb, '~');
        return;
    }
    for (; *s; ++s) {
        char c = *s;
        if (c == '\\' || c == ';' || c == '=' || c == '|' || c == '\n') {
            toc_sb_putc(sb, '\\');
            toc_sb_putc(sb, c == '\n' ? 'n' : c);
        } else {
            toc_sb_putc(sb, c);
        }
    }
}

static void qent(toc_sb *sb, const char *key, const char *val) {
    if (sb->len) toc_sb_putc(sb, ';');
    toc_sb_puts(sb, key);
    toc_sb_putc(sb, '=');
    qesc(sb, val);
}

static void qent_num(toc_sb *sb, const char *key, long v) {
    char b[32];
    snprintf(b, sizeof(b), "%ld", v);
    qent(sb, key, b);
}

static void qent_key(toc_sb *sb, const char *prefix, int i, const char *suffix,
                     const char *val) {
    char b[96];
    snprintf(b, sizeof(b), "%s%d%s", prefix, i, suffix);
    qent(sb, b, val);
}

/* Which attribute `toc_cfg_cs_transform` returns (by identity), or NULL. */
static const char *cs_transform_attr(const toc_node *cs, int want_to_ref,
                                     int *inv) {
    static const char *names[6] = {
        "to_reference", "from_reference",
        "to_scene_reference", "from_scene_reference",
        "to_display_reference", "from_display_reference",
    };
    const toc_node *t = toc_cfg_cs_transform(cs, want_to_ref, inv);
    if (!t) return NULL;
    for (int i = 0; i < 6; i++)
        if (toc_node_map_get(cs, names[i]) == t) return names[i];
    return "?";
}

static const char *node_name(const toc_node *n) {
    return n ? toc_node_scalar(toc_node_map_get(n, "name")) : NULL;
}

int main(int argc, char **argv) {
    FILE *out = stdout;
    if (argc > 1) {
        out = fopen(argv[1], "w");
        if (!out) return 1;
    }

    static const char *docs[] = {
        /* 0: full v2-style config with tags, aliases (seq + scalar),
         *    roles, displays/views/looks, view transforms, active lists */
        "ocio_profile_version: 2\n"
        "roles:\n"
        "  scene_linear: ACEScg\n"
        "  color_timing: ACEScct\n"
        "  data: Raw\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: ACEScg\n"
        "    family: ACES\n"
        "    encoding: scene-linear\n"
        "    to_scene_reference: !<MatrixTransform> {matrix: [1, 0, 0, 0]}\n"
        "  - !<ColorSpace>\n"
        "    name: ACEScct\n"
        "    aliases: [cct, aces_cct]\n"
        "    family: ACES\n"
        "    encoding: log\n"
        "    from_reference: !<ExponentTransform> {value: 2.2}\n"
        "  - !<ColorSpace>\n"
        "    name: Raw\n"
        "    isdata: true\n"
        "  - !<ColorSpace>\n"
        "    name: ACES2065-1\n"
        "    aliases: aces\n"
        "    to_reference: !<MatrixTransform> {matrix: [1]}\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: sRGB - Display\n"
        "    to_display_reference: !<MatrixTransform> {matrix: [1]}\n"
        "displays:\n"
        "  sRGB:\n"
        "    - !<View> {name: ACES SDR, colorspace: sRGB - Display, looks: 'A, B'}\n"
        "    - !<View> {name: Raw, colorspace: Raw, looks: }\n"
        "  sRGB2:\n"
        "    - !<View> {name: Only, colorspace: ACEScg}\n"
        "view_transforms:\n"
        "  - !<ViewTransform> {name: ACES SDR VT}\n"
        "  - !<ViewTransform> {name: Other}\n"
        "default_view_transform: Other\n"
        "looks:\n"
        "  - !<Look> {name: A}\n"
        "  - !<Look> {name: B}\n"
        "active_displays: [sRGB, sRGB2]\n"
        "active_views: [ACES SDR]\n",
        /* 1: empty config */
        "",
        /* 2: YAML parse error (tab indentation) */
        "roles:\n\tbad: 1\n",
        /* 3: alias lookup priority: display colorspace shadowing */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: SceneCS\n"
        "    aliases: [shared, scene_only]\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: DisplayCS\n"
        "    aliases: [shared, disp_only]\n",
        /* 4: role resolution chains, missing roles, non-map sections */
        "roles:\n"
        "  scene_linear: linear_cs\n"
        "  aces_intermediate: scene_linear\n"
        "colorspaces: not_a_seq\n"
        "displays: not_a_map\n"
        "looks: nope\n"
        "active_displays: only_one\n",
        /* 5: colorspace without a name; transform priority v1 vs v2 */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    family: unnamed\n"
        "    to_reference: !<A> {x: 1}\n"
        "    to_scene_reference: !<B> {x: 2}\n"
        "  - !<ColorSpace>\n"
        "    name: Both\n"
        "    from_reference: !<C> {x: 3}\n"
        "    to_display_reference: !<D> {x: 4}\n"
        "  - !<ColorSpace>\n"
        "    name: SceneOnly\n"
        "    to_scene_reference: !<E> {x: 5}\n"
        "    from_display_reference: !<F> {x: 6}\n",
        /* 6: look lists: comma/space quirks, missing look references */
        "displays:\n"
        "  d1:\n"
        "    - !<View> {name: V1, colorspace: cs, looks: 'A,B , C '}\n"
        "    - !<View> {name: V2, colorspace: cs, looks: 'nosuch'}\n"
        "looks:\n"
        "  - !<Look> {name: A}\n"
        "  - !<Look> {name: B}\n"
        "  - !<Look> {name: C}\n",
        /* 7: singular view_transform section + default naming a missing VT */
        "view_transform:\n"
        "  - !<ViewTransform> {name: First}\n"
        "  - !<ViewTransform> {name: Second}\n"
        "default_view_transform: Missing\n",
        /* 8: display names and views without names */
        "displays:\n"
        "  plain:\n"
        "    - !<View> {colorspace: cs}\n"
        "    - !<View> {name: Named, colorspace: cs}\n"
        "  empty: []\n",
        /* 9: isdata variants and alias list with odd entries */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: D1\n"
        "    isdata: 1\n"
        "  - !<ColorSpace>\n"
        "    name: D2\n"
        "    isdata: yes\n"
        "  - !<ColorSpace>\n"
        "    name: AliasOdd\n"
        "    aliases: [ '', extra ]\n",
        /* 10: display-section membership via roles and display aliases */
        "roles:\n"
        "  scene_linear: linear_cs\n"
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: linear_cs\n"
        "  - !<ColorSpace>\n"
        "    name: scene_linear\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: DisplayOnly\n"
        "    aliases: [linear_cs]\n",
        /* 11: valid default view transform wins over the first entry */
        "view_transforms:\n"
        "  - !<ViewTransform> {name: First}\n"
        "  - !<ViewTransform> {name: Second}\n"
        "default_view_transform: Second\n",
        /* 12: duplicate names/aliases: first match wins */
        "colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: dup\n"
        "    family: first\n"
        "  - !<ColorSpace>\n"
        "    name: dup\n"
        "    family: second\n"
        "  - !<ColorSpace>\n"
        "    name: aliased\n"
        "    aliases: [dup, twice]\n"
        "display_colorspaces:\n"
        "  - !<ColorSpace>\n"
        "    name: dup\n"
        "    family: display\n",
        /* 13: non-sequence display value and empty view transform seq */
        "displays:\n"
        "  scalar_display: nope\n"
        "  real:\n"
        "    - !<View> {name: V}\n"
        "view_transforms: []\n",
        /* 14: active lists as non-sequence values */
        "active_displays: single\n"
        "active_views: [v1]\n",
        /* 15: look-list separators and comments */
        "displays:\n"
        "  d:\n"
        "    - !<View> {name: V, colorspace: c, looks: ' , A ,, B '}\n"
        "looks:\n"
        "  - !<Look> {name: A}\n"
        "  - !<Look> {name: B}\n",
    };

    size_t ndocs = sizeof(docs) / sizeof(docs[0]);
    for (size_t id = 0; id < ndocs; id++) {
        const char *text = docs[id];
        size_t len = strlen(text);
        toc_config *cfg = NULL;
        toc_result rc;
        toc_sb sb;

        fprintf(out, "cdoc %zu | ", id);
        print_hex(out, text, len);
        fprintf(out, "\n");

        rc = toc_config_parse(text, len, NULL, &cfg);
        if (rc != TOC_SUCCESS || !cfg) {
            fprintf(out, "c %zu 1 | \n", id);
            if (cfg) toc_config_free(cfg);
            continue;
        }

        toc_sb_init(&sb, &cfg->alloc);

        /* colorspaces */
        {
            int n = toc_config_num_colorspaces(cfg);
            qent_num(&sb, "ncs", n);
            const toc_node *seq = toc_node_map_get(cfg->root, "colorspaces");
            for (int i = 0; i < n; i++) {
                const char *nm = toc_config_colorspace_name(cfg, i);
                const toc_node *cs = seq->items[i];
                int inv;
                const char *attr;
                qent_key(&sb, "csv.", i, "", nm);
                qent_key(&sb, "fd.", i, "",
                         nm ? node_name(toc_cfg_find_colorspace(cfg, nm)) : NULL);
                qent_key(&sb, "fam.", i, "",
                         toc_node_scalar(toc_node_map_get(cs, "family")));
                qent_key(&sb, "enc.", i, "",
                         toc_node_scalar(toc_node_map_get(cs, "encoding")));
                qent_key(&sb, "data.", i, "", toc_cfg_is_data(cs) ? "1" : "0");
                {
                    char b[32];
                    snprintf(b, sizeof(b), "%d",
                             nm ? toc_cfg_cs_in_display_section(cfg, nm) : 0);
                    qent_key(&sb, "inds.", i, "", b);
                }
                attr = cs_transform_attr(cs, 1, &inv);
                qent_key(&sb, "to.", i, "", attr);
                qent_key(&sb, "toinv.", i, "", inv ? "1" : "0");
                attr = cs_transform_attr(cs, 0, &inv);
                qent_key(&sb, "fr.", i, "", attr);
                qent_key(&sb, "frinv.", i, "", inv ? "1" : "0");
                {
                    const toc_node *al = toc_node_map_get(cs, "aliases");
                    size_t nal = 0;
                    char kb[64];
                    if (al && al->kind == TOC_NODE_SEQ) nal = al->n_items;
                    else if (al && al->kind == TOC_NODE_SCALAR) nal = 1;
                    snprintf(kb, sizeof(kb), "nal.%d", i);
                    qent_num(&sb, kb, (long)nal);
                    for (size_t j = 0; j < nal; ++j) {
                        const char *an = (al->kind == TOC_NODE_SEQ)
                                             ? toc_node_scalar(al->items[j])
                                             : toc_node_scalar(al);
                        snprintf(kb, sizeof(kb), "al.%d.%zu", i, j);
                        qent(&sb, kb, an);
                        snprintf(kb, sizeof(kb), "alr.%d.%zu", i, j);
                        qent(&sb, kb,
                             an ? node_name(toc_cfg_find_colorspace(cfg, an)) : NULL);
                    }
                }
            }
        }
        /* display_colorspaces */
        {
            const toc_node *seq = toc_node_map_get(cfg->root, "display_colorspaces");
            int n = (seq && seq->kind == TOC_NODE_SEQ) ? (int)seq->n_items : 0;
            qent_num(&sb, "ndcs", n);
            for (int i = 0; i < n; i++)
                qent_key(&sb, "dcs.", i, "",
                         node_name(seq->items[i]));
        }
        /* roles */
        {
            const toc_node *roles = toc_node_map_get(cfg->root, "roles");
            int n = (roles && roles->kind == TOC_NODE_MAP) ? (int)roles->n_pairs : 0;
            qent_num(&sb, "nroles", n);
            for (int i = 0; i < n; i++) {
                const char *k = roles->keys[i];
                char kb[96];
                snprintf(kb, sizeof(kb), "role.%d.k", i);
                qent(&sb, kb, k);
                snprintf(kb, sizeof(kb), "role.%d.v", i);
                qent(&sb, kb, toc_config_role(cfg, k));
                snprintf(kb, sizeof(kb), "role.%d.r", i);
                qent(&sb, kb, toc_cfg_resolve_role(cfg, k));
            }
        }
        /* displays */
        {
            int n = toc_config_num_displays(cfg);
            qent_num(&sb, "ndisp", n);
            for (int i = 0; i < n; i++) {
                const char *dn = toc_config_display_name(cfg, i);
                int nv = dn ? toc_config_num_views(cfg, dn) : 0;
                char kb[96];
                qent_key(&sb, "disp.", i, "", dn);
                snprintf(kb, sizeof(kb), "nviews.%d", i);
                qent_num(&sb, kb, nv);
                const toc_node *vseq =
                    toc_node_map_get(toc_node_map_get(cfg->root, "displays"), dn);
                for (int j = 0; j < nv; j++) {
                    const char *vn = toc_config_view_name(cfg, dn, j);
                    const toc_node *vnode = vseq->items[j];
                    const char *lnames[32];
                    int nl;
                    snprintf(kb, sizeof(kb), "view.%d.%d", i, j);
                    qent(&sb, kb, vn);
                    nl = toc_cfg_view_looks(vnode, lnames, 32);
                    snprintf(kb, sizeof(kb), "nvl.%d.%d", i, j);
                    qent_num(&sb, kb, nl);
                    for (int k = 0; k < nl; k++) {
                        snprintf(kb, sizeof(kb), "vl.%d.%d.%d", i, j, k);
                        qent(&sb, kb, lnames[k]);
                    }
                }
            }
        }
        /* view transforms */
        {
            int n = toc_config_num_view_transforms(cfg);
            qent_num(&sb, "nvt", n);
            for (int i = 0; i < n; i++)
                qent_key(&sb, "vt.", i, "", toc_config_view_transform_name(cfg, i));
            qent(&sb, "vtd", node_name(toc_cfg_default_view_transform(cfg)));
        }
        /* looks */
        {
            int n = toc_config_num_looks(cfg);
            qent_num(&sb, "nlooks", n);
            for (int i = 0; i < n; i++) {
                const char *ln = toc_config_look_name(cfg, i);
                qent_key(&sb, "look.", i, "", ln);
                qent_key(&sb, "lkf.", i, "",
                         ln ? node_name(toc_cfg_find_look(cfg, ln)) : NULL);
            }
        }
        /* active displays/views */
        {
            int n = toc_config_num_active_displays(cfg);
            qent_num(&sb, "nad", n);
            for (int i = 0; i < n; i++)
                qent_key(&sb, "ad.", i, "",
                         toc_config_active_display_name(cfg, i));
            n = toc_config_num_active_views(cfg);
            qent_num(&sb, "nav", n);
            for (int i = 0; i < n; i++)
                qent_key(&sb, "av.", i, "",
                         toc_config_active_view_name(cfg, i));
        }

        fprintf(out, "c %zu 0 | %s\n", id, sb.buf ? sb.buf : "");
        toc_sb_free(&sb);
        toc_config_free(cfg);
    }

    if (out != stdout) fclose(out);
    return 0;
}
