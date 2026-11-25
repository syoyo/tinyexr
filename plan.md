# Lean formalization review + remaining-work plan (tinyexr)

- **Repo:** `/mnt/disk01/work/tinyexr`, branch `release` (HEAD `e48a52f`, 2026‑11‑13, == `origin/release`, nothing unpushed).
- **Written:** 2026‑11‑23, read-only review; no gate was re-run while writing this plan.
- **Scope reviewed:** `lean/Exr` (tinyexr EXR core), `lean/Texcomp` (texture **compression**), `lean/Tocio` (OCIO), and `tools/resize` (**tir**, currently unformalized).
- **Companion docs:** `AGENTS.md`, `lean/README.md`, `lean/VERIFICATION.md`, `resume-lean.md`.
- **Copies:** in-repo `plan.md` (this file) and `/home/syoyo/.opencode/plan/lean-review-2026-11-23.md`.

---

## 0. Rules that stay in force

- Never push without explicit permission. Before any push run **gitleaks and trufflehog**; both must exit 0.
  ```sh
  RANGE=origin/release..HEAD
  gitleaks detect --source . --log-opts="$RANGE" --no-banner --redact
  ~/go/bin/trufflehog git "file://$(pwd)" --since-commit "${RANGE%%..*}" \
      --results=verified,unknown --no-update --fail
  ```
- **Do not** implement DWAA/DWAB (must stay `EXR_ERROR_UNSUPPORTED`), refactor HTJ2K/JPH internals without coordination, or touch legacy `tinyexr.h`.
- C stays pure C11; hostile-input arithmetic uses `exr_mul_ovf`/`exr_add_ovf`; SIMD must be bit-identical to scalar and scalar is the source of truth.
- Lean: no `sorry`/`admit`; every new file carries BSD-3-Clause; `make lean-axiom-check` stays green; `native_decide` only for approved fixture checks.
- **A Lean change is not done until its C-vs-Lean differential gate shows 0 mismatches**, and docs (`lean/README.md`, `lean/VERIFICATION.md`, conformance matrix) are updated in the same commit.
- Temp files go in the session scratchpad, not `/tmp`.

---

## 1. Baseline evidence (what exists today)

| Area | Lean files / LOC | Top-level `theorem`/`lemma` decls | Gates | Verdict |
|---|---|---|---|---|
| EXR core (`lean/Exr`, `ExrCheck`/`ExrGen`/`CodecGen`) | 46 / 17,305 | 978 | `lean-diff` (126 files), `codec-diff` (8192), `lean-gen-check`, `lean-validation-*` | Proof-heavy reference model |
| texcomp (`lean/Texcomp`) | 102 / 17,924 | 169 | ~40 `texcomp-*-diff` targets | Block layer byte-exact; image-driver layer partial |
| tocio (`lean/Tocio`) | 65 / 9,195 | 166 | 10 checkers (`tocio-diff`, `-yaml`, `-config`, `-proc`, `-codegen`, `-glsl`, `-lut`, `-spi`, `-clf`, `-csp`, `-sqrt`) | Broad executable model + diff gates; thin proof layer |
| resize / tir (`tools/resize`) | **0** | **0** | C unit tests only (naive double oracle) | **Not formalized** |

Last recorded axiom audit: 4,060 first-party theorems, no unexpected axioms (recount in Phase 0; `resume-lean.md` still says 3,919).

### 1.1 Known boundaries already accepted (do not re-open casually)

- DWAA/DWAB out of scope; HTJ2K/JPH internals owned separately; DEFLATE stored/fixed/dynamic decode modelled (encoder-side LZ77 choices unmodelled); B44 perceptual (`p_linear`) tables unmodelled; compressed-deep payloads opaque; RLE equal-size verbatim dispatch is a C quirk the model mirrors.
- tocio: universal arbitrary-mantissa ULP bound, ACES 2.0 hue-indexed runtime tables (`reach_m`/`hue_table`/`cusp_*`), `.cube`/CSP payloads inside `FileTransform`, `Float32 ↔ Float32.Model` kernel equivalence (upstream toolchain obligation).

### 1.2 Gaps found by this review (not tracked today)

**texcomp — `VERIFICATION.md` says "Remaining Texcomp work: none tracked"; that is inaccurate:**
- Placeholder image decoders (length check only, return input): `bc4DecodeImage`, `bc5DecodeImage`, `bc7DecodeImage2`, `etc2DecodeImage`, `eacDecodeImage`, `astcDecodeImage`. Real per-block image loops exist only for BC1 (`Bc1Image.lean`), BC3 (`Bc3DecodeImage.lean`), ASTC LDR (`AstcLdrImgDec.lean`).
- Missing public image encoders (block model already exists): `tc_bc3_compress_rgba8`, `tc_bc5_compress_rg8/rgba8`, `tc_eac_compress_rgba8`, `tc_bc6h_compress_rgb32f`, `tc_bc7_compress_rgba8/rgbaf`, `tc_astc_hdr_compress_rgbaf/rgbf`.
- Missing public decompress wrappers: `tc_bc6h_decompress_rgb16f/rgbaf`, `tc_bc7_decompress_rgba8/rgbaf`, `tc_astc_hdr_decompress_rgbaf`, `tc_etc2_decompress_rgba8`, `tc_eac_decompress_rgba8`.
- `tc_*_compressed_size` equations only partly modelled (`Container.lean`).

**tocio — coverage is broad but most modules are model-only:**
- Zero top-level theorems: `Matrix`, `Range`, `Exponent`, `Log`, `Cdl`, `Lut`, `Builtins`, `YamlEngine` (30 of 65 files have none).
- Proof content concentrated in `FloatModel`/`FloatBridge`/`LoaderBounds` (SPI only)/exponent round trips.
- Unmodelled C: `toc_jit.c` (1,079 lines), SIMD interpreter paths; codegen is byte-identical to C but has no proved *semantics* link to the interpreter.
- YAML work fuel is a validated over-approximation, not a proved exact bound.

**resize / tir — greenfield:**
- 4,151 lines C (`tir_table.c` 410, `tir_core.c` 556, `tir_pipeline.c` 342, `tir_domain.c` 145, `tir_convert.c` 142, scalar + SSE2/AVX2/NEON/SVE kernels).
- Has a `deterministic = 1` scalar mode (bit-identical by contract) and a naive double oracle in `tools/resize/tests/tir_test.c` — both ideal for a Lean model.
- Reusable Lean math already exists: `Tocio.sqrtfExact`, `Tocio.Math` `log2f`/`exp2f`/`powf` ports (needed by `kd_bessel_i0`, `kd_kaiser`, `kd_sinc`, `tir__rangecompress/expand`).

**EXR tail:**
- `src/exr_jph.c` (9,067) + SIMD (2,873) has no Lean model.
- `src/exr_reader.c` (1,989) / `src/exr_writer.c` (2,563) state machines unmodelled; `task.md` documents real bugs exactly there (S1 `parts_cap` + retry, S5 missing writer validation).
- `src/exr_resize.c` (441), `exr_mip.c`, `exr_spectral.c`, `exr_color.c`, `exr_convert.c` unmodelled.
- DEFLATE payload is the only ZIP gap; the encoder is in-tree (`src/exr_deflate.c`, 1,564).

---

## 2. Goal

Close the **coverage** gap in resize, finish the **compression** area's image-driver layer, raise tocio from "diff-gated model" to "proved kernel/loader layer" where tractable, and shrink the EXR tail (JPH wrapper, DEFLATE subset, API state invariants) — while keeping every existing gate green and the docs truthful.

Non-goals: DWA, JPH entropy internals, proving C execution semantics, universal float error bounds, CI rework.

---

## 3. Plan

### Phase 0 — Baseline, docs truth, gate hygiene (S, do first)

**Tasks**
1. Re-run and record: `make lean-check lean-axiom-check lean-diff codec-diff lean-gen-check lean-validation-test`, `make c11-gate test-c fuzz-corpus`, `make tools-test`.
2. Fix `lean/VERIFICATION.md`: header date (says 2026‑11‑09 while content covers 2026‑11‑13), theorem count (recount), and the false "Texcomp remaining: none tracked" line — replace with §1.2.
3. Add `make lean-status`: prints per-area file/LOC/top-level theorem counts and the last gate results; add `make lean-diff-all` aggregating every `*-diff` target (audit `.PHONY` too — several targets are missing from it).
4. Add a "Known gaps" subsection to `lean/README.md` mirroring §1.2 so plan and docs cannot diverge again.

**Acceptance:** all gates green; docs counts match `lean-status`; `lean-diff-all` covers every existing diff target.

---

### Phase 1 — `Tir` formalization (new namespace; P1, highest marginal value)

**Goal:** a scalar, total model of tir with proved table/geometry/kernel invariants plus a bit-exact C-vs-Lean gate — the same architecture as texcomp.

**Wiring**
- `lean/lakefile.lean`: add `Tir.+` to `ExrSpec` globs; add `lean_exe tircheck` (`root := \`TirCheck`).
- `lean/ExrSpec.lean`: `import Tir.Table` (root imports).
- `lean/AxiomAudit.lean`: add `Tir.` / `_private.Tir.` prefixes.
- `Makefile`: `tir-diff` (+ `.PHONY`), include in `lean-diff-all`.

**1.1 `Tir/Geometry.lean` (S)**
Model `axis_geom_init`, `axis_center`, radius/`filter_radius`, vertex flag from `tir_table.c`.
Theorems: `axis_center_zero`, `axis_center_last` (grid-vertex endpoints exact: `0 → 0`, `d-1 → s-1`), `axis_center_mono` (cell-centered and vertex), `ratio_pos`, `support_pos`, `box_halfwidth_pos`. Integer-only where possible; floats as `Float`/`Float32.Model` values with explicit hypotheses.

**1.2 `Tir/Edge.lean` (S)**
Model `edge_map`, `ifloor_div`, `window_fold`, `ar_window`, `win_bound`.
Theorems: `edge_map_nonneg`, `edge_map_lt` (total in-bounds map, `s ≥ 1`), `edge_map_wrap_period`, `edge_map_reflect_period` (period `2n-2`), `window_fold_fast_in_bounds`, `window_fold_run_len_le_win_max`, `ar_window_in_bounds`, `ifloor_div_*` lemmas.

**1.3 `Tir/Table.lean` (M)**
Model `window_weights` (trim + normalize + zero-sum fallback) and `tir__axis_measure` / `tir__axis_fill` classification.
Theorems: `window_weights_len_pos`, `window_trim_left/right` (first/last kept weight is non-zero), `window_zero_sum_single`, `window_sum_one` (idealized real-valued builder: `sum w = 1` when `sum ≠ 0`), and **`measure_fill_agree`**: the `fast_lo`/`fast_hi`/`n_exc` classification produced by the measuring pass is exactly the one the filling pass consumes (the C comment warns disagreement corrupts the arena). Pin actual double→f32 coefficient values with the differential gate.

**1.4 `Tir/Kernels.lean` (M/L)**
Scalar f32 model of the separable two-pass path (`tir_core.c` / `tir_pipeline.c`), including `tir__rangecompress/expand`, `tir__nonfinite_repair`, `tir__normal_decode_row/encode_row` (`tir_domain.c`).
Theorems:
- `resample_identity` at `s = d` for BOX/TRIANGLE (cell-centered);
- `resample_const` (weight normalization ⇒ constant image preserved);
- `resample_bounds` for non-negative kernels (convex weights ⇒ result in footprint range);
- `antiring_within` (result in reduced-footprint `[min,max]`), `clamp_nonneg` (with `antiring=1, clamp_min=0`, output has no negative pixels);
- `premult_unpremult` and `premult_alpha0_keep` (documented rule: RGB preserved where filtered alpha is exactly 0);
- `normal_renorm_magnitude` and `normal_degenerate_fallback` (`(0,0,1)` on cancelled footprints);
- `f16_roundtrip_exact` (representable halves), `unorm8/16_roundtrip`, `unorm_mono`;
- `hicomp_expand_compress` (exact at the `x1 = 0.18` branch, tolerance elsewhere — reuse the `Tocio` exponential models).

**1.5 `Tir/Streaming.lean` (M)**
Model ring buffer + sampler state machine (`tir_core.c`, `tir_thread.c` semantics as observable ordering only).
Theorems: `ring_occupancy_le_support`, `push_pull_progress` (no deadlock: `WOULD_BLOCK` only while a row is needed/available), `pull_out_of_order_rejected`, `threads_output_identical` (serial vs band-parallel as a permutation of deterministic row writes; C already tests this).

**1.6 Differential gate (M)**
- New `test/v3/tir_vectors.c` + `lean/TirCheck.lean` + `make tir-diff`.
- Records: dims (incl. 1, 2, non-square, up/down), channel count 1–4, pixel type F32/F16/U8/U16, filter × edge × registration × mode (general/normal/heightmap), alpha mode, antiring/clamp, nonfinite policy, `deterministic = 1`.
- Compare full output bytes bit-exactly against `tir_resize`; include negative controls (e.g. forced SIMD level must match scalar; wrap y-buffer path; band threads == serial).
- Reuse the naive double reference only as an independent sanity oracle in the C generator, not as the Lean comparison.

**Acceptance:** no `sorry`; axiom audit green; `tir-diff` 0 mismatches on ≥ 2 seeds; `resize-test`, `resize-c11-gate` unchanged and green; `Tir` rows added to README/VERIFICATION.

---

### Phase 2 — texcomp image layer (P1, cheap completeness win)

**2.1 Real image decoders (S each)**
Replace the six placeholders with per-block loops (template: `Bc3DecodeImage2`):
`bc4DecodeImage`, `bc5DecodeImage`, `bc7DecodeImage2`, `etc2DecodeImage`, `eacDecodeImage`, `astcDecodeImage` — or add `*ImageDec.lean` files if names/imports clash (remember the earlier `Bc6hMode*` name collision lesson).
Theorems: `*_none_if_small`, `*_length` (`w*h*4` RGBA8 / `w*h` single channel), `*_block_read_in_bounds`, partial-edge coverage (`ceil` block counts).

**2.2 Public image encoders (M each)**
Add drivers over existing block models:
- `Texcomp/Bc3EncodeImage.lean` — `tc_bc3_compress_rgba8` (BC1 colour + BC4 alpha per 4×4 block, row-major gather).
- `Texcomp/Bc5EncodeImage.lean` — `tc_bc5_compress_rg8` / `rgba8`.
- `Texcomp/EacEncodeImage.lean` — `tc_eac_compress_rgba8` (RGB + optional EAC alpha, column-major gather — note the ETC2/Uni difference).
- `Texcomp/Bc6hEncodeImage.lean` — `tc_bc6h_compress_rgb32f` (float→half, per-block driver `tc_encode_bc6h_block_*`, image gather).
- `Texcomp/Bc7EncodeImage.lean` — `tc_bc7_compress_rgba8/rgbaf` (options plumbing: quick/pca/mode_mask/rdo; public driver).
- `Texcomp/AstcHdrEncodeImage.lean` — `tc_astc_hdr_compress_rgbaf/rgbf` (block model in `AstcHdrEnc.lean`).
Theorems: `*_length = *_compressed_size`, edge-clamp/gather coverage, option-default equality with `*_options_init`.

**2.3 Decompress wrappers (S)**
`tc_bc6h_decompress_rgb16f/rgbaf`, `tc_bc7_decompress_rgba8/rgbaf`, `tc_astc_hdr_decompress_rgbaf`, `tc_etc2_decompress_rgba8`, `tc_eac_decompress_rgba8` over the real image decoders; prove output lengths/formats.

**2.4 Gates (M)**
Mirror `astc_hdrimg_vectors.c` / `astc_ldrimg_vectors.c`: one `test/v3/<codec>_img_vectors.c` per codec; compare **full compressed byte stream** and **full decoded image**; include odd dimensions and 1-pixel images. Wire `make texcomp-<codec>-img-diff`, add to `.PHONY` and `lean-diff-all`.

**Acceptance:** every public `tc_*_compress_*` / `tc_*_decompress_*` in `tools/texcomp/include/texcomp.h` maps to a Lean def and a gate (or an explicit boundary row); `VERIFICATION.md` claim corrected.

---

### Phase 3 — tocio proof hardening (P2)

**3.1 Loader bounds for CLF/CSP/cube (M)** — extend `Tocio/LoaderBounds.lean` (today SPI only):
- every parser loop consumes input (progress) for `Tocio/ClfXml.lean`, `Clf.lean`, `Csp.lean`, `LutFile.lean`;
- `toc_values_fit`-style soundness: dimension products checked before allocation; short buffers cannot reach stride-3/trilinear kernels;
- XML nesting depth cap; CSP prelut resample bounds.
Theorems mirror `spi1dVals_length` / `spiValuesFit_le`.

**3.2 YAML exactness (M)** — replace the `8 * length + 1024` fuel over-approximation with a structural measure (or prove `calls ≤ fuel` and the height bound exactly); prove the 128 depth cap boundary (127 parses, 128/129 fail) as a theorem, not a fixture.

**3.3 Kernel laws on `Float32.Model` (L)** — reuse the `FloatModel` pattern:
- `Tocio/MatrixModel.lean`: identity/associativity (real model), inverse laws + condition hypothesis, transfer to `f32Ops`.
- `Tocio/LutModel.lean`: linear interpolation exact at nodes, trilinear exact at corners, monotonicity for monotone tables.
- `Tocio/CdlModel.lean`: forward∘inverse within the documented 2e-3 tolerance on the non-negative grid (make the fixture a theorem where possible).
- `Tocio/FfModel.lean`: inverse-pair tolerance laws for the 22 styles (GamutComp13 may stay diff-only per AGENTS.md).
- `Tocio/ExpLinearModel.lean`, `LogCameraModel.lean`: identity/round-trip laws consistent with `mPowf_one_ulp_bound`.

**3.4 Codegen semantics (M/L)** — the strongest remaining Tocio item:
- `Tocio/CodegenSemantics.lean`: an expression AST + evaluator; prove `eval (emit op) x = apply op x` (per op, with the same `KernelOps` bridge) for the AOT-C and GLSL emitters; then connect the existing byte-identical text to the AST (parse or shared constructor).
- Keep the byte-identical gates as the C link; this adds the *semantic* link.

**3.5 JIT / SIMD parity (S, C-side)** — add `make tocio-jit-diff` (JIT output vs interpreter per op) and `tocio-simd-diff` (SSE2/AVX2/NEON vs scalar) rather than modelling `toc_jit.c`; document as boundary if JIT cannot be driven headlessly.

**3.6 FileTransform `.cube`/CSP (S)** — extend `FileMap` dispatch to `.cube` via `Tocio.LutFile` and CSP payloads via `Tocio.Csp`; add vectors to `tocio-proc-diff`.

**Acceptance:** each new law is kernel-checked (`decide` only where finite and exact); no new `native_decide`; axiom audit green; diff gates 0 mismatches; boundaries list updated.

---

### Phase 4 — EXR tail (P3, coordinate)

**4.1 JPH wrapper model (M/L, needs JPH owner sign-off)**
`Exr/Jph.lean` + `JphCheck.lean`: HT marker sequence (SOC/SIZ/CAP/COD/QCD/QCC/NLT/SOT/SOD/EOC), profile/RPCL checks, tile/codeblock geometry, packet-inclusion tag-tree structure, codeblock descriptor bounds — **excluding** cleanup/SPP/MRP entropy decode. Gate on the existing in-tree JPH fixtures and `~/work/openexr-images` HT files; compare accept/reject + parsed geometry against `src/exr_jph.c`.

**4.2 DEFLATE subset (M)**
`Exr/Deflate.lean` + `Exr/DeflateDynamic.lean`: stored, fixed and dynamic-Huffman block decoding with LZ77 overlap copy and canonical Huffman tables, gated by `make deflate-diff` (9 streams, including 3 BTYPE=2 blocks from `exr_deflate_zlib`). Encoder-side LZ77 choice and a universal `decode∘encode` theorem remain boundaries.

**4.3 Reader/writer invariants (M)**
`Exr/ReaderState.lean`: abstract op state machine (open → parse → read/decode/close, retry after error) proving the error latch/idempotency, `parts_cap ≥ num_parts`, and ownership (no double free / no leak) — directly targeting `task.md` S1/S2. `Exr/HeaderValidate.lean`: one validation predicate used by both sides; prove `reader_accepts ⇒ validate` and `writer_emits ⇒ validate` (S5). Pure Lean model + targeted C negative-control tests.

**4.4 `exr_resize.c` disposition (S)**
Either fold `exr_resize_float` into the `Tir` model (preferred: tir is 2–5× faster and already tested) or declare it legacy with a boundary note. Do not duplicate the model.

**4.5 B44 perceptual tables (optional, S)** only if the `Tocio.Math` `powf` port makes the `p_linear` table generation cheap; otherwise keep the boundary.

**Acceptance:** JPH gate 0 mismatches on fixtures; DEFLATE subset gate 0 mismatches; state-machine theorems compile with no `sorry`; docs updated; JPH changes coordinated.

---

### Phase 5 — Close-out (S)

- Update `lean/README.md` module table + conformance matrix (Tir rows, texcomp image layer, tocio law modules, EXR JPH/DEFLATE/state).
- Update `lean/VERIFICATION.md` evidence table with exact vector counts; move completed boundaries to "covered", keep honest ones.
- Run the full matrix: `lean-check lean-axiom-check lean-diff codec-diff lean-gen-check lean-validation-test lean-validation-sanitize`, `lib c11-gate test-c fuzz-corpus`, `tools-test`, `texcomp-*`, `tocio-*`, new `tir-*`.
- Secret scans; CI green; only then ask for push permission.
- Record the next boundaries explicitly (e.g. JPH entropy, dynamic DEFLATE, arbitrary-mantissa ULP, JIT).

---

## 4. Ordering and effort

| Order | Item | Effort | Why now |
|---|---|---|---|
| 0 | Baseline + docs + `lean-status`/`lean-diff-all` | S | Cheap; unblocks trustworthy status |
| 1 | Tir geometry/edge/table + gate | M | New area, provable invariants, memory-safety relevance |
| 2 | Tir kernels/streaming | M/L | Completes the model; needs Tocio math reuse |
| 3 | texcomp image decoders (placeholders) | S/S/S/S/S/S | Cheapest way to make "compression complete" honest |
| 4 | texcomp image encoders + wrappers + gates | M×6 | Finishes the public API |
| 5 | tocio loader bounds + YAML exactness | M+M | Turns fixtures into proofs |
| 6 | tocio kernel laws + codegen semantics | L | Deepest remaining proof gap |
| 7 | EXR JPH wrapper (coordinated) | M/L | Largest unmodelled codec surface |
| 8 | EXR DEFLATE subset + reader/writer state | M+M | Closes ZIP boundary; targets known bugs |
| 9 | Close-out | S | Docs, full matrix, scans |

Each numbered item is a commit-sized slice with its own gate; do not batch a model and its gate in different commits.

---

## 5. Definition of done (per slice)

1. Model + theorems compile, no `sorry`, `make lean-axiom-check` green.
2. A C vector generator + Lean checker exists; **0 mismatches**; at least one negative control (mutation) proves the gate can fail.
3. `make c11-gate` and the relevant C tests unchanged/green (C edits only where the model exposed a real bug, with the bug recorded in `lean/README.md`).
4. `lean/README.md` + `lean/VERIFICATION.md` updated in the same commit.
5. Gate wired into `Makefile`, `.PHONY`, `lean-diff-all`, `ExrSpec.lean`, and (for new namespaces) `AxiomAudit.lean`.
6. No push without explicit permission + both secret scans clean.

---

## 6. Risks / open questions

- **tir table build uses double + libm** (`sin`, `exp`, `sqrt`): prove the *idealized* builder laws in ℝ, pin actual values by the gate; treat `kd_bessel_i0`/`kd_kaiser` as the modelling boundary unless the Tocio `powf`/`sqrt` ports suffice.
- **Float proof cost**: kernel laws may need `Float32.Model` plus tolerance predicates; if a law resists, downgrade to a diff-gated fixture and record the boundary — do not introduce `native_decide` outside the approved list.
- **texcomp naming collisions**: `Bc6hMode*` (decoder) vs `Bc6hEnc*` (encoder) already collided once; choose `*EncodeImage`/`*ImageDec` names up front.
- **JPH ownership**: do not touch `src/exr_jph.c` internals; wrapper model only, with the owner's review.
- **Do not overclaim**: every "covered" row must point at a gate or a theorem; placeholder models must be labelled as such.
