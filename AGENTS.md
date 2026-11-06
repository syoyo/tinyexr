# AGENTS.md — TinyEXR v3 (pure-C11 rewrite)

Guidance for AI agents working on the pure-C11 EXR loader/writer under
`include/exr.h` + `src/*.c` (private decls in `src/exr_internal.h`). The legacy
v1 `tinyexr.h` at the repo root is a dependency of older tests — leave it
untouched.

## Scope / non-goals

- **DWA (DWAA / DWAB) is intentionally NOT supported — do not implement it.**
  We do not plan to support the lossy DCT DWA codecs. Leave
  `EXR_COMPRESSION_DWAA` / `EXR_COMPRESSION_DWAB` returning
  `EXR_ERROR_UNSUPPORTED` in the codec dispatch; do not add a DCT/zigzag/AC-DC
  decoder. Do not spend effort here.
- HTJ2K / JPH (`src/exr_jph.c`, `EXR_COMPRESSION_HTJ2K*`) is owned separately —
  don't refactor it without coordination.

## Build / test / validate

- `make lib`        — build `build/libtinyexr3.a` (`-std=c11 -Wall -Wextra -Werror`).
- `make c11-gate`   — strict pure-C11 syntax gate over all `src/*.c` (must stay green).
- `make test-c`     — unit tests under ASan+UBSan (note: runs with `detect_leaks=0`).
- `make fuzz-corpus`— replay `test/unit/regression/*` under ASan+UBSan+**LSan**
  (this is what catches error-path leaks; keep it green).
- `make fuzz-corpus-asan` — same corpus replay with `ASAN_OPTIONS=detect_leaks=0`;
  use only in ptrace/sandboxed local sessions where LSan aborts with
  "LeakSanitizer does not work under ptrace". It is a crash/ASan/UBSan fallback,
  not a replacement for the LSan gate.
- `make fuzz`       — clang/libFuzzer coverage-guided target (`build/fuzz_v3`).
- `make bench`      — codec + SIMD-kernel throughput.

Validation method: cross-check against the legacy v1 loader
(`LoadEXRImageFromFile` / `LoadDeepEXR`) and OpenEXR CLI tools
(`exrheader`, `exrmaketiled`, `exrmultipart`). `oiiotool` is broken here
(missing libboost). For lossy codecs the bar is "OpenEXR reads my output and my
own decode matches"; for lossless it is byte-identical.

## Secret-scanning audit (run before/after committing)

Audit new commits for accidentally-committed credentials with **both**
gitleaks and trufflehog. Tools default to `~/go/bin/` (trufflehog lives there;
gitleaks may also be on `PATH`). Both must exit 0 (no findings) before pushing.

```sh
# Scan only the new commits: RANGE = <last-known-clean>..HEAD (e.g. a tag or the
# upstream commit you branched from). Use --all / drop --log-opts for a full sweep.
RANGE=origin/release..HEAD

# gitleaks: history scan, redact matches, fail (non-zero) on any leak.
gitleaks detect --source . --log-opts="$RANGE" --no-banner --redact

# trufflehog: scan the same range; --fail makes it exit non-zero on a finding.
~/go/bin/trufflehog git "file://$(pwd)" --since-commit "${RANGE%%..*}" \
    --results=verified,unknown --no-update --fail
```

Both should report "no leaks found" / `verified_secrets: 0` and exit 0. If either
flags something, do not push — rewrite history to drop the secret and rotate it.

`.gitleaks.toml` (auto-loaded from the repo root) allowlists the vendored
`deps/zstd/` amalgamation, whose xxHash key-mixing intrinsics (`key_lo`/`key_hi`)
trip the generic-api-key heuristic — those are upstream constants, not secrets.
Keep first-party code out of the allowlist.

## Conventions

- Every new file gets the BSD-3-Clause header. Ported code keeps upstream
  attribution (fpng = public domain, fpnge = Apache-2.0; see `NOTICE`).
- All hostile-input arithmetic goes through `exr_mul_ovf` / `exr_add_ovf`.
  Error paths must leave outputs owning nothing (`exr_part_free` on failure).
- SIMD kernels use `__attribute__((target(...)))` + a runtime CPUID vtable so
  everything compiles at baseline; scalar fallback is always present and is the
  source of truth (SIMD must be bit-identical).

## lean/ — Lean 4 formalization of the OpenEXR format

`lean/` holds the machine-checked model: the structural encode/decode
inverse theorems (`parseFile_emit` for arbitrary well-formed files), the
container/parser-emitter layout, and the PXR24/B44/RLE/ADLER32/Deep codec
models. It is validated differentially against this C library and the
OpenEXR corpus — no Lean change is "done" until its gate is green.

Build / test:
- `make lean-check`   — full `lake build` of `ExrSpec` + the exes (must stay green).
- `make lean-diff`    — structural differential: Lean model vs tinyexr v3 +
  corpus (`test/v3/lean_diff.py`, `build/lean-gen/*`, `~/work/openexr-images`).
- `make codec-diff`   — codec differential (`test/v3/codec_diff.c` vs
  `CodecGen.lean` vectors): PXR24, B44/B44A, RLE and ADLER32 bit-exact.
- `make lean-gen`     — regenerate the Lean structural fixtures
  (`build/lean-gen/*.exr`); `make lean-gen-update` commits them;
  `make lean-gen-check` fails if the committed fixtures go stale.

Conventions (matching the C side):
- Same scope exclusions as the C implementation: DWA is not supported and
  the DEFLATE payload bitstream is not modelled (wrapper checksum/structure
  only — see `Exr/Zip.lean` and `lean/README.md` for documented boundaries).
- The Lean model follows OpenEXR's library where the spec text is stricter
  (e.g. missing `maxSamplesPerPixel` on deep parts is accepted) — note such
  leniency in `lean/README.md` rather than silently diverging.
- Codec models aim for bit-exactness with the C codecs (byte-identical);
  encoder-side disagreements are found by `codec-diff`, structural ones by
  `lean-diff` — fixing the model, not breaking the C, unless the C is proven
  wrong (then record the bug in `lean/README.md`).

### tocio (sandbox/tocio) — pure-C11 OCIO Config Processor

Build / test:
- `make tocio-c11-gate`   — C11 strict gate for all `sandbox/tocio/src/*.c`
- `make tocio-freestanding-gate` — freestanding gate (nm-scans for libm symbols)
- `make tocio-test`       — unit tests (ASan+UBSan+LSan)
- `make tocio-fuzz`       — libFuzzer target (`build/toc_fuzz`); replay fixed
  findings with `./build/toc_fuzz sandbox/tocio/tests/fuzz-regression/*`
- `make wasm-tocio`       — WASM/emscripten build (`build/tocio.mjs` + `.wasm`)
- `make wasm-tocio-test`  — WASM smoke check via Node (set PATH to emsdk's node)
- `make tocio-wasm`       — WASM build of core

## tocio status — all phases

```
Phase 1 (FixedFunction)    ████████████████████ 100%  106 tests
Phase 2 (view_transform)   ████████████████████ 100%  118 tests
Phase 3 (CDL inverse)      ████████████████████ 100%  118 tests  
Phase 4 (YAML keys)        ████████████████████ 100%  127 tests
Phase 5 (looks/aliases)    ████████████████████ 100%  127 tests
Phase 6 (file LUTs)        ████████████████████ 100%  127 tests
```

### Phase 1 — FixedFunction styles (all OCIO styles)

**Done:**
- `toc_ff_style` enum extended to 22 values in `tocio.h` (invert-pair pattern)
- All math kernels in `toc_builtins.c`:
  - ACES Glow 03/10 fwd+inv (sigmoid, saturation-weighted)
  - ACES Red Mod 03/10 fwd+inv (B-spline hue lobe, quadratic inv)
  - ACES DarkToDim 10 fwd+inv (luma gamma scale)
  - ACES GamutComp 13 fwd+inv (per-axis distance compression, 7 params)
  - RGB_TO_HSV / HSV_TO_RGB (extended range: negative V, S>1)
  - XYZ_TO/TO_xyY, XYZ_TO/TO_uvY, XYZ_TO/TO_LUV (D65)
- Freestanding `ff_atan2f` (minimax rational) replaces libc `atan2f`
- `toc_lower_fixedfunc` string parser extended for all styles + params
- AOT-C codegen: helper `static` source strings + per-op `case TOC_OP_FIXEDFUNC:` emit
- GLSL codegen: per-style inline math emit for all styles (RedMod inv & GamutComp13 fall back to CPU)
- Round-trip tests in `toc_test.c` for all 10 style pairs
- GLSL shader compilation verified via glslangValidator for ES3.0/GLSL330/Vulkan450 targets

### Phase 2 — view_transform / display_view path

**Done:**
- `toc_cfg_find_view_transform` — look up ViewTransform by name from `view_transform` top-level seq
- `toc_processor_from_display_view` handles three cases:
  - Simple views (colorspace key) → src → colorspace
  - VT views (view_transform key) → src → reference → vt.from_reference → display_colorspace
  - Both support optional looks
- Config introspection: `toc_config_num_view_transforms`, `toc_config_view_transform_name`

### Phase 3 — CDL inverse

**Done:**
- CDL inverse decomposed at lowering time into basic ops:
  - Inverse saturation → MatrixTransform
  - Inverse power → ExponentTransform  
  - Inverse (slope, offset) → RangeTransform
- Forward CDL remains a single TOC_OP_CDL (all backends handle it)
- Round-trip test cdlin↔lin passes within 2e-3

### Phase 4 — YAML config keys

**Done:**
- `view_transform` parsing (seq of ViewTransform nodes with from_reference/to_reference)
- `looks` parsing (seq of Look nodes with name/process_space/transform/inverse_transform)
- `active_displays` / `active_views` parsing (seq of names)
- Config introspection: `toc_config_num_looks`, `toc_config_look_name`
- Config introspection: `toc_config_num_active_displays`, `toc_config_active_display_name`

### Phase 5 — look support

**Done:**
- Views can reference looks via comma-separated `looks` key
- `toc_cfg_view_looks` parses the comma-separated list
- Processor applies each look: convert to process_space → apply transform → convert back
- Color space aliases already handled by `name_matches` in `toc_config.c`
- Roles already handled by `toc_cfg_resolve_role`

### Phase 6 — file-format LUTs

**Done:**
- `.cube` 1D/3D (toc_lutfile.c)
- `.spi1d` / `.spi3d` (toc_lutfile.c)
- `.clf` (Common LUT Format, XML-based ACES standard) (toc_clf.c)
  - Supports: Matrix, Range, Exponent, Log, LUT1D, LUT3D
  - Minimal single-pass XML parser (no DOM tree)
  - Content sniffing via `<?xml` or `<ProcessList` prefix
- FileTransform resolution via `toc_file_reader` hook
- Round-trip tests for all formats

### Rules
- `toc_builtins.c` is freestanding core — never use `<math.h>` or libm symbols
- Every new FixedFunction style must have an inverse pair (`_INV = forward+1`)
- GamutComp13 is complex — AOT-C and GLSL codegens fall back to interpreter for it
- Decompose inverse ops at lowering time (not in backends) for backend-agnostic support
- File LUTs follow OpenColorIO's readers (CLF dims/bit depths/styles, CSP
  "CSPLUTV100"); check changes against the PyOCIO oracle in `ref/.pyoracle`
  (run it with `python3.12`). Unsupported CLF nodes must return UNSUPPORTED,
  never be skipped silently. 3D LUTs default to trilinear (OCIO default).
- Hostile input: every parser loop must consume input on each iteration (compare
  bytes as `unsigned char`); LUT loaders check `toc_values_fit` before
  allocating; recursion is depth-capped (YAML 128, transform walk 64)
