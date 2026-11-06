# `lean/` — Lean 4 model of the OpenEXR container + PXR24/B44 codecs

This package is the **verified oracle** used to validate (and, where it disagreed,
fix) the TinyEXR v3 C implementation in `include/exr.h` + `src/*.c`. It is not a
proof *about* the C code: the Lean model is proven, and the C code is checked
against it by two differential harnesses.

* Lean `v4.35.0`, mathlib pinned at `v4.35.0` (`lake-manifest.json`).
* Every new file carries the BSD-3-Clause header.
* No `sorry` in any theorem. Axioms used are listed below.

## Build / validate

```sh
make lean-check     # lake exe cache get && lake build (+ exrcheck/exrgen/codecgen)
make lean-diff      # Lean structural oracle vs tinyexr v3 vs OpenEXR corpus
make codec-diff     # Lean codec vectors vs tinyexr v3 PXR24/B44 codecs
```

`make lean-diff` and `make codec-diff` are the validation gates for the model;
`make c11-gate`, `make test-c`, `make fuzz-corpus` are the unchanged C gates.

## Modules

| Module | Contents |
| --- | --- |
| `Exr/Bytes.lean` | Total little-endian readers (`getU8?`, `getU16LE`, `getU32LE`, `getU64LE`, `getI32LE`, …) and writers over `ByteArray`; difference-list `Emit`; append/extract lemmas (`getU8?_append_left/right`, `getU32LE_append_right`, …); `get*(put* x) = some x` round trips. |
| `Exr/Version.lean` | magic `0x01312F76`; version field with the five legal flag combinations (tiled / long names / non-image / multipart); `ofBits`/`toBits` round trip and injectivity. |
| `Exr/Attribute.lean` | `PixelType`/`Compression`/`LineOrder` enums with round trips; `Channel` + `StrictlySorted`; cstring reader with bounds; `RawAttr.parse`/`parseAll` + `parse_bounds`/`parseAll_terminates`; typed decoders (box2i/box2f/compression/lineOrder/float/double/int/v2f/v3f/m33f/m44f/chromaticities/tiledesc/string/text/int32List/chlist) with size/range theorems; `Emittable` + `parse_wire` (parse ∘ emit = id for a single attribute) and the prefix-aware `readCString_emit_at`. |
| `Exr/Tiles.lean` | level halving (`half`), `levelSize`, `numLevels`, mipmap level count, monotonicity/positivity; scan-line and tile chunk counts (`scanlineChunks`, `tilesIn`, `levelTiles`, `tiledChunks`) with cover + positivity theorems. |
| `Exr/File.lean` | `PartType`, `Header`, `validateChecks`/`validate` (required attrs, channel sampling/order, tiles, deep rules), `chunkCountConsistent`, `computedChunks_pos`; `OffsetTable` bounds/length; chunk header layout sizes for all four part kinds. |
| `Exr/Parse.lean` | `parseFile`, `parsePartHeaders`, `parseTables`, `checkParts` (name rule for multipart, per-part validation, table length, `dataStart ≤ offset < fileSize`); `parseFile_bounds`. |
| `Exr/Emit.lean` | attribute/header/offset-table/magic+version emitters (the inverse of the parser's layout). |
| `Exr/Pxr24.lean` | `float24` (round-to-nearest top-3-bytes), byte-plane group codec (`planes`/`join`, `packGroups`/`unpackGroups`), plane-major row layout (`packPlanes`, `unpackPlanesToGroups`). |
| `Exr/B44.lean` | wavy `t8`/`unt8`, shift quantization (`shiftRound`, `residuals`, `chooseShift`), `packBlock`, 14-byte decoder (`r6`, `unpack14`, `decode14Int`), flat decoder (`unpack3`), size accounting. |
| `ExrCheck.lean` | `exrcheck <file.exr>`: machine-readable structural verdict used by the differ. |
| `ExrGen.lean` | `exrgen <out> <seed> <kind>`: valid, loadable fixtures (scanline/tiled/mipmap/ripmap/deepscanline/multipart) + `native_decide` self-checks that they parse and validate. |
| `CodecGen.lean` | `codecgen <out.bin> <seed>`: PXR24 (uint/half/float) and B44/B44A vectors for `test/v3/codec_diff.c`. |

## Conformance matrix

| Spec / library rule | Model | Key lemmas | Checked by |
| --- | --- | --- | --- |
| magic + version flags (5 combos) | `Exr/Version.lean` | `ofBits_toBits`, `toBits_injective` | `lean-diff` (every corpus file) |
| attribute wire format (name/type/size/value) | `Exr/Attribute.lean` | `parse_wire`, `parseAll_terminates`, `readCString_emit_at` | `lean-diff` |
| chlist (pixel type, pLinear, reserved, sampling, strict order) | `Exr/Attribute.lean` | `decodeChlist_bounds` | `lean-diff` (channel counts) |
| required attributes per part type | `Exr/File.lean` | `wellFormed_*` | `lean-diff` accept/reject |
| chunkCount == computed | `Exr/File.lean` | `wellFormed_chunkCount_consistent`, `computedChunks_pos` | `lean-diff` (chunk counts) |
| scan-line blocks = ceil(height / linesPerBlock) | `Exr/Tiles.lean` | `scanlineChunks_pos`, `scanlineChunks_covers` | `lean-diff` |
| tiled levels (ONE/MIP/RIP, ROUND_DOWN/UP) | `Exr/Tiles.lean` | `levelSize_antitone`, `tiledChunks_pos` | `lean-diff` (tiled fixtures) |
| offset table: one entry/chunk, `dataStart ≤ off < fileSize` | `Exr/Parse.lean` | `parseTables_bounds`, `parseFile_bounds` | `lean-diff` (issue-238 fixtures) |
| PXR24: 4/2/3 byte planes, delta rows, plane-major order | `Exr/Pxr24.lean` | `uint_roundtrip`, `half_roundtrip`, `float_roundtrip`, `float_decode_eq`, `packPlanes_length` | `codec-diff` (bit-exact) |
| PXR24 `float24`: RN truncation, Inf→Inf, NaN stays NaN, finite≠Inf | `Exr/Pxr24.lean` | `float24_lt`, `float24_inf`, `float24_nan_nonzero`, `float24_finite_not_inf` | `codec-diff` |
| B44 t-transform is a bijection on non-NaN halves | `Exr/B44.lean` | `unt8_t8` (exhaustive over 65536 patterns), `t8_nan` | `codec-diff` (all blocks) |
| B44 shift search terminates (shift ≤ 16) | `Exr/B44.lean` | `chooseShift_le` | `codec-diff` |
| B44 14-byte block decodes exactly to the quantized values | `Exr/B44.lean` | `decode14_telescopes` (16 explicit path proofs over ℤ) | `codec-diff` (pack + unpack) |
| B44A flat block → constant, 3 vs 14 byte accounting | `Exr/B44.lean` | `decode3_constant`, `packBlock_length`, `blockBytes_mem` | `codec-diff` (constant/NaN/Inf/±0 blocks) |

## Differential harnesses

**Structural** (`test/v3/lean_diff.py`, `make lean-diff`) runs `exrcheck` and the
tinyexr `test/v3/parse_harness` over: `test/unit/regression/*` (including the
Lean-generated fixtures), `~/work/openexr-images` and `build/lean-gen/*`, and
compares accept/reject, part type, tiled/deep flags, computed chunk count,
offset-table length, data window and channel count.

Result: **122 files, 0 disagreements**.

**Codec** (`test/v3/codec_diff.c`, `make codec-diff`) reads TEXV vectors from
`codecgen` and checks, per record, that

* tinyexr v3's decoder reproduces the Lean decode bytes exactly (PXR24, B44,
  B44A), and
* tinyexr v3's B44/B44A encoder reproduces the Lean packed bytes exactly.

Records per seed: 120 PXR24 rows (uint/half/float, lengths 1–40), 120 random B44
blocks (60 B44 + 60 B44A) and 28 edge blocks (constant ±0/±1/max/subnormal/Inf/NaN,
near-constant, monotone ramps) — **268 records per seed**, run for seeds
`12345 1 7 42 999 20240101 65535` (7 × 268 = 1876 records), all bit-exact.

### Bugs the harnesses found

| Harness | Finding | Resolution |
| --- | --- | --- |
| structural | `issue-238` fixtures have offset-table entries past EOF; the model accepted them | model gained the `dataStart ≤ off < fileSize` check (matches tinyexr) |
| structural | OpenEXR requires shared attributes (`displayWindow`, …) to agree across multipart parts; `exrgen` used different display windows | `exrgen` multipart now shares the display window (generator fix, not a C change) |
| codec (PXR24) | the C row layout is **plane-major**, not per-sample groups | model transposed (`packPlanes`/`unpackPlanesToGroups`); group algebra kept proven |
| codec (PXR24) | HALF/FLOAT reconstruction must truncate to `8*bytes` bits | `unpackGroupsAux` masks with `maskOf` |
| codec (B44) | residuals are **signed** during the shift search (`Nat` truncation accepts too-small shifts) | `residuals : List Int` + `0 ≤ r ≤ 0x3f` |
| codec (B44) | the decoder's middle columns chain from `v4`/`v8`, not `s0` | corrected `decode14Int`/`unpack14` (telescoping proof re-stated) |
| codec (B44A) | `unpack3` already sign-decodes; `decodeBlock` applied `unt8` twice | `unpack3` returns t-values |
| OpenEXR CLI cross-check | tinyexr v3 wrote **DECREASING_Y** scan-line chunks in increasing-y order, which OpenEXR rejects (`Invalid chunk index`) | **C fix** in `src/exr_writer.c` (`wr_scanline_block_index`, serial + parallel + deep paths); regression fixture `test/unit/regression/decreasing-y-scanline.exr` and a unit test that re-applies OpenEXRCore's rule |

The writer fix is the only behaviour change to the C implementation. Codec wire
formats are untouched (the PXR24/B44 fixes were model-side).

## Documented boundaries (honest gaps)

* **DWAA / DWAB are not modelled** and stay `EXR_ERROR_UNSUPPORTED` in the C
  codec dispatch (per `AGENTS.md`). HTJ2K internals are untouched.
* **PXR24 plane-major row layout is validated, not proven.** The proven part is
  the per-sample byte-plane algebra (`planes`/`join`, delta round trips,
  `float24`); the plane-major stream (`packPlanes`) is executable and pinned
  byte-exactly by `codec-diff`. A full transpose-involution proof was attempted
  and set aside as disproportionately costly for the value.
* **B44 perceptual tables (`p_linear` channels) are not re-modelled.** The
  t-transform, quantization, block packing and reconstruction are proven and
  bit-exact; the two 65536-entry `exp`/`log` double tables are validated by the
  C-side table test against libm (≤1 ulp), which is the agreed fallback bar.
* **Extraction is a subprocess oracle, not a linked static library.** The Lean
  executables (`exrcheck`, `exrgen`, `codecgen`) drive the C harnesses. Linking a
  Lean runtime into the ASan test binaries was judged brittle; this is the
  documented M5 fallback.
* **`parse (emit f) = some f` is proven at the attribute level and for the
  concrete generated files, not for arbitrary well-formed headers.** The
  symbolic round trip is `RawAttr.parse_wire` (+ `readCString_emit_at`) for any
  `Emittable` attribute; full-file round trips are `generate_*_parses` /
  `generate_*_valid` for all six `exrgen` kinds (machine-checked with
  `native_decide`). A general theorem over arbitrary header/attribute lists
  (which would also need `headerOfAttrs` to be a proven inverse) is not proven;
  the differential harnesses cover the corpus side.
* **Spec vs library leniency.** The model follows OpenEXR's library where the
  spec text is stricter: a missing `maxSamplesPerPixel` on deep parts is accepted
  (OpenEXR reads such files), and multipart shared-attribute equality is not
  enforced (tinyexr does not enforce it either). `exrgen` still emits files that
  OpenEXR accepts.

## Axiom profile

Small-step proofs use only `propext`, `Classical.choice`, `Quot.sound`.
Bit-vector goals go through `bv_decide`, which adds one LRAT axiom per goal
(`*_native.bv_decide.ax_*`). Exhaustive checks over the 65536-pattern half domain
(`unt8_t8`, `t8_nan`-adjacent enumeration) and the generator self-checks use
`native_decide` (`*_native.native_decide.ax_*`). No `sorryAx` anywhere.

## Fixtures added

* `test/unit/regression/decreasing-y-scanline.exr` — DECREASING_Y writer regression.
* `test/unit/regression/leangen-{scanline,tiled,mipmap,ripmap,deepscanline,multipart}.exr`
  — `exrgen` output, replayed by `make fuzz-corpus` under ASan+UBSan+LSan and by
  `make lean-diff`.
