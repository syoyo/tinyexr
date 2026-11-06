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
| `Exr/Attribute.lean` | `PixelType`/`Compression`/`LineOrder` enums with round trips; `Channel` + `StrictlySorted`; cstring reader with bounds; `RawAttr.parse`/`parseAll` + `parse_bounds`/`parseAll_terminates`; typed decoders (box2i/box2f/compression/lineOrder/float/double/int/v2f/v3f/m33f/m44f/chromaticities/tiledesc/string/text/int32List/chlist) with size/range theorems; `Emittable` + `parse_wire` with its prefix/suffix-aware generalization `parse_emit_at`; `wireAll`/`wireAll_size`/`foldl_wireAll` and `parseAll_emit` (list-level round trip for arbitrary prefixes and suffixes); the prefix-aware `readCString_emit_at`. |
| `Exr/Tiles.lean` | level halving (`half`), `levelSize`, `numLevels`, mipmap level count, monotonicity/positivity; scan-line and tile chunk counts (`scanlineChunks`, `tilesIn`, `levelTiles`, `tiledChunks`) with cover + positivity theorems. |
| `Exr/File.lean` | `PartType`, `Header`, `validateChecks`/`validate` (required attrs, channel sampling/order, tiles, deep rules), `chunkCountConsistent`, `computedChunks_pos`; `OffsetTable` bounds/length; chunk header layout sizes for all four part kinds. |
| `Exr/Parse.lean` | `parseFile`, `parsePartHeaders`, `parseTables`, `checkParts` (name rule for multipart, per-part validation, table length, `dataStart ≤ offset < fileSize`); `parseFile_bounds`. |
| `Exr/Emit.lean` | attribute/header/offset-table/magic+version emitters (the inverse of the parser's layout). |
| `Exr/TypedEmit.lean` | typed attribute *encoders* and round-trip theorems for the schema table (`box2i` … `tiledesc`): `u32Words`/`u64Words` emitters with indexed readers, `encBox2i`/`encBox2f`/`encCompression`/`encLineOrder`/`encFloatBits`/`encDoubleBits`/`encInt`/`encV2f`/`encV3f`/`encM44f`/`encM33f`/`encChromaticities`/`encTileDesc`, plus `encLevelMode`/`encRoundingMode`; `decode*_encode` for every entry consumed by `headerOfAttrs` (and the chromaticities/matrix entries), with `m33f`/`m44f` reversed-accumulation round trips and the `tiledesc` mode/rounding round trip. |
| `Exr/Size.lean` | byte-size equations for rows, blocks and parts: `rowBytes` (List-sum and BigOperators `Finset.range` forms) with no-overflow bounds, per-chunk scan-line line counts (`chunkLines_sum`: the chunks sum to exactly the image height), scan-line payload = `height × rowBytes`, PXR24 plane-major row totals, B44 block-stream totals (`blockStreamBytes`, matches `packBlock`'s emitted length), offset-table region size (8 bytes per chunk; `Parse.parseTables_end`), u32/u64 emitter truncation boundaries. |
| `Exr/Deep.lean` | deep payload model: cumulative-count table algebra (`cumCounts`/`diffCounts` are exact inverses, the last cumulative count is the chunk total, non-negative counts give valid tables), unpacked offset-table bytes (4 per pixel), and `DeepChunk.WellFormed` (table covers the chunk's pixels, totals match, `unpackedSampleSize = total × pixelSize`). |
| `Exr/Pxr24.lean` | `float24` (round-to-nearest top-3-bytes), byte-plane group codec (`planes`/`join`, `packGroups`/`unpackGroups`), plane-major row layout (`packPlanes`, `unpackPlanesToGroups`), and the plane transposition involution (`unpackPlanesToGroups_packPlanes`, `unpackRowPlanes_packPlanes`). |
| `Exr/B44.lean` | wavy `t8`/`unt8`, shift quantization (`shiftRound`, `residuals`, `chooseShift`), `packBlock`, 14-byte decoder (`r6`, `unpack14`, `decode14Int`), flat decoder (`unpack3`), size accounting. |
| `ExrCheck.lean` | `exrcheck <file.exr>`: machine-readable structural verdict used by the differ. |
| `ExrGen.lean` | `exrgen <out> <seed> <kind>`: valid, loadable fixtures (scanline/tiled/mipmap/ripmap/deepscanline/multipart) + `native_decide` self-checks that they parse and validate. |
| `Exr/Deep.lean` | deep payload model: cumulative-count tables (`cumCounts`/`diffCounts` inverses, last cum = chunk total, non-negative counts give valid tables), unpacked offset-table bytes (4 per pixel), `DeepChunk.WellFormed`. |
| `Exr/Rle.lean` | RLE pipeline: even/odd interleave and delta predictor (both proven inverses), run-length expand/encode (greedy, bit-exact with the C `rle_encode`), raw fallback (`rleCompress` size cap) and full decode (`rleDecodeFull`), with round-trip theorems. |
| `Exr/Zip.lean` | ZIP container layer: ADLER32 checksum (pure fold, with the block-boundary deferred-mod equivalence), zlib header validation (CM/CINFO/FDICT/check digits), the big-endian trailer, block validation, 16-line ZIP geometry. |
| `CodecGen.lean` | `codecgen <out.bin> <seed>`: PXR24 (uint/half/float), B44/B44A and RLE vectors for `test/v3/codec_diff.c`. |

## Conformance matrix

| Spec / library rule | Model | Key lemmas | Checked by |
| --- | --- | --- | --- |
| magic + version flags (5 combos) | `Exr/Version.lean` | `ofBits_toBits`, `toBits_injective` | `lean-diff` (every corpus file) |
| attribute wire format (name/type/size/value) | `Exr/Attribute.lean` | `parse_wire`, `parse_emit_at`, `parseAll_emit`, `parseAll_terminates`, `readCString_emit_at` | `lean-diff` |
| emitters produce the exact wire layout (attr/header bytes) | `Exr/Emit.lean` | `attrBytes_eq_wire`, `headerBytes_eq_wireAll` | — |
| typed attribute round trips (schema table `box2i … tiledesc`) | `Exr/TypedEmit.lean` | `decodeBox2i_encode`, `decodeBox2f_encode`, `decodeCompression_encode`, `decodeLineOrder_encode`, `decodeFloatBits_encode`, `decodeDoubleBits_encode`, `decodeInt_encode`, `decodeV2f_encode`, `decodeV3f_encode`, `decodeM33f_encode`, `decodeM44f_encode`, `decodeChromaticities_encode`, `decodeTileDesc_encode` | — |
| cstring name/type round trip (`readCString` of `s ++ NUL`) | `Exr/Attribute.lean` | `readCString_emit` | — |
| chlist (pixel type, pLinear, reserved, sampling, strict order) | `Exr/Attribute.lean` | `decodeChlist_bounds` | `lean-diff` (channel counts) |
| required attributes per part type | `Exr/File.lean` | `wellFormed_*` | `lean-diff` accept/reject |
| chunkCount == computed | `Exr/File.lean` | `wellFormed_chunkCount_consistent`, `computedChunks_pos` | `lean-diff` (chunk counts) |
| scan-line blocks = ceil(height / linesPerBlock) | `Exr/Tiles.lean` | `scanlineChunks_pos`, `scanlineChunks_covers` | `lean-diff` |
| tiled levels (ONE/MIP/RIP, ROUND_DOWN/UP) | `Exr/Tiles.lean` | `levelSize_antitone`, `tiledChunks_pos` | `lean-diff` (tiled fixtures) |
| offset table: one entry/chunk, `dataStart ≤ off < fileSize` | `Exr/Parse.lean` | `parseTables_bounds`, `parseFile_bounds` | `lean-diff` (issue-238 fixtures) |
| tile offset index inside `[0, chunkCount)` and injective (all modes) | `Exr/Tiles.lean` | `tileIndex_{oneLevel,mipmap,ripmap}_lt`, `tileIndex_{oneLevel,mipmap,ripmap}_injective` | `lean-diff` (tile counts) |
| multi-part shared attributes (OpenEXR-strict mode) | `Exr/File.lean`, `Exr/Parse.lean` | `sharesAttrs_spec`, `checkPartsOpenEXR_implies_checkParts` | `exrcheck --strict` on the generated multipart fixture |
| PXR24: 4/2/3 byte planes, delta rows, plane-major order | `Exr/Pxr24.lean` | `uint_roundtrip`, `half_roundtrip`, `float_roundtrip`, `float_decode_eq`, `packPlanes_length` | `codec-diff` (bit-exact) |
| PXR24 plane transposition is an involution (pack→unpack = identity) | `Exr/Pxr24.lean` | `unpackPlanesToGroups_flatMap`, `unpackPlanesToGroups_packPlanes`, `unpackRowPlanes_packPlanes` | `codec-diff` (bit-exact) |
| full-file round trip: emitter + parser are inverse on well-formed files | `Exr/Emit.lean` | `parseFile_emit` (single- and multi-part, tiled/deep flags flow through) | `lean-diff` (generated fixtures) |
| PXR24 `float24`: RN truncation, Inf→Inf, NaN stays NaN, finite≠Inf | `Exr/Pxr24.lean` | `float24_lt`, `float24_inf`, `float24_nan_nonzero`, `float24_finite_not_inf` | `codec-diff` |
| PXR24 decode/encode stability | `Exr/Pxr24.lean` | `float24_shift_stable`, `float24_stable` | `codec-diff` |
| B44 t-transform is a bijection on non-NaN halves | `Exr/B44.lean` | `unt8_t8` (exhaustive over 65536 patterns), `t8_nan` | `codec-diff` (all blocks) |
| B44 shift search terminates and never needs its 16 fallback | `Exr/B44.lean` | `chooseShift_le`, `chooseShift_le_12`, `chooseShift_fits` | `codec-diff` |
| B44 reconstruction error (bounded by 2^11+1) at shift 12 | `Exr/B44.lean` | `shiftRound_12_abs_error`, `dvals_12_within` | — |
| B44 14-byte blocks stay below the `s[2] >= 52` flat marker | `Exr/B44.lean` | `packBlock_third_lt_52`, `packBlock_flat_byte2` | `codec-diff` |
| B44A flat form iff every residual equals the bias | `Exr/B44.lean` | `packBlock_flat_iff` | `codec-diff` |
| B44 14-byte block decodes exactly to the quantized values | `Exr/B44.lean` | `decode14_telescopes` (16 explicit path proofs over ℤ) | `codec-diff` (pack + unpack) |
| B44A flat block → constant, 3 vs 14 byte accounting | `Exr/B44.lean` | `decode3_constant`, `packBlock_length`, `blockBytes_mem` | `codec-diff` (constant/NaN/Inf/±0 blocks) |
| uncompressed row bytes = Σ over channels (× width) | `Exr/Size.lean` | `rowBytes_eq_finset_sum`, `rowBytes_eq_width_mul_pixelSize`, `rowBytes_le`, `rowBytes_lt_2pow64` | — |
| scan-line payload = `height × rowBytes`; per-chunk lines sum to the image height | `Exr/Size.lean` | `chunkLines_sum`, `scanlinePayloadBytes_eq`, `scanlinePayloadBytes_lt_2pow64` | — |
| B44 block stream totals (3/14 B per block); `packBlock` emits exactly `blockBytes` | `Exr/Size.lean` | `packBlock_length_eq_blockBytes`, `blockStreamBytes_eq_finset_sum`, `blockStreamBytes_le`, `blockStreamBytes_ge` | `codec-diff` |
| PXR24 plane-major row = Σ over planes (BigOperators form) | `Exr/Size.lean` | `packPlanes_length_eq_finset_sum` | `codec-diff` |
| offset-table region = 8 B × total chunks (parser and emitter sides) | `Exr/Size.lean`, `Exr/Parse.lean` | `parseTables_length`, `parseOffsetTable_length`, `parseTables_end`, `tablesBytes_of_parseTables`, `offsetTableBytes_size` | `lean-diff` |
| u32/u64 emitters do not truncate below 2^32/2^64; `ofNat` truncates above | `Exr/Size.lean` | `u64Bytes_faithful`, `u32Bytes_faithful`, `u64Bytes_ofNat_mod`, `u32Bytes_ofNat_mod` | — |
| RLE byte-run codec (interleave + predictor + runs) | `Exr/Rle.lean` | `interleaveDecode_encode`, `interleaveEncode_decode`, `predictorDecode_encode`, `predictorEncode_decode`, `rleExpand_rleEncode`, `rleEncode_length_le`, `rleCompress_length_le`, `rleRoundTrip` | `codec-diff` (bit-exact both directions) |
| ZIP container: ADLER32 (per-step = deferred modulo), zlib header checks, big-endian trailer, wrapper validation | `Exr/Zip.lean` | `adler32Acc_mod`, `adler32Go_lt`, `adler32_empty`, `zlibHeaderValid_78_01`, `zlibHeaderValid_78_9c`, `adler32Trailer_length`, `validateZlibBlock_of_valid`, `zipLinesPerBlock`, `zipsLinesPerBlock` | `codec-diff` (bit-exact checksum) |
| deep cumulative-count tables are exact inverses; last cum = chunk total; non-negative counts give valid tables | `Exr/Deep.lean` | `diffCounts_cumCounts`, `cumCounts_diffCounts`, `cumCounts_last`, `cumCounts_valid`, `DeepChunk.WellFormed`, `WellFormed.offsetTableSize`, `WellFormed.sampleSize` | `lean-diff` (deep fixtures) |

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
  B44A, RLE), and
* tinyexr v3's B44/B44A/RLE encoders reproduce the Lean packed bytes exactly,
  and the C `exr_adler32` matches the Lean `adler32` bit-exactly (the deferred
  modulo is proven value-equivalent to the per-step fold).

Records per seed: 120 PXR24 rows (uint/half/float, lengths 1–40), 120 random B44
blocks (60 B44 + 60 B44A) and 28 edge blocks (constant ±0/±1/max/subnormal/Inf/NaN,
near-constant, monotone ramps), 60 random RLE byte streams and 13 RLE edge
patterns (3/127/128/129-run caps, split literals, incompressible), 12 random
ADLER32 streams and 5 long ones (5552/5553/1105/6000/11107 bytes, crossing the
C deferred-modulo boundary) —
**358 records per seed**, run for seeds `12345 1 7 42 999 20240101 65535`
(7 × 358 = 2506 records), all bit-exact.

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
* **DEFLATE payload bitstream is not modelled.** The ZIP model covers the
  zlib wrapper (header + ADLER32 trailer), the 16-line scan-line block
  geometry and block validation; Huffman coding (the in-tree `exr_deflate`
  bit writer) is unmodelled by design (any valid DEFLATE stream satisfies
  the wrapper rules).
* **RLE size-based dispatch.** tinyexr's reader treats a compressed payload
  whose length equals the uncompressed size as stored-verbatim (a memcpy
  fast path in `exr_decompress_block`); `rleDecodeFull` mirrors that exact
  behaviour. A foreign RLE stream whose encoded length coincides with the
  decoded size would decode as verbatim (OpenEXR always run-decodes); only
  the greedy `rleEncode` (bit-exact) is claimed codec-exact, and the C
  `rlen >= n` fallback means tinyexr itself never emits such a stream.
* **PXR24 plane-major row layout is proven.** The per-sample byte-plane algebra
  (`planes`/`join`, delta round trips, `float24`) and the plane-major
  transposition involution are both proven (`unpackPlanesToGroups_packPlanes`,
  `unpackRowPlanes_packPlanes`); the emitted row layout is additionally pinned
  byte-exactly against the C implementation by `codec-diff`.
* **B44 perceptual tables (`p_linear` channels) are not re-modelled.** The
  t-transform, quantization, block packing and reconstruction are proven and
  bit-exact; the two 65536-entry `exp`/`log` double tables are validated by the
  C-side table test against libm (≤1 ulp), which is the agreed fallback bar.
* **Extraction is a subprocess oracle, not a linked static library.** The Lean
  executables (`exrcheck`, `exrgen`, `codecgen`) drive the C harnesses. Linking a
  Lean runtime into the ASan test binaries was judged brittle; this is the
  documented M5 fallback.
* **`parse (emit f) = some f` is proven for arbitrary well-formed files**
  (`Emit.parseFile_emit`: magic+version, part headers via
  `parsePartHeaders_emit_multipart` / `parsePartHeaders_emit_single_list`,
  offset tables via `parseOffsetTable_emit` / `parseTables_emit`), built on
  `RawAttr.parse_wire` / `RawAttr.parse_emit_at` (any prefix and suffix) and
  `RawAttr.parseAll_emit` plus the typed inverses in `Exr/TypedEmit.lean`
  (`headerOfAttrs_of_ok`); the concrete generated files are machine-checked
  by `generate_*_parses` / `generate_*_valid`.
* **Spec vs library leniency.** The model follows OpenEXR's library where the
  spec text is stricter: a missing `maxSamplesPerPixel` on deep parts is accepted
  (OpenEXR reads such files), and multipart shared-attribute equality is not
  enforced (tinyexr does not enforce it either). `exrgen` still emits files that
  OpenEXR accepts.

## Axiom profile

**First-party `sorry` / `admit` count: 0** (grep-verified over `lean/*.lean`
and `lean/Exr/*.lean`).

By site count (grep-verified):

| Tactic site | Count | Where | Axiom contributed |
| --- | --- | --- | --- |
| `bv_decide` | 29 | `Exr/Bytes.lean` (3, LE write/read round trips), `Exr/Pxr24.lean` (22, float24 mask/shift/NaN/Inf arithmetic, `join_planes`/`maskOf` bounds), `Exr/B44.lean` (4, t-code sign cases in `unt8_t8`) | one `*._native.bv_decide.ax_*` per site (LRAT certificate checked by the tactic) |
| `native_decide` | 10 | `ExrGen.lean` (6 `generate_*_parses`, 3 `generate_*_valid`, 1 `generate_multipart_valid_openexr`) | one `*._native.native_decide.ax_*` per site (native evaluation, not kernel reduction) |

`bv_decide` goals stay small (≤ 32-bit arithmetic), so the LRAT certificates
are small and the tactic discharges them directly; `unt8_t8` is a sign-case
analysis with `bv_decide` leaves rather than a 65536-way `native_decide`.
The `ExrGen` self-checks evaluate multi-KB generated fixtures through the
byte-level parser; kernel `decide` was measured infeasible on the smallest
fixture (`generate "tiled"`, 2012 bytes) — it exceeds 4m40s at
`maxHeartbeats 100000000` / `maxRecDepth 100000` locally — so the ten checks
keep `native_decide` and are pinned byte-exactly by the harness instead.

Full census over all 443 first-party library theorems in `lean/Exr/*.lean`
(`#print axioms`, scripted): **380 depend only on
`propext`/`Classical.choice`/`Quot.sound`, 63 additionally carry
`bv_decide` LRAT certificate axioms, 0 `sorryAx`, 0 `native_decide`**.
The 10 executable self-checks in `ExrGen.lean` carry one
`*._native.native_decide.ax_*` each (native evaluation, not kernel reduction —
kernel `decide` was measured infeasible). The residual axiom surface is
therefore: `propext`, `Classical.choice`, `Quot.sound`, 63 site-generated
`bv_decide` certificate axioms, plus the 10 documented `native_decide` self-checks. The
differential harnesses (`lean-diff`, `codec-diff`) are the independent check
on what the certificates assert.
There is also no remaining tile-index injectivity gap: ONE_LEVEL, MIPMAP and
RIPMAP indices are all proven injective (`tileIndex_*_injective`).

## Fixtures added

* `test/unit/regression/decreasing-y-scanline.exr` — DECREASING_Y writer regression.
* `test/unit/regression/leangen-{scanline,tiled,mipmap,ripmap,deepscanline,multipart}.exr`
  — `exrgen` output, replayed by `make fuzz-corpus` under ASan+UBSan+LSan and by
  `make lean-diff`.
