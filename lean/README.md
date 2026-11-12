# `lean/` — Lean 4 formalization of OpenEXR and its codecs

This package is the **verified oracle** used to validate (and, where it disagreed,
fix) the TinyEXR v3 C implementation in `include/exr.h` + `src/*.c`. It is not a
proof *about* the C code: the Lean model is proven, and the C code is checked
against it by two differential harnesses.

The current proof coverage, theorem boundaries, reproducible gates and latest
validation results are recorded in [Formalization and verification status](VERIFICATION.md).

* Lean `v4.35.0`, mathlib pinned at `v4.35.0` (`lake-manifest.json`).
* Every new file carries the BSD-3-Clause header.
* No `sorry` in any theorem. Axioms used are listed below.

## Build / validate

```sh
make lean-check     # lake exe cache get && lake build (+ exrcheck/exrgen/codecgen)
make lean-diff      # Lean structural oracle vs tinyexr v3 vs OpenEXR corpus
make codec-diff     # Lean codec vectors vs tinyexr v3 codecs
make lean-validation-test # gate failure, metadata, seeded and strict-mode regressions
make lean-axiom-check # transitive first-party theorem axiom audit
make lean-validation-sanitize # sanitized codec vectors and malformed-vector regressions
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
| `Exr/Chunk.lean` | Bounded reads for all four chunk-header layouts, packed payload extents (`parse_bounds`), part IDs and coordinate/index correspondence; used by `exrcheck --chunks`. |
| `Exr/Parse.lean` | `parseFile`, `parsePartHeaders`, `parseTables`, `checkParts` (name rule for multipart, per-part validation, table length, `dataStart ≤ offset < fileSize`); `parseFile_bounds`. |
| `Exr/Emit.lean` | attribute/header/offset-table/magic+version emitters (the inverse of the parser's layout). |
| `Exr/TypedEmit.lean` | typed attribute *encoders* and round-trip theorems for the schema table (`box2i` … `tiledesc`): `u32Words`/`u64Words` emitters with indexed readers, `encBox2i`/`encBox2f`/`encCompression`/`encLineOrder`/`encFloatBits`/`encDoubleBits`/`encInt`/`encV2f`/`encV3f`/`encM44f`/`encM33f`/`encChromaticities`/`encTileDesc`, plus `encLevelMode`/`encRoundingMode`; `decode*_encode` for every entry consumed by `headerOfAttrs` (and the chromaticities/matrix entries), with `m33f`/`m44f` reversed-accumulation round trips and the `tiledesc` mode/rounding round trip. |
| `Exr/Size.lean` | byte-size equations for rows, blocks and parts: `rowBytes` (List-sum and BigOperators `Finset.range` forms) with no-overflow bounds, per-chunk scan-line line counts (`chunkLines_sum`: the chunks sum to exactly the image height), scan-line payload = `height × rowBytes`, PXR24 plane-major row totals, B44 block-stream totals (`blockStreamBytes`, matches `packBlock`'s emitted length), offset-table region size (8 bytes per chunk; `Parse.parseTables_end`), u32/u64 emitter truncation boundaries. |
| `Exr/Deep.lean` | deep payload model: cumulative-count table algebra (`cumCounts`/`diffCounts` are exact inverses, the last cumulative count is the chunk total, non-negative counts give valid tables), unpacked offset-table bytes (4 per pixel), and `DeepChunk.WellFormed` (table covers the chunk's pixels, totals match, `unpackedSampleSize = total × pixelSize`). |
| `Exr/Pxr24.lean` | `float24` (round-to-nearest top-3-bytes), byte-plane group codec (`planes`/`join`, `packGroups`/`unpackGroups`), plane-major row layout (`packPlanes`, `unpackPlanesToGroups`), and the plane transposition involution (`unpackPlanesToGroups_packPlanes`, `unpackRowPlanes_packPlanes`), and mixed/sampled channel-row stream composition (`unpackRows_packRows`). |
| `Exr/B44.lean` | wavy `t8`/`unt8`, shift quantization (`shiftRound`, `residuals`, `chooseShift`), `packBlock`, 14-byte decoder (`r6`, `unpack14`, `decode14Int`), flat decoder (`unpack3`), size accounting. |
| `ExrCheck.lean` | `exrcheck <file.exr>`: machine-readable structural verdict used by the differ. |
| `ExrGen.lean` | `exrgen <out> <seed> <kind>`: valid, loadable fixtures (scanline/tiled/mipmap/ripmap/deepscanline/multipart) + `native_decide` self-checks that they parse and validate. |
| `Exr/Deep.lean` | deep payload model: cumulative-count tables (`cumCounts`/`diffCounts` inverses, last cum = chunk total, non-negative counts give valid tables), unpacked offset-table bytes (4 per pixel), `DeepChunk.WellFormed`. |
| `Exr/Rle.lean` | RLE pipeline: even/odd interleave and delta predictor (both proven inverses), run-length expand/encode (greedy, bit-exact with the C `rle_encode`), raw fallback (`rleCompress` size cap) and full decode (`rleDecodeFull`), with round-trip theorems. |
| `Exr/PizCodebook.lean` | Checked canonical-code trie construction, duplicate/prefix rejection, insertion/path preservation, decoder path derivation from the actual table, and strict symbol-read progress. |
| `Exr/PizEntropy.lean` | Canonical symbol/RLE parser, exact output/alphabet bounds, arbitrary event-stream inversion, and the complete greedy entropy-bit writer/parser inverse under checked codebook construction. |
| `Exr/PizLayout.lean` | Sampled planar/canonical channel ordering, negative-origin sampling, allocation and per-lane wavelet access bounds; address permutation and both executable reorder inverses. |
| `Exr/PizBlock.lean` | Outer bitmap/Huffman framing, composed wavelet/LUT/reorder decoder, exact output size and intermediate access bounds. |
| `Exr/PizPacketEmit.lean` | Actual packet emitter/parser inverse, sliced tables, header fields, table padding/alignment and entropy bit budgets; checked canonical construction remains an explicit precondition. |
| `Exr/PizPacket.lean` | Composed 20-byte Huffman header, length-table and entropy parser; actual byte alignment, bit budgets, output lengths/alphabet bounds; zero-output semantics and documented ignored fields. |
| `Exr/PizBits.lean` | Bounded MSB-first field reads, arbitrary-width field/value inverses, byte-packing inverse including terminal padding, and read/length bounds. |
| `Exr/PizTable.lean` | Huffman literal/short/long-zero-run table parser; token and greedy-emitter byte inverses with arbitrary suffixes; exact decoded length, length ≤58 and input-consumption bounds. |
| `Exr/PizLengthTable.lean` | Exact emitted depths and absent slots, positive active codes, accepted-table Kraft mass and precise heap support including the run marker. |
| `Exr/PizFrequencySource.lean` | Entropy source/marker validity, omitted zero-prefix restoration and sliced-table size derived from accepted frequency lengths. |
| `Exr/PizHistogram.lean` | Shared executable histogram, active-source preservation, maximum/minimum bounds and generated sliced-source validity. |
| `Exr/PizWireBounds.lean` | Greedy table/payload length bounds; C source-size limit implies signed payload bits and 32-bit packet bytes. |
| `Exr/PizGeneratedRoundtrip.lean` | Complete encoder factory and decoder inverse, deriving histogram/source/slicing/wire conditions and checked canonical acceptance. |
| `Exr/PizCanonicalMass.lean` | Exact dyadic mass invariant for the actual descending canonical recurrence. |
| `Exr/PizCanonicalWords.lean` | Actual canonical words are representable and prefix free; every accepted frequency table builds successfully. |
| `Exr/PizCodebookTotal.lean` | Checked trie construction succeeds for representable prefix-free entries. |
| `Exr/PizKraft.lean` | Exact integer Kraft mass for full frequency trees, including every tree accepted by the actual 58-bit length emitter. |
| `Exr/PizHeap.lean` | Frequency-ordered array heap (Batteries, reversed weight comparison); minimum extraction, invariant-preserving merges, size-decreasing termination, total frequency/symbol conservation, unique and bounded output symbols, depth/58-bit output bounds; frequency-derived lengths checked against C including ties and RLE-marker placement. |
| `Exr/PizDisjoint.lean` | Separation and disjoint points/addresses for generated row-major levels, including both odd edges. |
| `Exr/PizComposition.lean` | Disjoint channel/lane task construction, cross-layout traversal commutation and complete planar `waveletGo` inverse in both modes. |
| `Exr/PizReconstruct.lean` | Shared coefficient preparation and inverse of scatter/rank/all wavelet tasks/restore/gather, with bitmap coverage as a source precondition. |
| `Exr/PizBitmap.lean` | Actual byte-OR bitmap builder, fixed allocation and complete source-alphabet coverage, deriving numerical reconstruction's bitmap hypothesis. |
| `Exr/PizBitmapSpan.lean` | Canonical min/max bitmap extent, empty sentinel, omitted-zero bounds and exact zero-padding restoration. |
| `Exr/PizFrameEmit.lean` | Trimmed outer bitmap/Huffman framing emitter/parser inverse, including both LE header sizes and exact payload extent. |
| `Exr/PizRoundtrip.lean` | Full block emitter/parser composition and raw fallback, with checked canonical/source/table representability as explicit preconditions. |
| `Exr/PizDecodePacket.lean` | Actual Huffman packet parser composed with complete numerical reconstruction, under the checked table and source conditions. |
| `Exr/PizSmallRange.lean` | Low-pass lattice range preservation through all encoder prefixes and complete executable 14-bit/mode-selected traversal inverses, derived from source bounds. |
| `Exr/PizWaveletInverse.lean` | Disjoint array instruction commutation, same-order level inverses, complete executable 16-bit traversal inverse, local 14-bit level inverse and low-pass range bounds. |
| `Exr/PizWavelet.lean` | Executable array cell/edge inverses for 14/16-bit lifting, address injectivity/distinctness, reverse-instruction full-range composition, and preservation outside channel storage. |
| `Exr/PizTraversal.lean` | Complete multilevel cell/odd-edge traversal, power-of-two edge-test equivalence, per-point and lane-strided allocation bounds, intermediate-array size preservation and signed stride-product bounds under an explicit allocation limit; executable scalar array traversal checked against C. |
| `Exr/Piz.lean` | Range bitmap/alphabet and rank inverse with 16-bit bounds; signed 14-bit and modular 16-bit wavelet pairs and 2×2 cells; inverse composition for arbitrary distinct-position lifting schedules; descending canonical Huffman assignment, length-table zero-run serialization and payload symbol/RLE bits; prefix-tree symbol-stream inversion under explicit path hypotheses. |
| `Exr/Zip.lean` | ZIP predictor/interleave composition with inverse, validated reconstruction after external inflate, bad header/checksum rejection; container layer: ADLER32 checksum (pure fold, with the block-boundary deferred-mod equivalence), zlib header validation (CM/CINFO/FDICT/check digits), the big-endian trailer, block validation, 16-line ZIP geometry. |
| `CodecGen.lean` | `codecgen <out.bin> <seed>`: PXR24 (uint/half/float, mixed sampled blocks), B44/B44A, RLE, ZIP, ADLER32 and PIZ kernel/Huffman vectors for `test/v3/codec_diff.c`. |
| `Texcomp/*` | `Container` (DDS/KTX/ASTC-file headers + payloads + writer verdicts), BC1/BC3/BC4/BC5 decoders and BC1/BC4/BC5 encoders, BC6H block decoders and every BC6H block encoder (unsigned 0–13, signed 0–8/12/13), BC7 pack path/mode 6/seeds/full default-option encoder/decoder-driven RDO pass, ETC2 individual/T-mode/EAC, the ASTC LDR top-level block encoder (`AstcLdr`), ASTC LDR + HDR endpoint packers, colour quantizer, weight decimation, weight infill, the encoder block-mode filter, the partition cache, the block-mode candidate ranking, the endpoint/colour-quant plumbing and the projection/least-squares/SSE fit kernels, the partition search, the partition-RGB and dual-RGBA encoders, and the ISE bit packer. Every model has a C-vs-Lean differential gate (`make texcomp-*-diff`). |
| `Tocio/*` | OCIO scaffolding: `Op` (op kinds + FixedFunction styles), Matrix/Range/Exponent/Log/CDL/LUT/YAML/Config/Resolve/Lower/Processor. `YamlTotal.lean`: fuel-bounded total YAML parser with the general inductive height-bound theorem (`parseTotal_height_bound` / `parseYamlTotalV_height_bound`: any accepted document has height ≤ the fuel budget) plus concrete depth-cap theorems (100/127 parse, 129 fails; boundary documented, see below). `FloatSemantics.lean`: identity/sign/round-trip laws for the exponent kernels, CDL round-trip within the C's 2e-3 tolerance on the non-negative grid, and Range clamp boundary semantics. `YamlEngine.lean`: C-faithful block+flow+tag parser model (`yamlParse` / `dumpTree`) pinned byte-for-byte against `toc_yaml_parse` by `make tocio-yaml-diff` (48 documents, `<tag>` prefixes included). `ConfigQuery.lean`: the `toc_config.c` query layer over the parsed tree (name/alias matching, role resolution, display-section membership, transform-attribute priority, view-looks tokenization) pinned by `make tocio-config-diff` (16 configs, query transcripts byte-identical). `ProcessorModel.lean`: the `toc_processor.c` pipeline build (transform walk order, inversions, colorspace references, fixed-function styles, reference-domain bridging, looks, view transforms) at op-kind level, pinned by `make tocio-proc-diff` (57 queries; numeric op parameters stay with the kernel gates). `CodegenC.lean` (+ `CodegenSnippets.lean`): the AOT-C emitter (scalar path) down to the hex-float literal writer, pinned by `make tocio-codegen-diff` (12 op lists, sources byte-identical). `CodegenGLSL.lean` / `CodegenMetal.lean`: the GPU emitters (all GLSL targets, MSL, decimal-float writer, LUT texture descriptors), pinned by `make tocio-glsl-diff` (16 shaders byte-identical). |

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
| structural-prefix round trip under `FileWireOK` (also canonical `FileEmitOK`) | `Exr/Emit.lean` | `parseFile_emit_raw` / `parseFile_emit` (single- and multi-part) | `lean-diff`, raw attribute order/extension regressions |
| PXR24 `float24`: RN truncation, Inf→Inf, NaN stays NaN, finite≠Inf | `Exr/Pxr24.lean` | `float24_lt`, `float24_inf`, `float24_nan_nonzero`, `float24_finite_not_inf` | `codec-diff` |
| PXR24 decode/encode stability | `Exr/Pxr24.lean` | `float24_shift_stable`, `float24_stable` | `codec-diff` |
| B44 t-transform is a bijection on finite halves | `Exr/B44.lean` | `unt8_t8`, `t8_nan`, `t8_range` | `codec-diff` (all blocks) |
| B44 shift search terminates and never needs its 16 fallback | `Exr/B44.lean` | `chooseShift_le`, `chooseShift_le_12`, `chooseShift_fits` | `codec-diff` |
| B44 reconstruction error (bounded by 2^11+1) at shift 12 | `Exr/B44.lean` | `shiftRound_12_abs_error`, `dvals_12_within` | — |
| B44 14-byte blocks stay below the `s[2] >= 52` flat marker | `Exr/B44.lean` | `packBlock_third_lt_52`, `packBlock_flat_byte2` | `codec-diff` |
| B44A flat form iff every residual equals the bias | `Exr/B44.lean` | `packBlock_flat_iff` | `codec-diff` |
| B44 14-byte block decodes exactly to the quantized values | `Exr/B44.lean` | `decode14_telescopes`, `unpack14_packBlock`, `decodeBlock_packBlock` | `codec-diff` (pack + unpack) |
| B44A flat block → constant, 3 vs 14 byte accounting | `Exr/B44.lean` | `decode3_constant`, `packBlock_length`, `blockBytes_mem` | `codec-diff` (constant/NaN/Inf/±0 blocks) |
| uncompressed row bytes = Σ over channels (× width) | `Exr/Size.lean` | `rowBytes_eq_finset_sum`, `rowBytes_eq_width_mul_pixelSize`, `rowBytes_le`, `rowBytes_lt_2pow64` | — |
| scan-line payload = `height × rowBytes`; per-chunk lines sum to the image height | `Exr/Size.lean` | `chunkLines_sum`, `scanlinePayloadBytes_eq`, `scanlinePayloadBytes_lt_2pow64` | — |
| B44 block stream totals (3/14 B per block); `packBlock` emits exactly `blockBytes` | `Exr/Size.lean` | `packBlock_length_eq_blockBytes`, `blockStreamBytes_eq_finset_sum`, `blockStreamBytes_le`, `blockStreamBytes_ge` | `codec-diff` |
| PXR24 plane-major row = Σ over planes (BigOperators form) | `Exr/Size.lean` | `packPlanes_length_eq_finset_sum` | `codec-diff` |
| offset-table region = 8 B × total chunks (parser and emitter sides) | `Exr/Size.lean`, `Exr/Parse.lean` | `parseTables_length`, `parseOffsetTable_length`, `parseTables_end`, `tablesBytes_of_parseTables`, `offsetTableBytes_size` | `lean-diff` |
| u32/u64 emitters do not truncate below 2^32/2^64; `ofNat` truncates above | `Exr/Size.lean` | `u64Bytes_faithful`, `u32Bytes_faithful`, `u64Bytes_ofNat_mod`, `u32Bytes_ofNat_mod` | — |
| RLE byte-run codec (interleave + predictor + runs) | `Exr/Rle.lean` | `interleaveDecode_encode`, `interleaveEncode_decode`, `predictorDecode_encode`, `predictorEncode_decode`, `rleExpand_rleEncode`, `rleEncode_length_le`, `rleCompress_length_le`, `rleRoundTrip` | `codec-diff` (bit-exact both directions) |
| ZIP container: ADLER32 (per-step = deferred modulo), zlib header checks, big-endian trailer, wrapper validation | `Exr/Zip.lean` | `adler32Acc_mod`, `adler32Go_lt`, `adler32_empty`, `zlibHeaderValid_78_01`, `zlibHeaderValid_78_9c`, `adler32Trailer_length`, `validateZlibBlock_of_valid`, `zipLinesPerBlock`, `zipsLinesPerBlock` | `codec-diff` (bit-exact checksum) |
| deep cumulative-count tables are exact inverses; last cum = chunk total; non-negative counts give valid tables | `Exr/Deep.lean` | `diffCounts_cumCounts`, `cumCounts_diffCounts`, `cumCounts_last`, `cumCounts_modular_valid`, `DeepChunk.WellFormed`, `WellFormed.offsetTableSize`, `WellFormed.sampleSize` | `lean-diff` (deep fixtures) |

## Differential harnesses

**Structural** (`test/v3/lean_diff.py`, `make lean-diff`) runs `exrcheck` and the
tinyexr `test/v3/parse_harness` over: `test/unit/regression/*` (including the
Lean-generated fixtures), `~/work/openexr-images` and `build/lean-gen/*`, and
compares accept/reject, part type, tiled/deep flags, computed chunk count,
offset-table length, data window and channel count.

Result: **126 files, 0 disagreements** (including the deep-tile fixtures).

**Codec** (`test/v3/codec_diff.c`, `make codec-diff`) reads TEXV vectors from
`codecgen`. Both the default backend (libdeflate in the normal build) and the
in-tree zlib backend run every seed. It checks:

* PXR24 decoder output and encoder intermediate planes, after inflating the
  opaque DEFLATE payload. Canonical raw fallback preserves original FLOAT bits;
  compressed output uses the model's float24 quantization. A mixed block spans
  three rows/channels with HALF/FLOAT/UINT, negative origins and x/y sampling.
* B44/B44A and RLE encoders and decoders byte-exactly, and ADLER32 values.
* ZIP intermediate predictor bytes and their Adler trailer; compressed decode,
  raw fallback, malformed header/checksum, truncation and wrong decoded size.
* PIZ small/full-range wavelet pairs and 2×2 cells against the actual private C
  kernels, bitmap bytes and LUT ranks, both canonical-code assignment routines,
  six-bit length-table serialization and Lean parsing including short/long zero runs, and
  symbol/RLE payload bits with a supplied balanced codebook. The C Huffman
  decoder also reconstructs these Lean-generated entropy streams. Complete
  frequency-derived Huffman headers/tables/payloads are compared byte-exactly
  with C encoding and parsed by both implementations, including truncated
  packets, wrong output budgets, invalid bit counts and deliberately ignored
  table-length/reserved fields.

There are **578 records per seed**: the original 358 records, 15 ZIP blocks,
9 compressible PXR24 rows, 77 PIZ lifting cells, 7 LUT inputs, 9 canonical-code
tables, 15 length tables, 11 entropy streams, one mixed PXR24 block, and 44 full multilevel PIZ traversal
cases (odd/nonsquare dimensions, one/two lanes, both branches, prefix/tail canaries),
and 12 frequency-derived Huffman tables (empty/zero, ties, sparse/trailing zero,
skewed and random frequencies, and the synthetic RLE symbol), plus 9 complete
Huffman packets and 11 malformed/lenient packet verdict comparisons.
Seeds are `12345 1 7 42 999 20240101 65535`; both backends give
**8092 record checks**, all bit-exact. Mutation controls corrupt every record
kind and require failure, including under ASan/UBSan. The PIZ implementation is
included under test-only public symbol names to reach its private kernels;
production APIs and dispatch remain unchanged.

### Bugs the harnesses found

| Harness | Finding | Resolution |
| --- | --- | --- |
| structural | `issue-238` fixtures have offset-table entries past EOF; the model accepted them | model gained the `dataStart ≤ off < fileSize` check (matches tinyexr) |
| structural | OpenEXR requires shared attributes (`displayWindow`, …) to agree across multipart parts; `exrgen` used different display windows | `exrgen` multipart now shares the display window (generator fix, not a C change) |
| composed PIZ Huffman parser | C accepted packets with fewer decoded samples than requested; fast decoding also confused loaded bits with consumed bits | **C fix** in `src/exr_piz.c`: exact output/consumed-bit budgets and bounded tail codes; unit tests cover fast and fallback paths. OpenEXR 3.1.11 fallback `hufDecode` independently checks final output size and truncated tail codes; its fast path still accepts two wrong-count probes (documented below). |
| ZIP integration (both backends) | the in-tree zlib wrapper accepted bad Adler trailers, unsupported preset dictionaries and CINFO above seven | **C fix** in `src/exr_deflate.c`: validate wrapper/checksum and clear output size on failure; stored-stream unit regressions cover both backends |
| codec (PXR24) | the C row layout is **plane-major**, not per-sample groups | model transposed (`packPlanes`/`unpackPlanesToGroups`); group algebra kept proven |
| codec (PXR24) | HALF/FLOAT reconstruction must truncate to `8*bytes` bits | `unpackGroupsAux` masks with `maskOf` |
| codec (B44) | residuals are **signed** during the shift search (`Nat` truncation accepts too-small shifts) | `residuals : List Int` + `0 ≤ r ≤ 0x3f` |
| codec (B44) | the decoder's middle columns chain from `v4`/`v8`, not `s0` | corrected `decode14Int`/`unpack14` (telescoping proof re-stated) |
| codec (B44A) | `unpack3` already sign-decodes; `decodeBlock` applied `unt8` twice | `unpack3` returns t-values |
| OpenEXR CLI cross-check | tinyexr v3 wrote **DECREASING_Y** scan-line chunks in increasing-y order, which OpenEXR rejects (`Invalid chunk index`) | **C fix** in `src/exr_writer.c` (`wr_scanline_block_index`, serial + parallel + deep paths); regression fixture `test/unit/regression/decreasing-y-scanline.exr` and a unit test that re-applies OpenEXRCore's rule |

The initial writer-order fix changed C behavior; the assurance follow-up also
fixes raw deep-tile count-table padding and the in-tree zlib wrapper checks, documented here. PXR24/B44 wire formats
are unchanged (their corrections and proofs are model-side).

The nine complete Huffman packet cases were also decoded byte-for-byte by the
installed OpenEXR 3.1.11 library (`ImfHuf.h`). Its fallback rejects a short-output
packet, but its fast decoder accepts the two 128-symbol packets requested as
127/129 outputs. These are malformed output-budget cases, not valid format
variants; the model and v3 now require exact output and declared bit consumption.
This independent probe is a local check, not an additional CI oracle.

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
* **PIZ is a staged formalization, not a complete file-codec inverse.** LUT
  rank reversal, both wavelet pairs/cells, full-range lifting-schedule algebra,
  and prefix-tree symbol-stream decoding are proven. `Exr/PizBits.lean` and
  `Exr/PizTable.lean` prove the MSB-first fields, byte packing/padding and the
  actual greedy length-table encoder/parser inverse, including 261-symbol run
  splitting, arbitrary suffixes, exact decoded length and ≤58 length bounds.
  `Exr/PizCodebook.lean` derives paths from checked insertion of the actual
  canonical table, rejecting duplicate/prefix collisions. `Exr/PizEntropy.lean`
  composes those paths with repeat expansion and proves the actual greedy
  entropy writer/parser inverse, exact output size and alphabet bounds.
  `Exr/PizPacket.lean` composes the Huffman header, table and entropy parser,
  with byte alignment and input/bit/output bounds. `Exr/PizPacketEmit.lean`
  proves the actual packet emitter/parser round trip, including sliced tables,
  the ignored advertised table-size field, byte padding and the entropy bit
  budget. Its hypotheses require representable lengths, active source symbols
  and successful checked canonical construction; the generated-table theorem
  below derives these premises from every accepted frequency profile.
  `CodecGen` uses this verified emitter for packet and whole-block vectors.
  `Exr/PizBlock.lean` now executes the outer bitmap framing and the complete
  Huffman → per-channel wavelet → reverse LUT → canonical reorder pipeline.
  `Exr/PizLayout.lean` proves sampled layout size and allocation/access bounds,
  including negative origins and mixed 16/32-bit channels. Its address sequence
  is proved to permute the entire allocation, and both actual array-scatter /
  canonical-gather inverse theorems (`canonical_planar`, `planar_canonical`)
  are proved for every geometry and buffer of the computed size. The UInt16
  array LUT rank/restore inverse also proves that narrowing ranks is safe;
  successful outer framing reconstructs exactly 8192 bitmap bytes.
  Whole-block vectors compare this composition against the C decoder, with
  the original canonical words checked independently, including a >16384-value
  alphabet that selects full-range lifting. `Exr/PizBitmap.lean` proves actual
  bitmap construction covers every source word. `Exr/PizBitmapSpan.lean` and
  `Exr/PizFrameEmit.lean` prove canonical min/max trimming, the empty sentinel,
  omitted-zero restoration and the complete outer framing inverse.
  `Exr/PizRoundtrip.lean` composes those results with Huffman parsing and every
  numerical stage, including the raw-fallback branch. The generated-table
  theorem below discharges its source, slicing and wire-size hypotheses from
  the actual histogram and C input-size bound, including canonical acceptance.
  The zero-sample differential exposed a model boundary error, now corrected:
  direct compressed PIZ decoding rejects a zero-word allocation; public dispatch
  accepts zero-byte raw fallback but rejects unequal empty or expanded input.
  `Block.decodeCompressed` and `Block.decode` model these distinct interfaces,
  and whole-block vectors compare both verdicts with C. No C change was needed.
  A kernel-proved `csimp` optimization skips canonical-word calculations for
  absent symbols without changing the logical table constructor. The frequency
  seed enumeration has a separate proved compilation optimization that replaces
  repeated list indexing with one indexed traversal.
  `Exr/PizHeap.lean` now proves minimum selection and heap-order preservation,
  strict size decrease and construction termination, frequency/leaf-count
  conservation, unique final leaves, bounded output indices and the 58-bit
  length cap. `Exr/PizKraft.lean` proves that every accepted full tree fills
  the 58-bit code space exactly (the integer Kraft sum). `Exr/PizLengthTable.lean`
  transfers that exact mass to the actual emitted length array and proves
  exact leaf-depth lookup, absent zero slots and positive active code lengths.
  Successfully prepared trees are proved non-singleton, retaining an active
  source symbol and its separate run marker. It uses the array binary
  heap whose sift-down strict/tie choices
  agree with C; its generated tables are checked against the actual C builder.
  `Exr/PizCanonicalMass.lean` relates that mass to the actual descending
  canonical recurrence. `Exr/PizCanonicalWords.lean` proves representability
  and prefix freedom, including symbol-index tie breaking;
  `Exr/PizCodebookTotal.lean` proves successful checked trie insertion. Thus
  every accepted frequency-generated table passes the actual constructor.
  `Exr/PizTraversal.lean` now supplies the actual
  multilevel cell/edge schedule, proves its power-of-two edge-test equivalence
  and allocation/stride bounds, and executes it against the private C traversal.
  Signed stride products require an explicit allocation bound (e.g. INT_MAX).
  `Exr/PizWavelet.lean` derives distinct addresses from geometry and proves
  inverses of the actual array cell/odd-edge updates, including local source
  bounds for 14-bit lifting. It proves full-range composition in reverse
  instruction order and proves that the complete executable `Traversal.run`
  preserves every entry outside its channel, in both directions and modes.
  `Exr/PizDisjoint.lean` proves generated levels have disjoint supports,
  including both odd edges. `Exr/PizWaveletInverse.lean` proves disjoint array
  instructions commute and derives the complete executable full-range inverse
  (`run16_inverse`) in the actual C decoder's order. `Exr/PizSmallRange.lean`
  proves the low-pass lattice invariant across every encoder prefix and derives
  the complete executable small-range inverse (`run14_inverse`) from initial
  sample bounds alone. `run_inverse` selects the appropriate theorem from the
  bitmap mode. `Exr/PizComposition.lean` proves cross-layout traversal
  commutation and disjointness of every generated channel/lane task, deriving
  the complete planar `waveletGo` inverse. `Exr/PizReconstruct.lean` composes
  scatter, bitmap-bounded ranks, all wavelet tasks, LUT restore and canonical
  gather to the source words; bitmap coverage is its explicit source condition.
  `Exr/PizDecodePacket.lean` connects that result to the actual Huffman packet
  emitter/parser. Bitmap coverage and framing are discharged by the actual
  bitmap builder and canonical trimmed-frame round trip. `PizHistogram.lean`
  derives source/marker activity and sliced zero-prefix conditions from the
  shared histogram/minimum/maximum computation; `PizWireBounds.lean` derives
  both wire budgets from C's source-size cap. `PizGeneratedRoundtrip.lean`
  composes those results for the frequency-generated table. Its `Block.encode`
  builds the histogram and table and chooses compressed or raw storage;
  `decode_encode` proves the complete round trip for successful encoding,
  valid geometry, matching source size and C's 33554431-word input cap.
  Canonical construction, source activity, bitmap coverage, traversal inverses
  and wire budgets are all derived internally. Frequency length generation
  may still return failure for profiles exceeding the supported 58-bit cap.
* **B44 perceptual tables (`p_linear` channels) are not re-modelled.** The
  t-transform, quantization, block packing and reconstruction are proven and
  bit-exact; the two 65536-entry `exp`/`log` double tables are validated by the
  C-side table test against libm (≤1 ulp), which is the agreed fallback bar.
* **Extraction is a subprocess oracle, not a linked static library.** The Lean
  executables (`exrcheck`, `exrgen`, `codecgen`) drive the C harnesses. Linking a
  Lean runtime into the ASan test binaries was judged brittle; this is the
  documented M5 fallback.
* **`parse (emit f) = some f` is proven for raw structural prefixes**
  under `FileWireOK` (`Emit.parseFile_emit_raw`). Raw attributes may be reordered,
  extended with unknown fields, or contain accepted deep sentinels. Mixed flat/deep
  multipart headers are supported through their explicit type attributes. Each
  header must be nonempty, have representable attribute names/types/lengths, and
  decode to its retained typed fields (`HeaderWireOK`). Tables must match chunk
  counts, offsets must fit 64 bits, and `dataStart` must match the prefix size.
  Parser fuel is bounded by actual raw attribute counts and emitted byte size,
  without a fixed per-header attribute limit. These are structural obligations;
  the theorem does not assert semantic validation or payload/chunk validity.
  The original canonical theorem `Emit.parseFile_emit` under `FileEmitOK` remains
  available. Both compose raw attribute parsing, typed interpretation, version
  parsing, and offset-table inverses. Generated fixtures retain their concrete
  `generate_*_parses` / `generate_*_valid` checks.
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
| `bv_decide` | 52 | `Exr/Bytes.lean` (3, LE write/read round trips), `Exr/Pxr24.lean` (22, float24 mask/shift/NaN/Inf arithmetic, `join_planes`/`maskOf` bounds), `Exr/B44.lean` (24: t-code sign cases, modular reconstruction, all residual/base/shift fields, finite-domain bounds and integer-to-word subtraction), `Exr/Piz.lean` (3 sites: small/full-range lifting pairs and the small-range 2×2 cell) | one `*._native.bv_decide.ax_*` per site (LRAT certificate checked by the tactic) |
| `native_decide` | 10 | `ExrGen.lean` (6 `generate_*_parses`, 3 `generate_*_valid`, 1 `generate_multipart_valid_openexr`) | one `*._native.native_decide.ax_*` per site (native evaluation, not kernel reduction) |

`bv_decide` goals stay small (≤ 32-bit arithmetic), so the LRAT certificates
are small and the tactic discharges them directly; `unt8_t8` is a sign-case
analysis with `bv_decide` leaves rather than a 65536-way `native_decide`.
The `ExrGen` self-checks evaluate multi-KB generated fixtures through the
byte-level parser; kernel `decide` was measured infeasible on the smallest
fixture (`generate "tiled"`, 2012 bytes) — it exceeds 4m40s at
`maxHeartbeats 100000000` / `maxRecDepth 100000` locally — so the ten checks
keep `native_decide` and are pinned byte-exactly by the harness instead.

The authoritative transitive census is now `make lean-axiom-check`. It visits
all first-party library and generator theorems, including private declarations
and generated auxiliary theorems, and prints the number that use bit-vector
certificates and approved native checks. Every dependency outside the three
standard logical axioms, first-party `bv_decide` certificates and the ten
explicitly approved native fixture checks is rejected, including `sorryAx`.
Negative regression tests inject both an arbitrary axiom and a `sorry` theorem
and require the audit to fail. Native fixture checks are not library proofs.
The differential harnesses remain the independent executable validation.
There is also no remaining tile-index injectivity gap: ONE_LEVEL, MIPMAP and
RIPMAP indices are all proven injective (`tileIndex_*_injective`).

## Fixtures added

* `test/unit/regression/decreasing-y-scanline.exr` — DECREASING_Y writer regression.
* `test/unit/regression/leangen-{scanline,tiled,mipmap,ripmap,deepscanline,multipart}.exr`
  — `exrgen` output, replayed by `make fuzz-corpus` under ASan+UBSan+LSan and by
  `make lean-diff`.

## Assurance hardening follow-up

The checker now validates known raw attribute schemas and duplicate names before
acceptance. A malformed optional attribute cannot disappear into an absent typed
field. Structural comparisons include absolute windows, dimensions, compression,
tile descriptions and every channel's byte name, type, sampling and pLinear flag.
Oracle crashes, missing/inconsistent reports, empty codec suites, unknown vector
kinds and trailing vector bytes fail the gates. `--require-corpus PATH` requires a
nonempty corpus; CI pins openexr-images and runs the differential gate regressions.
Lean tools are incremental Make prerequisites, so stale binaries cannot silently
stand in for changed source. Generation loops stop on the first failure.

`Deep.cumCounts`/`diffCounts` retain explicitly modular algebra;
`modularValidTable` is not a wire validity predicate. `Deep.validTable` instead
compares signed wire cumulative counts in widened integer arithmetic.
`Deep.Checked` gives mathematical count algebra, checked signed-32-bit row bounds,
row-wise tile encoding and unbounded totals across rows. `DeepChunk.WellFormed`
requires nonnegative counts, mathematical totals and per-row wire bounds.
Concrete kernel proofs cover signed wrap rejection, overflowing row rejection,
tile-row resets and totals above INT32_MAX. General wire serialization proofs and compressed deep payload
integration remain follow-up work; NONE row validation is now connected below.

`sampledCount`, `sampledChannelBytes`, `sampledRowBytes` and `sampledBlockBytes`
account for absolute sample coordinates and vertical subsampling. The previous
`rowBytes`/`blockPayloadBytes` equations describe full-resolution channels;
`sampledRowBytes_le` establishes their upper-bound relationship. These functions
are not yet connected to a full chunk-layout inversion theorem.

`exrgen` now honors its seed, varying odd/non-square extents and partial edge tiles
for seeds other than 1. Historical seed-1 bytes remain stable. The regression gate
fully loads all seven structures for seeds 1, 7 and 42, including nonzero deep
scanline variants and deep tiles. Strict shared metadata checks now cover
optional timecode and chromaticities, including one-sided absence.

Run `make lean-axiom-check` for the current complete theorem census (including
private and generated auxiliary theorems). It permits the three standard logical
axioms, first-party bv_decide certificates and native_decide only for the ten
explicitly approved generator checks. The current automated census includes compiler-generated and private auxiliary
theorems, so its total is broader than a manual count of named public lemmas.

`exrcheck --chunks file.exr` additionally reads every chunk header and checks
packed payload bounds, multipart identifiers, scanline coordinates and tile
coordinate/level/index correspondence. `--strict --chunks` combines both modes.
`Chunk.parse_bounds` proves successful bounded parsing places the complete
declared payload inside the input. Compressed bytes remain opaque to this mode. NONE count tables and sample
byte totals are checked; general pixel decoding and physical line-order
conformance are separate validation tasks. Regression tests cover all generated seeded
structures and corrupted chunk coordinates, part IDs, sizes and truncations.

`Deep.Checked.decodeRows_encodeRows` proves the checked mathematical tile-row
pipeline round-trips for every list of rows satisfying the signed-32-bit row sum
bound. The sanitized gate checks all seven codec vector kinds are represented,
runs all seven seeds, and uses a known-good vector control before negative tests.
In ptrace environments run it with `ASAN_OPTIONS=detect_leaks=0`; normal CI runs
retain LeakSanitizer.

## Executable codec and payload composition

B44 now exposes the exact `decode14Word` grid and proves it telescopes with
fixed-width wraparound. `unpack14_eq_decode14Word` and `unpack14_telescopes`
connect byte extraction to that grid. `pack14Word_base`, `pack14Word_shift` and
`pack14Word_residual` prove all bit-field extraction invariants;
`pack14_eq_word_of_bounds` lifts the natural encoder fields into that model.
`packBlock_residual14` establishes every selected encoder residual survives its
actual 14-byte packing. `decodeBlockChecked_packBlock` proves the checked,
marker-based standalone decoder accepts every encoder-produced block; codecgen
now uses that checked decoder. `unpack14_packBlock`, `unpack3_packBlock` and `decodeBlock_packBlock` compose
both wire forms with the selected quantization reference. `quantized_error`
proves the decoded t-code error is at most 1024 for the actual selected shift;
`packBlock_shift_le_11` and `selected_product_le_tmax` establish the stronger
finite-half-domain shift bound and absence of base underflow. Codecgen derives
expected B44 samples directly from `quantized` followed by `unt8`.

`sampledCountFast_eq` proves constant-time sample counting equals the finite
reference enumeration, including negative origins. `sampledBlockBytesFast_eq`
connects the bounded-row executable version to the sampling model.
`exrcheck --chunks` now checks exact NONE flat payload sizes, as well as NONE deep
cumulative-count rows and sample-byte totals. Compressed payloads remain opaque.
Deep count-table validation uses widened comparisons and per-row resets, with
kernel regressions for row resets and signed wrap rejection.

The generator includes nonzero deep scanline variants and a `deeptiled` kind.
The committed `leangen-deeptiled-edge.exr` is seed 42, with partial edge tiles;
fixture update/check gates cover it explicitly. `make lean-openexr-test` builds
an independent OpenEXR C++ fixture oracle and fully decodes all seven kinds for
seeds 1, 7 and 42, including every mip/rip level. It also checks v3-written deep
edge tiles under NONE/RLE/ZIPS. Negative controls require rejection of nonzero
samples and incorrect deep counts. The oracle is intentionally limited to these
small, zero-valued fixtures; it is not a general pixel comparator.

### Deep edge count-table interoperability fix

Independent decoding found that compact raw count tables on edge deep tiles
were rejected by OpenEXR 3.1.11. Its legacy writer stores a nominal tile's full
count-table byte length on raw fallback, packing real pixel counts first and
leaving an unused tail. The v3 writer now emits a zero-filled tail on raw
fallback; all count-table read paths accept nominal-size padding as well as the
previous compact encoding. Sample-data sizes and codec kernels are unchanged.
Every nominal-size calculation uses checked C arithmetic. The behavior is
covered through whole-image load, both deep block APIs, C re-encoding, OpenEXR
full decoding and the sanitizer corpus. The model accepts both count-table
sizes and validates the actual pixel rows only.

This follows the legacy reader/writer behavior in the local OpenEXR `v3.1.11`
source (`ImfDeepTiledInputFile.cpp` / `ImfDeepTiledOutputFile.cpp`). Current
OpenEXRCore `decoding.c` explicitly documents and accepts that historical
full-tile padding. The model also now allows an unnamed single deep part, as
both OpenEXR and the v3 writer do; multipart names remain mandatory and nonempty.

B44's error bound is in the monotone t-code domain, rather than a bound on the
real-number magnitude of reconstructed half values. Non-finite input halves
collapse to t-code 0x8000 as in C/OpenEXR; perceptual p_linear tables retain the
separately documented C-side numerical validation boundary.

B44 reconstruction now composes fully for both forms:
`decodeBlock_packBlock` and `decodeBlockChecked_packBlock_quantized` establish
actual emitted bytes decode to the quantized reference; `quantized_error` gives
the selected t-code bound. The byte-field proof is separate from the bounded
shift-search facts, keeping the proof fast enough for the normal Lake build.

### Texcomp: C defect found by the colour-quantizer gate

`tc_astc_hdr_color_roundtrip` (exposed in `texcomp_internal.h` for the ASTC HDR
endpoint packers) dispatched any `level < 20` to
`tc_astc_color_roundtrip`, which indexes `tc_astc_color_pquant_to_uquant[level - 4]`.
Levels 0..3 therefore read below the table base — an out-of-bounds read
(a segfault under the differential harness). The block encoders never request
those levels (the budget search yields 4..20 or 0xFF, and 0xFF takes the
identity path), but the helper itself was not defensive. It now returns the
unquantized value for `level < 4`, matching the "no table means no
quantization" reading used by the Lean model
(`Texcomp.hdrColorRoundtrip`). The gate `make texcomp-astc-quant-diff`
checks all 21 levels x 256 values plus the clamp edges (5394 values).

### Texcomp: ASTC LDR top-level block encoder (`AstcLdr.lean`)

`astcEncodeLdrBlock` ports `tc_encode_astc_ldr_block` end to end: the
per-tier scan caps / shortlist limits, the batch-scored luma-axis scan
(into a bounded error-sorted shortlist), the full-axis sweep with
least-squares endpoint upgrades, the iterative reproject/refit refinement
(before the partition fallback decision, as in C), the partition/dual/const
arbitration, and the final CEM value assembly, CEM 8/12 ascending-sum swap
and ISE bit-packing. Gate: `make texcomp-astc-ldr-diff` (bit-exact on every
tier and CEM).

Porting it pinned down three reference behaviours of the shared
partition-RGB encoder (`AstcPartitionRgb.lean`) that only fire at
`quality <= 1` — invisible to the original quality-2-only partenc gate,
which now covers all three tiers:

- The medium/fast candidate scan inserts `batch_start + bj`, the member's
  positional index, into the best/shortlist slots. Candidates skipped by
  the colour-quant budget check inside a batch shift that index off the
  true candidate, so the C can attribute a scored error to the wrong
  candidate (and even carry a `99u - weight_bits` unsigned underflow into
  the recorded quantizer). The model reproduces this exactly.
- The 3/4-partition caches are built only when `ctx->quality > 1`; with an
  empty cache `tc_astc_find_best_partition` always fails, so
  `partition_count` 3/4 cannot encode at reduced effort tiers.
- The per-seed variance sum accumulates in `uint64`: a seed that leaves a
  partition empty adds `UINT64_MAX` and the sum wraps modulo 2^64.
  `astcFindBestPartition` now folds modulo 2^64 as well.

Two further C behaviours surfaced once the vectors covered non-opaque
blocks and image-level clamped gathers (both fixed in the model, gates
re-greened):

- The scan-time colour budget check uses the C's pre-loop
  `endpoint_value_count`: for non-opaque blocks `tc_encode_astc_partition_rgb_block`
  re-classifies the endpoint format to CEM 10/12 (6/8 values per
  partition) *before* the candidate scan, while the opaque path keeps the
  classified format (4/6 values). The model originally computed one
  scan-time count from the pre-classification format for both, so
  non-opaque 2-partition scans accepted a different candidate set.
  `astcPartScanLoop`'s budget now matches the C's classification order.
- The encode context caches only **4** candidate lists keyed by
  `endpoint_end_bit`. At `quality == 0` the init pre-fills all four slots
  with the 33/49/65/81 luminance-family lists, so the partition path's
  29-bit request finds no slot and receives 0 candidates: the partition
  encoder can never succeed at quality 0 in any reachable context.
  `astcEncodePartitionRgbBlock` now returns `none` at quality 0 (matching
  AstcLdr's existing `quality > 0` guard on the fallback call).

### Texcomp: ASTC LDR image-level compress driver (`AstcLdrImg.lean`)

`astcCompressRgba8` ports `tc_astc_compress_rgba8`'s band loop: edge-clamped
block gather (`y >= height → height-1`, `x >= width → width-1`, yy-outer
xx-inner order as in C), then per-block dispatch — UASTC LDR when
`uastc != 0` (solid blocks handled inside the UASTC encoder), otherwise
`tc_encode_astc_ldr_block` for non-solid blocks and the const/void-extent
encoder for solid ones, with `quality`/`block_x`/`block_y` from the options.
The threads field only splits block rows across workers; output is
byte-identical for any thread count, so the model is the serial path.
Clamped gathers produce duplicated texel rows/columns that pure block-level
random vectors never hit — that is what exposed the two partition-encoder
behaviours above. Gate: `make texcomp-astc-ldrimg-diff` (40 images, 5 content
classes x 8 valid block footprints x quality 0-2, UASTC on 4x4 half of them).

### Texcomp: ASTC LDR image decoder and "uni" container (`AstcLdrImgDec.lean`, `Uni.lean`)

`astcDecodeImageRgba8` ports `tc_astc_decode_block_rgba8` /
`tc_astc_decompress_rgba8` (void-extent, block-mode, ISE, partitions, CEM
0-15 LDR, dual-plane; failures are `Option.none` = `TC_ERROR_CORRUPT` /
`UNSUPPORTED`). Gate: `make texcomp-astc-ldrdec-diff` (40 images: 20 encoder
round trips over 8 footprints + 20 random-block/random-footprint images that
exercise the failure paths).

`Uni.lean` models `texcomp_uni.c`: size, compress (= UASTC 4x4 image
encode), decompress (= 4x4 ASTC image decode) and the ASTC transcode (byte
copy; `uniTranscodeAstc_length`). Gate: `make texcomp-uni-diff` (40 images,
24 compressed + 16 random-stream images, 16 of which are rejected by the C
decoder and by the model alike).

`UniTranscode.lean` adds the BC1 and BC7 transcodes (`uniTranscodeBc1/Bc7`):
UNI decode, then the target's whole-image encoder (edge-clamped row-major
4x4 gather + `encodeBc1ColorBlock` / `bc7EncodeBlockDefault`, default options:
quick = 2, no PCA, all modes, rdo = 0). Gate: `make texcomp-uni-transcode-diff`
(36 streams: 20 accepted — flat, alpha-mixed and random content, BC7 modes
1/3/4/5/6/7 all exercised — and 16 corrupt streams that fail identically).
`Etc2Encode.lean` ports the ETC2 RGB encoder and the EAC alpha encoder
(`texcomp_etc2.c` / `texcomp_eac.c`): flat, individual, differential and planar
candidates with the C's strict-`<` selection order, the differential encoder's
"one out-of-range split abandons the whole call" behaviour, and EAC's
constant-block shortcut (returns just the value). The planar candidate does its
arithmetic in `Float32` (IEEE single, truncating `toInt32`), matching the C's
`float` code on x86-64 without FMA contraction. The image driver gathers
**column-major** (index = x*4 + y, as the C does) and emits the EAC block before
the RGB block for RGBA. Gate: `make texcomp-etc2-enc-diff` (400 blocks over ten
content classes; bits **and** errors of every candidate, the selected block, and
the EAC block compared; all four RGB modes win blocks — individual 185, planar 148,
differential 66, flat 1 — and EAC constant/full paths are both hit), plus
`uniTranscodeEtc2` in `make texcomp-uni-transcode-diff` (RGB and RGBA, 36 streams).
**Boundary:** BC7 with `rdo > 0` (`tc_bc7_rdo_pass`) is outside the model; uni
transcoding never enables it. The ETC2 model assumes the C is built without
FMA contraction of the planar float expressions (true for the x86-64 baseline
and for clang's default on macOS; GCC on AArch64 would need `-ffp-contract=off`
for bit-identity).

**Audit scope note.** `ExrSpec.lean` is the module root `lean-axiom-check`
enumerates; the ASTC LDR/UASTC/uni modules were not reachable from it, so their
theorems were silently outside the axiom census. `AstcLdrImgDec`, `Uni` and
`UniTranscode` (and the encoder chain they import) are now imported there
(census 3863 -> 3885, still no unexpected axioms). Modules that are only
imported by their own `*Check` executable are still unaudited. A later sweep
added `AstcHdrEnc`, `Bc1Props`, `Bc6hDecode` and `Tocio.LowerRecon` (census 3885 -> 3919).
Deliberately left out: `Tocio.FloatSemantics` (its `native_decide` fixtures are not on
the approved list), the `*Dbg` modules, and `Bc7Mode0` / `Etc2TModeDecode3`, which are
superseded by `Bc7Mode0Full` / `Etc2TModeDecode` and redefine the same names.

### Tocio: documented boundaries

* The total YAML parser's fuel charges one unit per parsed *line*, while
  the C (`TOC_YAML_MAX_DEPTH`) charges one per block. `yamlEntryFuel =
  2 * yamlMaxDepth` covers every document the C accepts within its cap
  with at most one item per level; deeper/wider synthetic documents fail
  earlier (pinned by `parseYamlTotalV_deep129`). Real configuration
  shapes are far inside both budgets.
* Soundness of that budget is now proved in general, not just by
  examples: `parseTotal_height_bound` shows by induction on the fuel
  that each worker only ever emits values whose `height` is bounded by
  its fuel (plus accumulated siblings), and
  `parseYamlTotalV_height_bound` lifts it to the entry fuel — no
  accepted document exceeds `2 * yamlMaxDepth` in height. The
  `Prod.Lex`-style well-founded measure fight is avoided entirely:
  every recursive call decrements the fuel by exactly one, so plain
  induction on `fuel` with a three-worker conjunctive motive suffices.
* `FloatSemantics.lean` proves the kernel laws on a sampled grid via
  `native_decide`; the full C-float correspondence remains gated by
  `make tocio-diff` (4096 blocks, 0 mismatches).
* `ConfigQuery.lean` models the `toc_config.c` query surface over the
  parsed tree and is pinned by `make tocio-config-diff` (16 configs; the
  transcript covers lookups, roles, displays/views/looks, view
  transforms and transform-attribute selection).
* `CodegenC.lean` ports the scalar AOT-C emitter and is pinned by `make
  tocio-codegen-diff` (12 op lists; generated sources byte-identical,
  including the verbatim helper snippets, hex-float literals and
  GamutComp13's codegen-time pow scale). The `simd` SSE2/AVX2 paths and
  the JIT backend are outside this model.
* `CodegenGLSL.lean` and `CodegenMetal.lean` port the GPU emitters
  (GLSL ES3.0/330/Vulkan450 and MSL) including the decimal-float writer
  and LUT texture descriptors, pinned by `make tocio-glsl-diff` (16
  shaders byte-identical). ACES 2.0 output transforms (precomputed
  parameter blob) and LUT1D NEAREST interpolation are outside the
  model.
* `ProcessorModel.lean` models the `toc_processor.c` pipeline build at
  op-kind level (transform walk order and inversions, colorspace
  references, fixed-function style ids, reference-domain bridging,
  looks, view transforms, the 64-level walk cap) and is pinned by `make
  tocio-proc-diff` (57 queries, 0 mismatches). Numeric op parameters are
  covered by the kernel/loader gates; `FileTransform`/`BuiltinTransform`
  payloads and singular-matrix inversion failures are outside this
  model. The processor build
  (`toc_processor.c`) remains outside the differential.
* `YamlEngine.lean` models the `toc_yaml_parse` surface (line
  preprocessing, block maps/dash sequences, block scalars, the flow
  parser, anchor/alias and trailing-content rejection, the 128-entry
  depth cap, and `!<Tag>` property attachment including the C's
  tag-overwrite on nested values) and is pinned by `make
  tocio-yaml-diff`: 48 documents whose canonical tree dumps are
  byte-identical to the C (0 mismatches). Termination fuel
  (`8 * length + 1024`) is a generous gate-validated over-approximation
  rather than a proved bound, while the depth cap counter is exact.

