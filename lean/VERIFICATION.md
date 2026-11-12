<!--
Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
SPDX-License-Identifier: BSD-3-Clause
-->

# Lean formalization and verification status

Updated: 2026-11-09. Toolchain: Lean 4.35.0 and the pinned mathlib dependency.
See [README.md](README.md) for the module inventory and format compatibility details.

The Lean model has machine-checked proofs. TinyEXR v3 C is validated against
that model by executable differential tests; this is not a proof of the C
implementation, its compiler, or memory safety for every possible input.

## Completed proof coverage

| Area | Proven model behavior |
| --- | --- |
| Container | Structural parser/emitter inverses, including arbitrary preserved attributes, reordered headers, offset-table layout and mixed flat/deep multipart files. Chunk-header reads and declared payload extents are bounded. |
| Sizes and deep data | Sampled-channel geometry, row/block sizes, cumulative-count/difference inverses and deep count/sample-size consistency. Compressed deep payloads remain opaque to structural validation. |
| PXR24 | Plane packing, float truncation/reconstruction and mixed-channel block sizing. |
| B44/B44A | Quantization, block packing and reconstruction, including flat blocks and bit-field bounds. Perceptual lookup tables are tested separately rather than re-proved. |
| RLE and ZIP wrapper | Interleave and predictor inverses, greedy RLE round trip and raw fallback; Adler-32 and ZIP wrapper structure/checksum. DEFLATE payload coding is outside the model. |
| PIZ | Complete successful encoder/decoder round trip through bitmap framing, frequency-derived canonical Huffman coding, both wavelet modes, sampled channel/lane traversal, LUT restoration, reordering and raw fallback. |
| Texcomp | Container headers/sizes and full DDS/KTX payload round trips; BC1/BC3/BC4/BC5 decoders and BC1/BC4/BC5 encoders; BC6H decoder modes plus every C block encoder (unsigned modes 0–13, signed modes 0–8/12/13) byte-exact against C; BC7 pack path, mode 6, seeds and the full default-option encoder; ETC2 individual/T-mode/EAC and ASTC LDR + HDR endpoint packers/colour quantizer. Each has a C-vs-Lean differential gate (`make texcomp-*-diff`) — see [Boundaries](#boundaries). |
| Tocio (scaffolding) | Op-kind + FixedFunction-style enums with inverse-pair invariants; Matrix/Range/Exponent/Log/CDL/LUT/YAML/Config/Resolve/Lower/Processor skeletons. Float semantics and YAML totality not yet proved — see [Boundaries](#boundaries). |

## PIZ proof chain and preconditions

The top-level theorem is
[`Exr.Piz.Block.decode_encode`](Exr/PizGeneratedRoundtrip.lean). For valid
layout geometry, a source word count matching that geometry, at most 33554431
16-bit source words, and successful `Block.encode`, the actual composed model
decoder returns the original source bytes. Empty input uses zero-byte raw
fallback. Frequency length generation can fail when the supported 58-bit
code-length cap cannot be met; the theorem does not assume universal encoder
success.

The proof derives its internal obligations from the source:

1. `PizBitmap`, `PizBitmapSpan` and `PizFrameEmit` establish source-alphabet
   coverage, canonical trimmed bitmap bounds and exact framing restoration.
2. `PizHeap`, `PizKraft` and `PizLengthTable` establish heap minimum/order
   properties, size-decreasing construction termination, frequency and leaf
   conservation, unique bounded leaves, emitted depths, absent slots and
   exact integer Kraft mass.
3. `PizCanonicalMass`, `PizCanonicalWords` and `PizCodebookTotal` connect that
   mass to the actual descending canonical assignment, prove representable
   prefix-free words including symbol-index ties, and derive successful
   checked trie construction for every accepted frequency-generated table.
4. `PizHistogram`, `PizFrequencySource` and `PizWireBounds` derive source/run
   marker activity, sliced zero-prefix restoration and wire-size budgets.
   `PizTable`, `PizEntropy` and `PizPacketEmit` supply actual table, greedy
   entropy and packet emitter/parser inverses.
5. `PizTraversal`, `PizDisjoint`, `PizWaveletInverse`, `PizSmallRange` and
   `PizComposition` establish allocation/stride bounds, disjoint schedules
   including odd edges, the 14-bit low-pass invariant, and complete 14/16-bit
   inverses across every channel/lane. `PizLayout` and `PizReconstruct`
   compose scatter/gather, rank, wavelets and LUT restoration.

Direct compressed PIZ decoding and public codec dispatch have distinct
semantics: direct decoding rejects a zero-word allocation; public dispatch
accepts equal-size raw input, including zero bytes, and rejects unequal empty
or expanded input. Whole-block differential vectors check both interfaces.

## Verification evidence

The final implementation validation on 2026-11-09 produced:

| Gate | Result |
| --- | --- |
| `make lean-tools lean-axiom-check` | Full build passed; 3479 first-party theorems (EXR + Texcomp + Tocio), 152 with bit-vector certificate dependencies, 98 with approved native checks; no unexpected axioms. |
| `make texcomp-lean-check tocio-lean-check` | New-module builds passed. |
| `make texcomp-bc6h-diff` | 1028 BC6H blocks (all 14 modes, signed + unsigned), C vs Lean byte-exact. |
| `make texcomp-bc6h-*-diff` | BC6H encoder models byte-exact against C: shared kernels (4215 values), unsigned modes 0/1/2/3/4/5/6/7/8/9/10/12/13 (400 + 520 + 1040 + 780 + 900 blocks), signed modes 0–8/12/13 (1800 blocks), and the per-block mode-selection drivers `tc_encode_bc6h_block_uf16`/`_sf16` (480 blocks, both variants). |
| `make texcomp-astc-partsel-diff` | 758 partition-search vectors: RGBA axis extremes, bitmap-mismatch popcount distance, the opaque/luminance/RGB-scale classifiers and `tc_astc_find_best_partition` end to end (2-means prefilter, mismatch shortlist, batched variance scan) over all 14 footprints and 2/3/4 partitions. |
| `make texcomp-astc-fits-diff` | 2 352 fit-path vectors: axis extremes, fixed-point projection weight, partition projection (ideal weights, active mask, per-texel endpoints), `weights_from_ideal{,_pt}`, `fit_from_ideal{,_pt}`, `rgb_sse_from_stats`, weight scramble/invert. |
| `make texcomp-astc-score-diff` | 200 score-from-ideal (all-texel + active-mask) and 120 score-batch (n=1) cases across all 14 footprints, C vs Lean exact (the C side's AVX2/SSE2 batch variants are bit-identical perf paths of the scalar kernel). |
| `make texcomp-astc-lsq-diff` | 2 700 least-squares/evaluation vectors: rounded division, `lsq_endpoints{,_partition}`, `eval_{single,partition,dual}_sse`, RGB clustering and the CEM 6/10 scale test. The C side runs its normal SSE2/AVX2 runtime dispatch, so the integer-exact scalar models are checked against the SIMD kernels too. |
| `make texcomp-astc-ise-diff` | 284 ISE encode-bit vectors (trit/quint/plain paths, arbitrary bit offsets) byte-exact against C. |
| `make texcomp-astc-endpoints-diff` | 8 464 endpoint-type/value-count cases, 2 016 colour-quant budget choices and 2 026 endpoint emits, C vs Lean exact. (The C `tc_astc_emit_partition_endpoint_values` writes into a caller `uint8_t[18]`; the gate only feeds format sets with ≤ 18 symbols, as the encoder does.) |
| `make texcomp-astc-candidates-diff` | 252 block-mode candidate lists (38 300 entries) across all 14 footprints, 3 quality levels, 3 endpoint budgets and both plane counts, C vs Lean exact in both content and percentile order (the Arm astcenc percentile table is copied in `Texcomp/AstcPercentiles.lean`). |
| `make texcomp-astc-partition-diff` | 43 008 per-seed partition-map digests (all 14 footprints, 2/3/4 partitions) plus 12 733 deduplicated cache entries (8 footprints up to 12×12), C vs Lean exact, including the hash pre-check and canonical-map dedup. |
| `make texcomp-astc-blockmode-diff` | All 2048 ASTC block modes compared with the encoder's `tc_astc_decode_block_mode_2d` (775 admissible), including the 24–96 weight-bit budget test. |
| `make texcomp-astc-infill-diff` | 12 weight-quant LUTs (65 entries each: `wq_q`/`wq_wt`/`wq_err`), 84 grid infills and 1008 quantised infills over all 14 footprints, C vs Lean byte-exact. The model uses the encoder's own `tc_astc_weight_unquant` table, which differs from the decoder's symbol-ordered `weightUnquant`. |
| `make texcomp-astc-decim-diff` | 10 164 per-texel weight taps + 112 decimation cache entries (all 14 ASTC footprints) byte-exact against C; the gate caught a `Nat`-truncation bug in the model's `16 - x_frac - y_frac + w3` term. |
| `make texcomp-bc7-rdo-diff` | 768 blocks through the decoder-driven RDO pass (`tc_bc7_rdo_pass`, two rate-distortion budgets over a 384-block synthetic image), C vs Lean byte-exact incl. the 64-block decode ring. |
| `make texcomp-bc7-diff` | 530 BC7 blocks (all 8 modes), C vs Lean byte-exact. |
| `make texcomp-bc135-diff` | 1536 BC1/BC3/BC5 blocks, C vs Lean byte-exact (BC5 snorm float step excluded, see Boundaries). |
| `make texcomp-etc2-diff` | 1024 ETC2/EAC blocks (all 5 RGB modes + EAC alpha), C vs Lean byte-exact. |
| `make texcomp-astc-diff` | 1024 ASTC LDR blocks (C-encoder output, all partition/CEM paths exercised), C vs Lean byte-exact. |
| `make texcomp-astc-quant-diff` | 5394 colour-quant values: `tc_astc_hdr_color_roundtrip` — the sub-256 colour-roundtrip LUT the ASTC HDR CEM 11 endpoint packers use (e.g. level 12 in the 2-subset encoder) — at all 21 quant levels × 256 values plus the clamp/negative edges, C vs Lean exact. |
| `make texcomp-astc-hdrenc-diff` | 240 ASTC HDR block-encoder vectors (60 seeds each of CEM 11 single/dual-plane, CEM 11 2-subset, CEM 7 and CEM 15), C vs Lean byte-exact including the SSE return and no-fit verdicts. |
| `make tocio-diff` | 4096 Tocio blocks: seven op kernels + FixedFunction styles, C vs Lean bit-exact except 12 documented RedMod seam residue blocks (relative deviation ≤ 3e-3). |
| `make codec-diff` | 8192 comparisons across seven seeds and both libdeflate/in-tree backends; zero failures. Includes PIZ primitives, frequency tables, malformed/lenient packets and whole blocks. |
| `make lean-validation-test` | 20 tests, two optional skips; all executed tests passed. Includes gate negative controls and axiom-audit rejection tests. |
| `make lean-diff` | 126 structural files checked; zero disagreements. |
| `make lean-gen-check` | Committed generated fixtures current. |
| `ASAN_OPTIONS=detect_leaks=0 make THREADS=1 lean-validation-sanitize` | All 8192 codec comparisons and the 20-test regression suite passed, with two optional skips. ASan, UBSan and float-cast-overflow instrumentation enabled. |
| `make lib c11-gate` | Library build and strict pure-C11 gate passed. |
| `ASAN_OPTIONS=detect_leaks=0 make test-c fuzz-corpus-asan` | 316 unit checks and 8297 streaming/hardening checks passed; 1238 corpus files replayed without crashes or sanitizer errors. Counts reflect the local build configuration and available fixtures. |

These results describe the tested corpus and configurations, not exhaustive
input coverage. The sanitizer retry was necessary because the initial default
LSan run aborted with “LeakSanitizer does not work under ptrace”. Local
`detect_leaks=0` results do not establish leak freedom. CI retains the full
LSan-enabled validation and `make fuzz-corpus` gates.

## Reproduce and maintain

From the repository root:

```sh
make lean-tools lean-axiom-check
make codec-diff lean-validation-test lean-diff lean-gen-check
make lean-validation-sanitize
make lib c11-gate test-c fuzz-corpus
```

For a ptrace environment where LSan aborts, use the two documented
`ASAN_OPTIONS=detect_leaks=0` commands in the results table as local fallbacks;
retain the LSan gates in CI. Run build targets sequentially when they share
object files or generated vectors. The axiom gate rejects `sorryAx`, arbitrary
added axioms and unapproved native evaluation; approved fixture checks are
validation checks, not library proofs.

## Boundaries

- DWAA/DWAB are intentionally unsupported; no DWA formalization or codec work
  is planned. HTJ2K/JPH internals are separately owned.
- DEFLATE payload coding, B44 perceptual table derivation and a proof connecting
  C execution semantics to Lean remain outside the proved model.
- Structural acceptance does not imply every compressed payload is valid.
  Differential/sanitizer gates supply independent implementation evidence.
- Tocio models are scaffolding: Tocio Float/YAML reasoning is incomplete, and no
  engine differential harness exists yet (`tocio-lean-diff` currently runs only
  the C tests). Texcomp is covered by implementation-level differential gates
  rather than an engine-level one. Plan for completion is in
  `~/.opencode/plan/lean-remaining-tasks.md` (outside repo).
- Texcomp BC/RG/ETC2/EAC/ASTC block decoders are now faithful byte-exact ports
  with C differential gates. The ASTC HDR *endpoint packers* (`cem11Pack`,
  `cem7Pack`, `hdrAlphaPack` — encoder side) are also byte-exact against the
  C packers at the block encoders' colour-quant level (1800 vectors).
  DDS/KTX/ASTC header models now have general `parse (emit h) = h` round trips
  (no example-only checks), payload-carrying `DdsFile`/`KtxFile`/`AstcFile`
  round trips (`parse (emit (h, payload)) = (h, payload)`), and a
  byte-layout gate against the C writers (`make texcomp-container-diff`,
  56 records — header *and* payload, with the payload pattern
  recomputed independently on both sides — plus verdict-only `E` records
  whose guard-chain verdicts (`ddsWriteVerdict` / `ktxWriteVerdict` /
  `astcWriteFileVerdict`) must match the C writers on both success and
  `INVALID_ARGUMENT` inputs). The gate covers the 10 DDS writer cases
  (BC7/BC1/BC3/BC5/BC6H), the 8 KTX writer cases (ETC2 RGB/sRGB, EAC R11/RG11,
  and the RGBA-alpha `0x9278`/`0x9279` internal formats), the full `.astc`
  file container (`tc_astc_write_file_memory`
  LE-magic header with 24-bit extents) across all 14 valid block footprints
  with partial-block extents, the 10 invalid footprints, and zero-dim /
  short-buffer verdict cases. Documented out of reach: the `size_t`-wrap
  regime (DDS verdicts still agree below `2^64` — the C's wrap is caught by
  its `UINT32_MAX` pitch guard; the KTX wrap regime would emit a header
  declaring a zero-length payload for a 2^60-block image — the model does
  not reproduce that success). Encoder models: the BC1
  colour-block encoder (`tc_encode_bc1_color_block`, 1200 blocks) and the
  BC4/BC5 alpha-block encoders UNORM+SNORM (`tc_encode_bc4_block*`,
  800 blocks) are byte-exact with the C encoders.
- BC6H unsigned encoders: modes 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13
  are byte-exact against the C block encoders, each with its own C-vs-Lean
  differential gate over seeded random blocks (mode 0: 400 blocks;
  modes 2/3/4 plus mode 5: 1040; modes 6/7/8: 780; modes 10/12/13: 900;
  modes 1/9: 520), including the no-fit (`UINT64_MAX`) path and the exact
  SSE return. Mode 9 additionally models `tc_bc6h_mode9_selectors` (the
  6-bit `unquant_n_to_mag` palette), and mode 1 reproduces the C's
  `pack_delta5` clamp of its 6-bit delta fields to [-16, 15].
  The shared kernels (10/N-bit quant + unquant, TOPK partition prefilter,
  least-squares refinement, anchor fix-up, `pack_delta5` clamping) are
  modelled once and reused. The signed (`sf16`) BC6H encoders are also
  byte-exact for every C `_sf16` mode (0–8, 12, 13; `make
  texcomp-bc6h-sf16-diff`, 1650 blocks, 825 encoded, 825 no-fit), including
  the C's `(uint32_t)` two's-complement bit extraction and its hard-coded
  ±511 clamp inside `tc_bc6h_refine_sf16`. The per-block mode-selection
  drivers `tc_encode_bc6h_block_uf16`/`_sf16` are modelled too
  (`Texcomp/Bc6hEncodeBlock.lean`, `make texcomp-bc6h-block-diff`, 480
  blocks covering both variants), including the `48 * 256 * 256`
  early-stop threshold, the fixed candidate order, and the fact that the
  signed driver's seed compares the luma key *signed* while modes 12/13
  compare it as `uint32_t`. The BC7 decoder-driven RDO pass
  (`tc_bc7_rdo_pass`) is modelled on top of `bc7DecodeBlock`
  (`Texcomp/Bc7Rdo.lean`, `make texcomp-bc7-rdo-diff`, 768 blocks with
  72 reuses), covering the 64-block decoded-pixel ring, the
  first-best-wins slot scan and the `rdo^2 * 16 * 4` distortion budget.
  The sub-256 colour-roundtrip LUT used by ASTC HDR 2-subset encoding
  (`tc_astc_hdr_color_roundtrip`, modelled as `Texcomp.hdrColorRoundtrip`)
  is exhaustively gated (`make texcomp-astc-quant-diff`, all 21 quant
  levels × 256 values plus the clamp edges) and exercised end to end
  through the 2-subset CEM 11 encoder in `make texcomp-astc-hdrenc-diff`
  (240 blocks, four HDR CEM kinds).
  Remaining Texcomp work: none tracked — the payload-parity extension of the
  container gate (ASTC `.astc` file container, KTX ETC2 RGBA cases, and
  writer error-verdict parity) is complete.
- Tocio: Float64-vs-f32 note aside, the seven op kernels (matrix, range,
  exponent, exp-linear, log, log-camera, CDL) are bit-exact `Float32` ports
  with a C differential gate (3072 seeded groups). FixedFunction helpers
  (RedMod/Glow/DarkToDim/GamutComp/HSV/XYZ/PQ/HLG/Surround) are ported and
  differentially tested bit-exact (the only RedMod B-spline coefficient
  error in the port, a −0.75-for−0.25 constant in the j=3 branch, was
  caught by this gate and fixed in `Tocio/FixedFunc.lean`). YAML totality,
  config lowering, and the .cube/.spi LUT loaders are total with C
  differential gates (192 .cube seeded blocks bit-exact; 200 .spi1d/.spi3d
  vectors bit-exact including parse-failure parity and applied pixels).
  The CLF loader (Matrix, Range, Exponent, Log, ASC_CDL, LUT1D, LUT3D,
  bit-depth normalization, UNSUPPORTED-not-skip discipline) is total
  with a C differential gate (396 seeded vectors bit-exact including
  error-kind parity and applied pixels). Loader safety invariants are
  proved for the SPI path (`spi1dVals` collects exactly `want` samples;
  `spiValuesFit` is sound), which is what stops a short sample buffer from
  reaching the stride-3 kernels. The CSP loader (line reader,
  case-insensitive prefixes, Rising-Sun spline preluts, 1D/3D LUTs) is
  total with a C differential gate (74 seeded vectors bit-exact).
- OpenEXR-compatible parser leniencies and C defects exposed by validation are
  documented in [README.md](README.md); keep those records synchronized when
  the executable model or C implementation changes.
