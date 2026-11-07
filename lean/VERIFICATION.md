<!--
Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
SPDX-License-Identifier: BSD-3-Clause
-->

# Lean formalization and verification status

Updated: 2026-11-07. Toolchain: Lean 4.35.0 and the pinned mathlib dependency.
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

The final implementation validation on 2026-11-07 produced:

| Gate | Result |
| --- | --- |
| `make lean-tools lean-axiom-check` | Full build passed; 2980 first-party theorems, 152 with bit-vector certificate dependencies, 10 with approved native fixture-check dependencies; no unexpected axioms. |
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
- OpenEXR-compatible parser leniencies and C defects exposed by validation are
  documented in [README.md](README.md); keep those records synchronized when
  the executable model or C implementation changes.
