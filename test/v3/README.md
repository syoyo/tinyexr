# TinyEXR v3 parse test foundation

Parse/load every `*.exr` under a directory tree (default: `~/work/openexr-images`)
through the pure-C11 v3 public API (`include/exr.h`) and classify each file.

## Pieces

- **`parse_harness.c`** — a tiny C program linked against `build/libtinyexr3.a`.
  For one file it prints machine-readable lines:

  ```
  FILE <path>
  HEADER_RESULT <code> <string>
  PARTS <n>
  PART <i> type=<scanline|tiled|deep_scanline|deep_tiled> compression=<NAME> channels=<n> size=<w>x<h>
  LOAD_RESULT <code> <string>
  ```

  It parses headers first (so the per-part compression is reported even when the
  full decode fails), then attempts a full `exr_load_from_memory()`. Exit 0 iff
  the load succeeded.

- **`parse-tester.py`** — stdlib-only Python driver. Globs `*.exr`, runs the
  harness on each, and buckets results:

  | Status  | Meaning                                                              |
  |---------|----------------------------------------------------------------------|
  | `PASS`  | Full load succeeded.                                                  |
  | `XFAIL` | Load failed, but the failure is **expected**. Currently DWA only.    |
  | `XPASS` | A file we expected to fail actually loaded (stale expectation).      |
  | `FAIL`  | Load failed and the failure is **not** expected — reported in detail.|

  Expected failures are driven by `EXPECTED_FAIL_COMPRESSIONS = {DWAA, DWAB}`.
  v3 intentionally does not implement the lossy DCT DWA codecs (see `AGENTS.md`),
  so any part using DWAA/DWAB is classified `XFAIL`.

## Usage

```sh
# Build the harness (also builds build/libtinyexr3.a):
test/v3/parse-tester.py --build

# Run over the default corpus (~/work/openexr-images):
test/v3/parse-tester.py

# Or point at any tree / subset:
test/v3/parse-tester.py ~/work/openexr-images/ScanLines
test/v3/parse-tester.py -v --progress ~/work/openexr-images   # list every file + live progress
test/v3/parse-tester.py --timeout 600 ~/work/openexr-images    # per-file timeout (s)
```

Exit status is non-zero if there is any `FAIL` or `XPASS`.

## Notes

- A full single-threaded sweep of the 299-file corpus takes ~35s; `-j` (default:
  all cores) speeds it up further. Use `--progress` to watch and point the tester
  at a single subdirectory for quick iteration.
- Building the harness by hand:

  ```sh
  make lib
  cc -std=c11 -Iinclude -O2 test/v3/parse_harness.c build/libtinyexr3.a -lm \
     -o test/v3/parse_harness
  ```

## Lean differential assurance

`make lean-validation-test` checks oracle process/report failures, malformed
metadata, seeded structural fixtures, optional shared metadata in strict mode and
chunk corruption rejection. `make lean-validation-sanitize` additionally runs the
codec differential harness under the C sanitizers. Each accepted part report now
includes `WINDOW`, `COMPRESSION`, `TILE` and `CHANNEL` records. Channel byte names
are dot-separated decimal octets so whitespace and non-UTF8 names are unambiguous.

`lean_diff.py --require-corpus PATH` fails if the required corpus is absent or
empty. Missing optional corpus paths remain diagnostic skips. Header acceptance
and metadata agreement are distinct from a successful full pixel load; only the
seeded valid-fixture tests require both. `exrcheck --chunks` is an additional
chunk-layout/bounds check and leaves compressed payload bytes opaque.

`make lean-openexr-test` requires OpenEXR development libraries and pkg-config.
It builds a bounded independent C++ oracle that fully decodes the small,
zero-valued Lean fixtures, checks every level and validates deep sample counts.
The same gate re-encodes partial deep tiles through v3 under NONE/RLE/ZIPS and
requires OpenEXR to read them. The C implementation and its strict C11 gate
retain no C++ dependency; only this independent reference probe uses C++.

`make codec-diff` checks 20 TEXV record kinds: PXR24 rows (0–2), B44/B44A (3–4),
RLE (5), ADLER32 (6), ZIP intermediate/checksum (7), PIZ 14/16-bit lifting (8–9),
PIZ bitmap/LUT (10), canonical Huffman assignment (11), Huffman length-table
zero runs (12), Huffman symbol/RLE payload (13), and a mixed, sampled PXR24 block
(14), and full multilevel PIZ traversal (15–16), including stride and canary
checks, and frequency-derived PIZ Huffman tables (17), complete Huffman packets (18), and malformed/lenient
packet verdicts (19). All seven seeds run with the default and explicit in-tree zlib backend.
PXR24/ZIP encoder streams are inflated to compare the model's intermediate
bytes; DEFLATE itself remains outside the formal model. The PIZ checks compile
the actual implementation under test-only public symbol names, accessing its
private kernels without adding production API hooks. See `lean/README.md` for
the distinction between proven PIZ algebra and remaining full-codec proofs.

PIZ length-table vectors now obtain their expected decoded values from the
Lean parser. `PizBits.lean` proves the arbitrary-width MSB field and byte-padding
inverses; `PizTable.lean` proves the greedy table emitter/parser round trip,
including run splitting and decoded-length/input-consumption bounds.

Complete Huffman packets now compare the frequency-derived Lean encoder with
C byte-for-byte, and compare decoded samples through the composed Lean packet
parser. The malformed matrix covers truncation, wrong symbol and bit bounds,
wrong output counts, and the C reader's ignored table-size/reserved words.
The resulting C fixes enforce exact output and declared bit consumption on both
fast and fallback Huffman paths; dedicated C unit cases exercise both paths.

The codec vectors also exercise complete model-generated PIZ blocks (kind 20),
including bitmap extents and the empty-bitmap sentinel, frequency-derived
Huffman packets, both word lanes of FLOAT/UINT channels, odd dimensions,
negative origins, mixed channel sampling and a zero-width sampled channel.
The Lean composed decoder and C PIZ decoder must both reproduce the original
canonical words. C encoder output must also match the model packet bytes when
compression helps, or the canonical raw bytes when it does not. This extends
the isolated PIZ kernel/packet differentials;
it does not establish the still-open whole-codec inverse theorem.

The packet and whole-block generators share `Exr.Piz.Packet.emit`, whose
parser round trip is proved in `Exr/PizPacketEmit.lean`. The theorem includes
the actual sliced table, header, byte padding and payload budget. It assumes
a successfully checked canonical table; total validity of heap-derived tables
remains a separate proof obligation.

`Exr/PizWaveletInverse.lean` now proves the complete executable 16-bit wavelet
traversal inverse in the C decoder's actual order. The existing odd-dimension,
strided-lane and nonzero-base traversal vectors continue to compare that
executable traversal directly against the private C kernel. Generated levels'
point/address disjointness is proved in `Exr/PizDisjoint.lean`.
`Exr/PizSmallRange.lean` proves the multilevel 14-bit lattice invariant and
complete small-range traversal inverse from initial sample bounds alone.

The whole-block generator now uses the shared, verified
`Exr.Piz.Block.coefficients` implementation. Seed 12345 additionally includes a
129×129 HALF block with 16641 distinct values, selecting the complete full-range
PIZ path. Its model/C decoding and C encoder bytes are checked alongside the
small-range mixed-channel and subsampling cases. The seven-seed sweep contains
4096 records (8192 comparisons across the two DEFLATE backends).

Whole-block vectors also share the verified `Bitmap.make` and
`Block.emitFraming` implementations. The bitmap builder's source coverage and
the canonical trimmed-frame round trip (including the empty sentinel and
omitted zeros) are kernel-proved. `Block.decode_emitWithTable` composes the full
block inverse and raw fallback under explicit canonical-table/source/size
conditions; deriving those conditions from the frequency builder remains open.

A complete zero-sample subsampled block additionally checks rejection of a
compressed empty-bitmap/Huffman frame and acceptance of the encoder's zero-byte
raw fallback. Kind 20 stores separate model verdicts for direct PIZ decoding and
public dispatch; the latter also rejects expanded representations. C encoder
output is decoded through public dispatch as an additional round-trip check.

Packet vectors now use the shared `Frequency.countSymbols` histogram. Its
source/marker activity and zero-prefix properties, exact emitted length-table
Kraft mass, and table/payload size budgets are proved. The generated-table block
round trip derives those conditions internally; checked canonical construction
for every accepted length table is the remaining proof obligation.
