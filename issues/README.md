# Issue reports produced by the Lean formalization / differential validation

These reports came out of building a Lean 4 model of the OpenEXR container and
codecs (`lean/`) and validating it against the tinyexr v3 implementation, the
OpenEXR library and the OpenEXR command-line tools. Both findings are
reproducible with the fixtures in this directory; neither requires the Lean
toolchain to reproduce.

| Report | Target | One-line summary |
| --- | --- | --- |
| [`spec/001-maxsamplesperpixel-deep-required.md`](spec/001-maxsamplesperpixel-deep-required.md) | format specification | `maxSamplesPerPixel` is documented as *required* for deep parts, but OpenEXR never reads it and its own 12 deep sample images omit it (source comment says it is "not actually used anywhere"). |
| [`openexr/001-exrmultipart-convert-part-types.md`](openexr/001-exrmultipart-convert-part-types.md) | OpenEXR (`exrmultipart`) | `exrmultipart -convert` hard-codes scanline `InputPart`/`OutputPart`, so it cannot convert valid tiled or deep single-part files; it fails with `"Can't build a OutputFile from a type-mismatched part."` |

## How each was found

**Spec report.** The Lean model encodes the header-requirement table from
`OpenEXRFileLayout.rst` literally (`lean/Exr/File.lean`, `validateChecks`). With
that rule, `exrcheck` rejected every deep file in `openexr-images/v2/` while the
C reader accepted them; `test/v3/lean_diff.py` surfaced the disagreement. The
root cause is the stale table row documented in the report, and the constant is
commented out in OpenEXR's own source.

**OpenEXR report.** The cross-check step of the plan feeds model-validated files
to the OpenEXR CLI. Tiled files that the Lean checker classifies as valid
(`file-ok true`, `type=tiledimage`, chunk count consistent) and that tinyexr
loads are rejected by `exrmultipart -convert`. Reading `convert()` showed it
uses the scanline part classes while its sibling modes (`-combine`, `-separate`)
dispatch on all four part types.

## Fixtures

```
spec/fixtures/gen_deep_no_maxsamples.py   # deterministic writer, stdlib only
spec/fixtures/deep_no_maxsamples.exr      # 449 bytes, 1x1 deep scanline, no maxSamplesPerPixel
spec/fixtures/read_deep.cpp               # OpenEXR C++ reader: sample counts + A/Y/Z values
openexr/fixtures/tiny_tiled_1x1.exr       # 335 bytes, 1x1 tiled single-part
```

## Reproducing the two failures quickly

```sh
# 1. Spec: OpenEXR fully decodes a deep file that the spec calls invalid.
python3 spec/fixtures/gen_deep_no_maxsamples.py /tmp/deep.exr
g++ -std=c++17 spec/fixtures/read_deep.cpp $(pkg-config --cflags --libs OpenEXR) -o /tmp/read_deep
/tmp/read_deep /tmp/deep.exr
# read 1x1 deep pixels, sampleCount[0,0]=1, A=1.0000 Y=1.0000 Z=1.0000

# 2. OpenEXR: convert refuses a valid tiled file (the 4.6 MB shipped
#    openexr-images/Tiles/Ocean.exr fails identically).
exrmultipart -convert -i openexr/fixtures/tiny_tiled_1x1.exr -o /tmp/out.exr
# ERROR: Cannot initialize output part "0". Can't build a OutputFile from a type-mismatched part.
```

## Environment used

* OpenEXR 3.1.11 (system install) for runtime reproduction.
* OpenEXR `main` source checkout (`/mnt/nvme02/work/openexr`) inspected to cite
  code paths and confirm the `exrmultipart` bug is still present.
* Lean 4.35.0 model in `lean/` (`make lean-check`, `make lean-diff`,
  `make codec-diff`) for the provenance described above.
