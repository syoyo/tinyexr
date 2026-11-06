# `exrmultipart -convert` cannot convert valid tiled or deep single-part files

- **Component:** `exrmultipart` (`src/bin/exrmultipart/exrmultipart.cpp`), also present in current `main`
- **Severity:** medium — the tool fails with a misleading error on files that the
  same tool's `-combine`/`-separate` modes and the library handle correctly
- **Found by:** cross-checking model-validated files against OpenEXR tooling during
  the Lean 4 formalization of the format (the Lean structural checker classifies
  the inputs as valid `tiledimage`/`deepscanline` parts; tinyexr loads them; only
  `exrmultipart -convert` fails)

## Summary

`exrmultipart -convert` is documented as "convert input to EXR2 multipart" and
accepts any single-part input, but `convert()` hard-codes the **scanline** part
classes (`InputPart` / `OutputPart`). For a single-part file whose `type` is
`tiledimage`, `deepscanline` or `deeptile`, it aborts with:

```
ERROR:
Cannot initialize output part "0". Can't build a OutputFile from a type-mismatched part.
```

Scanline conversion works, so this is not a general "unsupported file" path — it
is a missing part-type dispatch in `convert()`.

## Reproduction

Run from `issues/openexr/`. Using OpenEXR's own shipped tiled sample (no custom
file needed):

```console
$ exrheader openexr-images/Tiles/Ocean.exr > /dev/null && echo "valid tiled EXR"
valid tiled EXR

$ exrmultipart -convert -i openexr-images/Tiles/Ocean.exr -o /tmp/ocean_mp.exr
input:
      openexr-images/Tiles/Ocean.exr
output:
      /tmp/ocean_mp.exr
override:0

-convert input to EXR2 multipart

ERROR:
Cannot initialize output part "0". Can't build a OutputFile from a type-mismatched part.
$ echo $?
1
```

Minimal 335-byte fixture (1×1 tiled, one HALF channel, `flags 0x200`; accepted
by `exrheader` and fully decodable by OpenEXR's tiled reader, e.g.
`exrmakepreview`; attached as `fixtures/tiny_tiled_1x1.exr`):

```console
$ exrheader fixtures/tiny_tiled_1x1.exr | head -4
file format version: 2, flags 0x200
channels (type chlist):
    A, 16-bit floating-point, sampling 1 1

$ exrmultipart -convert -i fixtures/tiny_tiled_1x1.exr -o /tmp/tiny_mp.exr
ERROR:
Cannot initialize output part "0". Can't build a OutputFile from a type-mismatched part.
$ echo $?
1
```

The same failure occurs for single-part deep input (e.g. the 449-byte
`deep_no_maxsamples.exr` fixture in `../spec/fixtures/`), because `convert()`
also builds a scanline `OutputPart` for the deep part:

```console
$ exrmultipart -convert -i ../spec/fixtures/deep_no_maxsamples.exr -o /tmp/dm.exr
ERROR:
Cannot initialize output part "0". Can't build a OutputFile from a type-mismatched part.
$ echo $?
1
```

For comparison, the scanline path works (this is the documented main use case):

```console
$ exrmultipart -convert -i openexr-images/TestImages/GrayRampsHorizontal.exr \
                          -o /tmp/scan_mp.exr >/dev/null && echo ok
ok
```

## Root cause

`convert()` creates a scanline `InputPart` and a scanline `OutputPart` for every
part, regardless of the header's `type` / `tiles` attribute
(`src/bin/exrmultipart/exrmultipart.cpp`, `main` branch):

```cpp
    MultiPartOutputFile outfile (
        outname, &output_headers[0], output_headers.size ());

    InputPart inpart (infile, 0);            // <-- assumes scanlineimage
    ...
    for (size_t i = 0; i < output_framebuffers.size (); i++)
    {
        OutputPart outpart (outfile, i);     // <-- assumes scanlineimage
        outpart.setFrameBuffer (output_framebuffers[i]);
        outpart.writePixels (dataWindow.max.y + 1 - dataWindow.min.y);
    }
```

`OutputPart` then builds an `OutputFile` from a header whose `type` is
`tiledimage`; that constructor rejects the header with `"Can't build a
OutputFile from a type-mismatched part."` and wraps it as `"Cannot initialize
output part \"0\". …"` (`ImfOutputFile.cpp:755`). Note that the *input* side is
not the problem: `InputPart` wraps `InputFile`, which dispatches on the storage
type and can wrap tiled/deep data. The failure is that the **output** part class
is hard-coded to scanline — and the frame-buffer/`writePixels` loop around it is
scanline-only too, so fixing the class alone is not sufficient.

The two sibling modes already contain the correct dispatch, which is why
`-combine` and `-separate` handle all four part types:

```cpp
    std::string type = headers[p].type ();
    if      (type == SCANLINEIMAGE) copy_scanline     (...);
    else if (type == TILEDIMAGE)    copy_tile         (...);
    else if (type == DEEPSCANLINE)  copy_scanlinedeep (...);
    else if (type == DEEPTILE)      copy_tiledeep     (...);
```

So `convert()` is the odd one out; this looks like an oversight rather than an
intentional limitation.

## Suggested fix

Two options, in increasing effort:

1. **Minimal / honest:** reject non-scanline parts early with an actionable
   message and document the restriction:

   ```cpp
   if (infile.header(0).type() != SCANLINEIMAGE)
       throw invalid_argument(
           "exrmultipart -convert currently supports scanlineimage parts only; "
           "use -separate for tiled/deep files");
   ```

   (Keeping the current `type-mismatched` error is what makes this report
   worth filing: it points at an internal class mismatch instead of the
   limitation.)

2. **Proper fix:** reuse the `-separate` machinery. `-convert` is "split the
   channels of one part into several parts of a multipart file", so it can
   build the output headers as it does today, then copy pixels with
   `copy_scanline`, `copy_tile`, `copy_scanlinedeep` or `copy_tiledeep` based on
   `output_headers[i].type()`, exactly as `separate()` does. The output
   `MultiPartOutputFile` already supports all four part types.

   Note that `convert()` must also keep the per-channel views/proxy-channel
   splitting it currently does for scanline; the pixel copy helper choice is the
   only part-type-dependent change.

## Impact

* Any tiled EXR (including OpenEXR's own `openexr-images/Tiles/*.exr`) and any
  deep single-part file cannot be turned into a multipart EXR with
  `exrmultipart -convert`.
* The error message names an internal class ("OutputFile") rather than the
  unsupported part type, so users cannot tell whether the file is corrupt, the
  input is unsupported, or the tool is broken.

## Environment

* `exrmultipart` from OpenEXR 3.1.11 (system install) reproduces both cases.
* The root-cause code above is from the current `main` checkout in
  `/mnt/nvme02/work/openexr` (`ImfMultiPartOutputFile` part-type dispatch is
  present, `convert()` still uses `InputPart`/`OutputPart` unconditionally), so
  the bug is not yet fixed on `main`.

## Fixture

| File | Purpose |
| --- | --- |
| `fixtures/tiny_tiled_1x1.exr` | 335-byte valid tiled single-part file (1×1, one HALF channel, `flags 0x200`), reproduces the failure without the 4.6 MB `Tiles/Ocean.exr` |
