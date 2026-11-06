# `maxSamplesPerPixel` is documented as *required* for deep parts, but is unused and absent from OpenEXR's own deep images

- **Component:** file format specification (`website/OpenEXRFileLayout.rst`, "Deep Data Header Attributes")
- **Severity:** low for readers (they tolerate it), medium for conformance/interop (a literal reader must reject shipped files)
- **Found by:** the Lean 4 model of the format (`lean/Exr/File.lean`) + the differential harness (`test/v3/lean_diff.py`)

## Summary

The file-layout document marks `maxSamplesPerPixel` as **required** for every
deep-scanline and deep-tile part:

> | `maxSamplesPerPixel` | `int` | **Required for deep data (deepscanline and deeptile) parts.** *Note: Since the value of `maxSamplesPerPixel` maybe be unknown at the time of opening the file, the value "-1" is written to the file to indicate an unknown value.* […] |
> — `website/OpenEXRFileLayout.rst`, *Deep Data Header Attributes*

The reference implementation contradicts this in three ways:

1. **It is not validated.** OpenEXRCore's required-attribute checker never
   looks at it. The constant is deliberately commented out in
   `src/lib/OpenEXRCore/internal_constants.h`:

   ```c
   #define EXR_REQ_CHUNK_COUNT_STR "chunkCount"
   /* this is in the file layout / technical info document
    * but not actually used anywhere...
    * #define REQ_MSS_COUNT_STR "maxSamplesPerPixel"
    */
   ```

   `grep -rn maxSamplesPerPixel src/` finds only that comment and a struct
   field (`exr_attribute_t* maxSamplesPerPixel`); no code reads the value.

2. **It is not used.** Nothing pre-allocates or bounds per-pixel sample counts
   from it, so the "-1 = unknown" escape hatch is the only state the library
   ever effectively sees.

3. **OpenEXR's own deep test images omit it.** 12 files under
   `openexr-images/v2/` are deep-scanline files whose headers have no
   `maxSamplesPerPixel` (see list below), and `exrheader` — i.e. OpenEXR's
   header reader/validator — accepts every one of them. The fixture below shows
   the same for a full deep decode (sample counts and sample values).

A reader that implements the specification literally must reject those files.
That is what the Lean model did, which is how this discrepancy surfaced.

## Reproduction

The attached fixture is a 449-byte, 3-channel, 1×1 single-part deep-scanline
file with `name`, `version` and `chunkCount`, and **no**
`maxSamplesPerPixel`:

Run from `issues/spec/fixtures/`:

```console
$ python3 gen_deep_no_maxsamples.py deep_no_maxsamples.exr
wrote deep_no_maxsamples.exr (449 bytes)

$ exrheader deep_no_maxsamples.exr | grep -E 'flags|type|version|maxSamples'
file format version: 2, flags 0x800
type (type string): "deepscanline"
version (type int): 1
# <- no maxSamplesPerPixel

$ g++ -std=c++17 read_deep.cpp $(pkg-config --cflags --libs OpenEXR) -o read_deep
$ ./read_deep deep_no_maxsamples.exr
read 1x1 deep pixels, sampleCount[0,0]=1, A=1.0000 Y=1.0000 Z=1.0000
```

So OpenEXR 3.1.11 fully decodes the deep chunk — sample counts **and** sample
values — of a file that the specification says is invalid.

The same holds for the shipped corpus (run from the `openexr-images` checkout):

```console
$ python3 - <<'EOF'
# print deep files (version bit 11) with no maxSamplesPerPixel attribute
import glob, struct, os
def names(path):
    d = open(path, "rb").read()
    if d[:4] != b"v/1\x01": return None, None
    ver = struct.unpack("<I", d[4:8])[0]; i = 8; out = []
    while d[i] != 0:
        j = d.index(b"\0", i); out.append(d[i:j].decode()); i = j + 1
        j = d.index(b"\0", i); i = j + 1
        i += 4 + struct.unpack("<I", d[i:i+4])[0]
    return ver, out
for p in sorted(glob.glob("openexr-images/**/*.exr", recursive=True)):
    ver, ns = names(p)
    if ver and (ver & 0x800) and "maxSamplesPerPixel" not in ns:
        print(os.path.relpath(p, "openexr-images"))
EOF
v2/LeftView/Balls.exr
v2/LeftView/Ground.exr
v2/LeftView/Leaves.exr
v2/LeftView/Trunks.exr
v2/LowResLeftView/Balls.exr
v2/LowResLeftView/Ground.exr
v2/LowResLeftView/Leaves.exr
v2/LowResLeftView/Trunks.exr
v2/Stereo/Balls.exr
v2/Stereo/Ground.exr
v2/Stereo/Leaves.exr
v2/Stereo/Trunks.exr
```

## How the formalization found it

`lean/Exr/File.lean` encodes the header-requirement table as a list of boolean
checks. The deep-part check was first taken literally:

```lean
if h.isDeep then h.maxSamplesPerPixel.isSome else true
```

`exrcheck` therefore rejected all 12 shipped deep images, while the C reader
accepted them; the differential harness (`lean_diff.py`) reported the
disagreement. Investigating showed the implementation comment quoted above,
i.e. the table row is stale. The check was then relaxed to `true`, with the
reason recorded inline:

```lean
    -- `maxSamplesPerPixel` is required by the spec text for deep parts, but
    -- OpenEXR's library (which the spec declares authoritative) reads deep
    -- files that omit it, treating the value as unknown (-1). We follow the
    -- library: absence is accepted, and `maxSamplesUnknown` reports the
    -- `-1` convention when present.
    true ]
```

and in `lean/README.md`. The value, if present, is still range-checked
(`m >= -1`).

## Proposed resolution

Pick one and state it normatively:

**Option A (matches the implementation; preferred).** Make the attribute
optional and define the absence semantics:

> `maxSamplesPerPixel` (`int`, *optional* for deep parts). If present, it is an
> upper bound on the number of samples in any one pixel; the value `-1` means
> "unknown when the file was written". If absent, the value is unknown
> (equivalent to `-1`). Readers must derive the actual counts from the deep
> chunk sample tables and must not assume the attribute is present.

**Option B (matches the document).** Keep it required, and
(a) fix OpenEXR's required-attribute validation to reject files without it,
(b) re-write the 12 shipped deep images, and (c) bump the format or document
the strictness change — clearly much more disruptive.

Option A is the only pragmatic choice; OpenEXR's own source already says the
attribute is "not actually used anywhere".

## Related (secondary) spec gap

The same formalization pass hit a second undocumented rule: for multi-part
files, OpenEXRCore *rejects* parts whose `displayWindow`, `pixelAspectRatio`,
`timecode` or `chromaticities` differ from part 0
(`internal_exr_validate_shared_attrs`, called from `parse_header.c`), and the
C++ writer silently overwrites those values
(`MultiPartOutputFile::Data::overrideSharedAttributesValues`). Neither
`OpenEXRFileLayout.rst` nor `TechnicalIntroduction.rst` mentions shared
attributes at all. That requirement should be stated in the "Multi-Part Files"
section (including whether writers must copy or may reject). This one is a
plain omission rather than a contradiction, so it is filed here only as a
note.

## Fixtures

| File | Purpose |
| --- | --- |
| `fixtures/gen_deep_no_maxsamples.py` | deterministic writer for the 449-byte fixture (no dependencies) |
| `fixtures/deep_no_maxsamples.exr` | the fixture itself |
| `fixtures/read_deep.cpp` | OpenEXR C++ reader used above (reads sample counts and the A/Y/Z sample values) |

## Environment

* OpenEXR 3.1.11 (system library) for the runtime check; master
  (`/mnt/nvme02/work/openexr`) inspected for the validation code and the
  commented-out constant.
* Lean 4.35.0 model in `lean/` (`make lean-check`, `make lean-diff`).
