# texcomp — GPU texture compression for TinyEXR

**[▶ Live browser demo](https://syoyo.github.io/tinyexr/texcomp/)** — resize,
compress, decompress and compare, on your own image, entirely locally.

`texcomp` is a pure-C11 GPU block-compression library that ships alongside
TinyEXR. It exists because the last mile of a VFX/CG asset pipeline is turning
scene-linear EXRs into something a GPU can sample, and that step usually drags in
a pile of C++ dependencies.

It comes with three siblings, all pure C11 and all usable on their own:

| tool | what it does |
|---|---|
| **texcomp** | block compression + decompression: BC1/3/5/6H/7, ETC2, EAC, ASTC (LDR + HDR), and `uni` |
| **tir** | content-aware image resize (`tools/resize`) |
| **texpipe** | mip chains, alpha coverage, seam-free cube LOD, normal/roughness coherence, KTX2 + DDS containers |
| **envmap** | equirect ⇄ cubemap ⇄ octahedral, spherical harmonics, spherical gaussians |

No C++, no exceptions, no RTTI, no `<stdio.h>` in the library sources. The
optional [astcenc](https://github.com/ARM-software/astc-encoder) backend is the
one exception, and it is opt-in.

---

## Codecs

| codec | bpp | channels | target |
|---|---|---|---|
| BC1 | 4 | RGB | desktop, colour |
| BC3 | 8 | RGBA | desktop, colour + alpha |
| BC5 | 8 | RG | desktop, **normal maps** (UNORM and SNORM) |
| BC6H | 8 | RGB **HDR** | desktop, HDR / IBL (uf16 + sf16) |
| BC7 | 8 | RGBA | desktop, best LDR quality |
| ETC2 RGB / RGBA | 4 / 8 | RGB / RGBA | mobile |
| EAC R11 / RG11 | 4 / 8 | R / RG | mobile, masks and normal maps |
| ASTC | 0.9–8 | RGBA | mobile + desktop, variable block size |
| ASTC HDR | 8 | RGB **HDR** | mobile HDR |
| `uni` | 8 | RGBA | private ASTC-backed intermediate: encode once, convert per device |

`uni` is a texcomp-native carrier. Encode once, then convert on load to the
device format — BC7 on desktop, ASTC or ETC2 on mobile. ASTC 4×4 is a byte copy
because the stored blocks are valid ASTC; BC7, BC1 and ETC2 use decode/re-encode
conversion. It is not the Basis UASTC representation.

## Containers

`texpipe` writes **KTX2** (Vulkan `VkFormat`) and **DDS** (DX10 header), with mip
chains, cubemaps (`faceCount = 6`) and array textures (`layerCount`). It also
*reads* KTX2 back — including Zstd supercompression — and decodes or transcodes
any codec it can write:

```c
tp_ktx2_image img;
tp_ktx2_read(bytes, len, &img);            /* zero-copy parse            */
tp_ktx2_decode_level_rgba8(&img, 0, rgba, n);   /* LDR → RGBA8           */
tp_ktx2_decode_level_rgbaf(&img, 0, rgbaf, n);  /* BC6H / ASTC HDR → float */
```

## Every decoder is validated against an independent implementation

This is the part worth trusting, and it was not free. A round-trip test cannot
tell you a codec is correct: if the encoder and decoder share a wrong assumption
they agree with each other perfectly, and if the encoder never emits a shape,
nothing ever decodes it. So each decoder is cross-checked against an
implementation from *outside* this tree:

| decoder | oracle | coverage |
|---|---|---|
| BC1 / BC3 / BC5 | in-file S3TC reference | all modes, partial edge blocks |
| BC6H | bcdec port | all 14 modes, uf16 + sf16 |
| BC7 | upstream [bcdec](https://github.com/iOrange/bcdec) | 320k random blocks, all 8 modes |
| ETC2 / EAC | [Mesa](https://gitlab.freedesktop.org/mesa/mesa) | 200k random blocks, all 5 RGB modes |
| ASTC LDR | [astcenc](https://github.com/ARM-software/astc-encoder) | 4480 astcenc-encoded blocks, bit-exact |
| ASTC HDR | astcenc | 2240 encoded + 1856 mutated-CEM + 64 void-extent, bit-exact |

Doing this found **eight real bugs** that every round-trip test had happily
passed — including transposed ETC2/EAC blocks (every ETC2 texture the tool had
ever written would have displayed wrong on a GPU), an ETC2 differential mode that
packed its base and delta at overlapping bit positions, an ASTC HDR path whose
endpoints overlapped its own weight data, and an ASTC LDR interpolation model
that was off by 1 LSB from what hardware actually does.

The same trick works on encoders: hold a codec to a *rival's* quality on
identical content. ETC2 sat 22 dB behind BC1 for as long as nothing decoded it.

---

## Quick start

```sh
make texcomp                        # CLI + static lib
build/texcomp/texcomp --help
```

```c
#include "texcomp.h"

tc_bc7_options opt;
tc_bc7_options_init(&opt);
opt.quality = TC_BC7_QUALITY_MEDIUM;

size_t n = tc_bc7_compressed_size(w, h);
uint8_t *blocks = malloc(n);
tc_bc7_compress_rgba8(rgba, w, h, w * 4, &opt, blocks, n);

/* and back — the same decoder the KTX2 reader uses */
tc_bc7_decompress_rgba8(blocks, w, h, w * 4, out_rgba, w * h * 4);
```

For real-time encoding, use `TC_BC7_QUALITY_SPEED` (or
`--bc7-quality speed` in the CLI). This selects a mode-6-only projection path,
skips endpoint refinement and RDO, and is intended to favor throughput over
the higher quality of the default mode search.

For maximum throughput, `TC_BC7_QUALITY_FASTEST` / `--bc7-quality fastest`
uses a cheaper normalized selector estimate on opaque blocks.

The full pipeline (resize → mips → compress → container) is one call:

```c
#include "texpipe.h"

tp_options opt;
tp_options_init(&opt, TP_CONTENT_COLOR, TP_CODEC_BC7);
opt.container = TP_CONTAINER_KTX2;
opt.srgb_aware = 1;

uint8_t *ktx2; size_t n;
tp_process(NULL, &view, 1, &opt, &ktx2, &n);
```

---

## The CG/VFX cases the demo covers

**HDR / IBL.** An 8-bit codec clips everything above 1.0 at encode time — the
data is gone, not merely quantised. BC6H and ASTC HDR store half-float endpoints.
Load a scene-linear EXR in the demo, compress it with BC7 and then BC6H, and
raise the exposure: the highlights BC6H still holds are flat white in BC7.

**Normal maps: PSNR lies.** What matters is the *angle* of the reconstructed
normal, not the error in the raw channels. BC5 keeps only X and Y, each with its
own endpoints, and the shader rebuilds Z = √(1 − x² − y²). BC7 spends bits on a
blue channel that carries no information and shares endpoints across channels, so
it is usually **worse** on normals despite being the "better" codec. The demo
reports mean angular error in degrees and ranks the codecs; BC5 wins, and
EAC_RG11 is its mobile equivalent.

texpipe also bakes **Toksvig roughness** while it builds normal-map mips: a mip
that averages a bumpy surface flat should get *rougher*, not smoother, or the
specular highlight aliases in the distance.

**Cubemaps and octahedral maps.** `envmap` reprojects an equirect latlong EXR to
a cubemap or an octahedral map. texpipe does **seam-free cubemap LOD** — filtering
across face borders so the mips do not crack at the edges — and an equivalent
fold-seam fixup for octahedral maps. Octahedral packing wastes no texels on cube
seams, which is why it keeps showing up in modern renderers.

**Alpha-tested foliage.** Minifying an alpha-tested texture thins it out: fewer
texels survive the alpha test at each level and the leaves evaporate with
distance. texpipe rescales alpha per level so the coverage fraction stays put
(Castaño's method).

**Packed material maps (ORM).** Each channel of a packed map wants a different
downsample rule — a binary metallic mask should threshold, not average to grey;
roughness should account for the variance it is throwing away. `tp_channel_op`
sets the rule per channel.

**sRGB-aware resize.** Filtering directly in sRGB darkens what it averages: a
black/white checker minifies to ~0.5 sRGB (0.21 linear) instead of 0.5 linear
(~0.74 sRGB). `opt.srgb_aware` decodes to linear, filters, and re-encodes.

---

## Running the demo locally

```sh
cd web/texcomp
./build.sh            # needs emcc on PATH; SIMD=1 for -msimd128
python3 -m http.server
# open http://localhost:8000/web/texcomp/  (serve from the repo root)
```

The demo links the EXR decoder, tir, texcomp, texpipe and envmap into one ~600 KB
wasm module. Nothing is uploaded: every byte stays in the tab.

---

## Testing

```sh
make tools-test        # pure-C gates: texcomp, tir, texpipe, envmap
make tools-test-all    # + the astcenc C++ conformance cross-checks
make texpipe-three-ktx2-test  # optional Three.js KTX2 browser interop
```

`tools-test-all` runs the foreign-block sweeps described above, so a decoder that
drifts from astcenc, Mesa or bcdec fails the build.
The standalone browser gate needs Node, Three.js, Puppeteer and Chrome; setup
and dependency-reuse instructions are in
`tools/texpipe/test/three_ktx2_loader/README.md`.

## Status and known gaps

- ASTC LDR quality trails astcenc-medium by 1.7–4.2 dB on real photography; see
  `tools/texcomp/ASTC_PORT_NOTES.md`.
- BasisLZ (KTX2 `supercompressionScheme = 1`) is not implemented, and will not be
  until it can be validated against Basis's own transcoder.
- Raw `uni` blocks are valid ASTC 4×4 blocks but are not the Basis UASTC wire
  representation. The default KTX2 wrapper is therefore a TinyEXR-private
  carrier and must be read by texpipe. Pass `TP_UNI_ASTC_KTX2` to the raw or
  scheme-2 writer for a standards-defined ASTC KTX2 that interoperates with
  external consumers such as Three.js `KTX2Loader`. The texcomp-native
  `--basis` codebook is separate from BasisLZ and does not change the scheme-1
  limitation.
