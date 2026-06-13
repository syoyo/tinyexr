# TinyEXR vs OpenEXR — performance

How the pure-C11 TinyEXR v3 codec stacks up against the reference **OpenEXR**
library, codec by codec, for encode and decode — single-threaded and
multi-threaded.

> **Setup & method**
> - **CPU:** AMD Ryzen 9 3950X (16C/32T, Zen2), `avx2+f16c`. Machine idle.
> - **Image:** `asakusa.exr`, 660×440, 4× HALF. (Small — see the caveat in
>   [Multi-threading](#multi-threading) about chunk-count-limited scaling.)
> - **I/O:** fully in memory (`StdOSStream`/`StdISStream` on the OpenEXR side);
>   each library loads the same source independently. OpenEXR 4.0-dev, `gcc -O3`.
> - Throughput is **megapixels/second** (higher is better); sizes are the
>   compressed payload. Numbers vary a few % run-to-run.
> - Both libraries are pinned to the same thread count
>   (`Imf::setGlobalThreadCount(n)` / `exr_set_num_threads(n)`).

## TL;DR

- **Single-thread decode:** TinyEXR wins big on the cheap codecs — **3.4×** on
  uncompressed and **2.5×** on RLE. On the DEFLATE family / PIZ, OpenEXR leads
  (≈1.2× ZIP, ≈1.8× PXR24, ≈2–2.7× ZIPS/PIZ) because of its **libdeflate**
  backend and tuned PIZ. HTJ2K is now closer: TinyEXR is ~77% of the latest
  same-machine OpenJPH baseline (≈1.30× decode gap).
- **Single-thread encode:** TinyEXR ties or wins on RLE/PIZ/B44; OpenEXR is
  ≈1.5× on ZIP/ZIPS, ≈1.8× on PXR24, and ≈3× on HTJ2K.
- **libdeflate (opt-in):** with the same backend, TinyEXR **matches or beats**
  OpenEXR on the deflate family — e.g. **ZIP decode 1.4×** single-thread.
- **Multi-threaded:** TinyEXR's opt-in parallel path scales ~5–9× to 16 threads;
  at 16T it **out-decodes OpenEXR on RLE/ZIP/ZIPS/B44** (in-tree), and with
  libdeflate it leads the whole deflate family by a wide margin.

## Single thread

### Decode

![Decode throughput, single thread](perf-decode.svg)

`none` (uncompressed) is off the chart on purpose: **TinyEXR 2699 vs OpenEXR
789 MP/s** (~3.4×) — no thread-pool or framebuffer-copy overhead. TinyEXR also
leads **RLE** (230 vs 93, ~2.5×). On the compressed codecs OpenEXR is ahead —
ZIP ~1.2×, PXR24 ~1.8×, ZIPS ~2.1×, PIZ ~2.7×, and HTJ2K ~1.30× — dominated by
its libdeflate inflate (and tuned PIZ/JPH). A TinyEXR ZIP-decode profile is
~95 % inflate; the predictor and de-interleave passes are already vectorized.

### Encode

![Encode throughput, single thread](perf-encode.svg)

TinyEXR ties or beats OpenEXR on **RLE / PIZ / B44**. On **ZIP/ZIPS** it is ~1.5×
behind and **PXR24** ~1.8× — its in-tree, dependency-free LZ77 encoder is fast
but not libdeflate-level. **HTJ2K** encode is the widest gap (~3×: the separate
JPH/OpenJPH encoder). TinyEXR's HTJ2K paths recently gained an AVX2 forward 5/3
wavelet, an unstuffed-buffer entropy reader, and a `clz`-builtin fast path in the
per-sample prepare (encode +~39%, decode +~18% vs the pre-SIMD baseline). The
decode path then restructured the inverse 5/3 **column** pass into a
column-parallel, gather/scatter-free AVX2 vertical lifting (mirroring OpenJPH —
columns are the natural SIMD axis), and vectorized the sign-magnitude → signed
coefficient extraction; together these cut decode wavelet+extraction time
materially (~16% faster all-HALF decode on the dev box). The same
column-parallel restructuring was then applied to the **forward** 5/3 (encode,
byte-identical output, ~7% faster htj2k256 encode) and to the **int64** inverse
5/3 used for float/32-bit channels (AVX2 1D + vertical, ~18% faster float
decode). The cleanup-pass entropy decoder was then moved to an OpenJPH-style
rolling forward MagSgn reader, with AVX2 cleanup kernels for the common 16/32-bit
HT block paths; decode workspace reuse removed repeated scratch allocation; and
the all-HALF inverse 5/3 postprocess gained a bounded AVX2 vertical pass. On
this Zen2 machine, current `make bench` reports HTJ2K256 decode at **45.2 MP/s**
and HTJ2K32 decode at **43.1 MP/s**; the latest available same-machine OpenJPH
baseline is **58.8 / 56.2 MP/s**, so TinyEXR is ~77% of OpenJPH throughput
(~1.30× gap). The remaining gap is mostly entropy/block decode latency.

### Compression size

Sizes are essentially identical for the lossless/standard codecs — the formats
are interoperable (a TinyEXR file decodes in OpenEXR and vice-versa). Only ZIP
and HTJ2K differ, from encoder *tuning* (not format):

| codec | TinyEXR KB | OpenEXR KB | | codec | TinyEXR KB | OpenEXR KB |
|---|--:|--:|---|---|--:|--:|
| none | 2276 | 2276 | | pxr24 | 1158 | 1163 |
| rle  | 1644 | 1644 | | b44   |  993 |  993 |
| zips | 1205 | 1212 | | htj2k256 | 1132 | 1016 |
| zip  | 1155 | 1070 | | htj2k32  | 1160 | 1042 |
| piz  |  742 |  742 | | | | |

### Optional: the libdeflate backend

OpenEXR's deflate speed comes from libdeflate. TinyEXR vendors **libdeflate 1.25**
(MIT) as an **optional, off-by-default** backend for ZIP/ZIPS/PXR24 (the in-tree
codec stays the default and the only freestanding path):

```sh
make bench-compare LIBDEFLATE=1     # -DEXR_USE_LIBDEFLATE, level 4 (= OpenEXR)
```

![Decode with libdeflate backend, single thread](perf-libdeflate-decode.svg)

Same backend ⇒ byte-identical sizes, and TinyEXR **meets or beats** OpenEXR:
**ZIP decode 80.8 vs 58.8 MP/s (1.37×)**, ZIPS 61.4 vs 46.4 (1.32×), PXR24 at
parity. Encode reaches parity too (ZIP 15.3 vs 14.0, PXR24 16.4 vs 15.8). Both
call libdeflate's inflate; TinyEXR's edge is its SSE2/AVX2 predictor and lower
per-block overhead.

The two charts below put **libdeflate on/off vs OpenEXR** side by side across the
deflate family **and HTJ2K** (which has no deflate path, so only the in-tree and
OpenEXR bars apply). The in-tree TinyEXR bars are the freestanding default; the
green bars are the same `-DEXR_USE_LIBDEFLATE` build:

![Decode: tinyexr libdeflate on/off vs OpenEXR, incl. htj2k](perf-libdeflate-htj2k-decode.png)

![Encode: tinyexr libdeflate on/off vs OpenEXR, incl. htj2k](perf-libdeflate-htj2k-encode.png)

On decode, libdeflate flips the deflate family in TinyEXR's favour (ZIP/ZIPS) and
brings PXR24 to parity; HTJ2K stays OpenEXR's (its tuned JPH decoder). On encode,
libdeflate lifts the deflate family to parity-or-better, while OpenEXR keeps a
wide HTJ2K lead from its SIMD JPH entropy encoder.

### Full single-thread numbers

In-tree default:

| codec | tx enc | exr enc | tx dec | exr dec |
|-------|-------:|--------:|-------:|--------:|
| none  | 102.3 | 85.3 | 2699 | 789 |
| rle   | 55.1 | 46.3 | 230  | 92.6 |
| zips  | 10.3 | 15.5 | 23.2 | 48.9 |
| zip   | 9.6  | 14.7 | 50.4 | 61.9 |
| piz   | 23.6 | 25.4 | 24.6 | 67.5 |
| pxr24 | 9.2  | 16.4 | 48.0 | 88.0 |
| b44   | 31.7 | 34.8 | 145  | 178 |
| htj2k256 | 13.9 | 33.2* | 45.2 | 58.8* |
| htj2k32  | 16.6 | 31.6* | 43.1 | 56.2* |

`*` HTJ2K OpenEXR/OpenJPH values are the latest available same-machine baseline;
that OpenJPH build has the default x86 SIMD path enabled and selects its AVX2
codeblock decoder on this CPU. The TinyEXR HTJ2K values above were re-measured
on 2026-06-13 with `make bench`.

`LIBDEFLATE=1` (deflate family): zip 15.3/14.0/80.8/58.8, zips 16.2/14.8/61.4/46.4,
pxr24 16.4/15.8/83.6/83.8 (tx enc / exr enc / tx dec / exr dec).

## Multi-threading

TinyEXR supports **per-block parallel encode and decode** via portable C11
`<threads.h>` (or **Grand Central Dispatch** on Apple platforms, which do not
ship `<threads.h>`) and a small ephemeral worker pool. It is **opt-in** (build
`THREADS=1` / `-DEXR_USE_THREADS`; default and freestanding builds stay
single-threaded); the count is set at runtime:

```c
exr_set_num_threads(16);   /* 0/1 = serial (default) */
```

It covers scanline and single-level tiled parts, the deep scanline/tiled
encode and decode paths, and mipmap/ripmap level generation (the box downsample
is row-parallel) on the in-memory load/save paths; the streaming APIs remain
single-threaded. Encode stays byte-deterministic and decode bit-identical
regardless of thread count (unit-tested, ThreadSanitizer-clean).

### Scaling

![TinyEXR decode scaling by thread count](perf-mt-scaling.svg)

TinyEXR decode scales **~5× (ZIP, 28 blocks)** to **~8.8× (ZIPS, 440 blocks)** at
16 threads. Scaling is bounded by the number of chunks: `asakusa.exr` is small,
so ZIP (16 lines/block ⇒ 28 blocks) saturates earlier than ZIPS (1 line/block ⇒
440 blocks). Larger images would scale further. (`none` decode does *not* benefit
— it is memory-bound with no per-block work, so thread overhead dominates.)

### TinyEXR vs OpenEXR at 16 threads

![Decode throughput at 16 threads](perf-mt-compare.svg)

Both libraries at `EXR_THREADS=16`, in-tree TinyEXR build. TinyEXR out-decodes
OpenEXR on **RLE (456 vs 150), ZIP (251 vs 226), ZIPS (204 vs 174), B44 (362 vs
319)**; OpenEXR still leads **PIZ (208 vs 110)** and edges **PXR24 (270 vs 242)**.

With **`LIBDEFLATE=1` at 16 threads** TinyEXR leads the deflate family decisively:

| codec | tx dec | exr dec | | tx enc | exr enc |
|-------|-------:|--------:|---|-------:|--------:|
| zip   | **339.6** | 226.6 | | **102.3** | 88.0 |
| zips  | **358.5** | 151.1 | | **153.1** | 82.2 |
| pxr24 | **341.7** | 285.0 | | **105.7** | 96.9 |

(MP/s. OpenEXR's own per-block scaling is included — this is a like-for-like
16-thread comparison.)

Reproduce:

```sh
make bench-compare THREADS=1                         # single thread (default)
EXR_THREADS=16 ./build/bench_compare                 # 16 threads, both libs
make bench-compare THREADS=1 LIBDEFLATE=1            # + libdeflate backend
```

## ARM64 / NEON (Apple Silicon)

The same comparison on **Apple M1** (4 P-core + 4 E-core, macOS 26, Apple
clang 21), `asakusa.exr`. TinyEXR's codec auto-dispatches to **NEON**; threading
uses **Grand Central Dispatch** (Apple ships no `<threads.h>`). OpenEXR 4.0-dev
built from source for arm64 (vendored libdeflate, external OpenJPH 0.27 for
HTJ2K). The NEON micro-kernel speedups (de-interleave 7.6×, half↔float 5.8×, JPH
NLT 8.2×, predictor 1.9×) and the full HTJ2K kernel list are in
[`benchmark/README.md`](../benchmark/README.md#arm64--neon-results-make-bench).

### Single thread

| codec | tx enc | exr enc | tx dec | exr dec |
|-------|-------:|--------:|-------:|--------:|
| none  | 1080 | 423  | **2456** | 859 |
| rle   | 65.2 | 58.3 | **163**  | 89.3 |
| zips  | 12.5 | 17.0 | 22.2 | 60.6 |
| zip   | 11.5 | 16.4 | 42.6 | 80.2 |
| piz   | 26.4 | 25.9 | 28.2 | 66.1 |
| pxr24 | 10.8 | 20.1 | 43.7 | 82.0 |
| b44   | 46.6 | 68.6 | **318** | 217 |
| htj2k256 | 18.3 | 21.6 | 28.5 | 30.3 |
| htj2k32  | 17.8 | 20.9 | 26.7 | 29.4 |

Same shape as x64: TinyEXR wins the cheap codecs (**none ~2.9×**, **rle ~1.8×**,
**b44 dec ~1.5×**); OpenEXR leads the DEFLATE family / PIZ via its libdeflate
inflate and tuned PIZ. With **`LIBDEFLATE=1`** the deflate family comes to
near-parity (zip 72.3 vs 80.2, zips 57.4 vs 60.8, **pxr24 83.1 vs 82.0**; tx enc /
exr enc / tx dec / exr dec).

**HTJ2K is near parity on ARM.** With the NEON reversible-5/3 wavelet, NLT,
sign-magnitude extraction and pack kernels, htj2k256 **decode reaches 28.5 vs
30.3 MP/s (~94%)** and htj2k32 26.7 vs 29.4; encode is 18.3 vs 21.6 (~85%). The
residual gap is **not** SIMD — OpenJPH ships AVX2/AVX-512/SSSE3 block coders but
**no NEON** entropy coder, so on ARM *both* libraries run their scalar cleanup-pass
entropy coder (VLC/MEL + MagSgn), which dominates both profiles once the transform
is vectorized. OpenJPH's scalar entropy coder is a little more tuned; SIMD does not
help here (the decode-side attempts are written up in
[`doc/htj2k-entropy-simd-scope.md`](htj2k-entropy-simd-scope.md), and NEON's
128-bit vectors are narrower still). On x64, by contrast, OpenEXR's AVX2 JPH coder
makes the encode gap ~3×; ARM closes most of it.

### Multi-threaded (8 threads, in-tree)

| codec | tx enc | exr enc | tx dec | exr dec |
|-------|-------:|--------:|-------:|--------:|
| none  | 928  | 212  | **2391** | 160 |
| rle   | 276  | 127  | **684**  | 139 |
| zips  | 61.4 | 60.7 | 109  | 128 |
| zip   | 47.9 | 75.4 | 174  | **328** |
| piz   | 88.7 | 106  | 96.2 | 258 |
| pxr24 | 45.0 | 90.8 | 181  | **334** |
| b44   | 160  | 254  | **796** | 701 |
| htj2k256 | 18.2 | 35.7 | 28.4 | 50.3 |
| htj2k32  | 58.6 | 86.1 | 83.1 | 116 |

TinyEXR decode scales **~4×** to 8 threads (rle 163→684, zip 42→174, b44
318→796) and out-decodes OpenEXR on **none / rle / zips / b44**. OpenEXR's
libdeflate inflate scales harder, so it leads **zip / pxr24 / piz** decode at 8
threads in-tree. With **`LIBDEFLATE=1` at 8 threads** TinyEXR leads **zips
(272 vs 124)** and reaches parity on **zip (298 vs 321)** and **pxr24 (329 vs
324)** decode. (HTJ2K256 decode stays flat — at 256 lines/block `asakusa.exr` has
too few chunks to parallelize; HTJ2K32 scales to ~75 MP/s. The JPH codec itself is
scalar on ARM — no NEON entropy/wavelet kernels yet.)

The deep (scanline + tiled, encode + decode) and mipmap/ripmap paths are now
threaded. Still future work: optimize the scalar HTJ2K entropy coder (the
remaining encode/decode gap on ARM, where neither library has a NEON entropy
path); thread the streaming APIs; sweep larger images and channel counts.

---

*Charts: `doc/perf-decode.svg`, `perf-encode.svg`, `perf-libdeflate-decode.svg`,
`perf-libdeflate-htj2k-decode.png`, `perf-libdeflate-htj2k-encode.png`,
`perf-mt-scaling.svg`, `perf-mt-compare.svg`. Harness:
`benchmark/bench_compare.cpp` (`make bench-compare [THREADS=1] [LIBDEFLATE=1]`).*
