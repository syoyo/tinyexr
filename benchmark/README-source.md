<!--
Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors
SPDX-License-Identifier: BSD-3-Clause
-->

# Input throughput and memory

Build with `make -B lib THREADS=1`, then `make bench-source THREADS=1` or
`make bench-source-large THREADS=1`. An individual case is
`./build/bench_source WIDTH HEIGHT CHANNELS REPEATS`.

The generated lossless HALF channels contain a deterministic finite pattern.
Every case compares NONE, ZIP, and PIZ with one and four configured workers:

- `memory`: whole-image decoding from an already resident encoded buffer.
- `file`: whole-image decoding through bounded random-access input.
- `blocks`: file input decoded one canonical block at a time, without retaining
  the decoded image. This path deliberately runs sequentially.

CSV reports elapsed milliseconds per image, encoded bytes, and peak tracked
library bytes. Allocation metering runs separately from timing, so its locks
cannot distort throughput. Caller-owned encoded/input planes and stdio's own
internal storage are excluded from the peak; the block path includes its caller
scratch buffer. Timed iterations include allocation, decode, and cleanup, and
use warm filesystem caches. These are throughput comparisons, not storage-device
benchmarks. Temporary files are removed after each codec case.

The measurements below record 1024×1024×4,
2048×2048×4, and 1024×1024×32 on a Ryzen Threadripper 1950X, Linux,
GCC 15.2, `-O2`, runtime SIMD dispatch, libdeflate, and `THREADS=1`.
Timing varies with CPU scheduling and cache locality; byte counts are more stable.

Serial whole-part PIZ source reads reuse a private codec context when the caller
has not supplied one. Completed compressed buffers and per-batch decoded scratch
are reused; they remain bounded by the range slots and batch width. Threaded
input helpers block on a condition variable while the caller reads, rather than
polling. The delayed-source regression checks elapsed versus process CPU time
and confirms that callbacks run only on the caller.

## Measurements (2026-11-04)

Three timed warm-cache iterations per path, after a separately metered warm-up.
Memory and file columns both materialize the full image; block peak includes
one decoded block and codec/range scratch, but retains no complete image.

| Shape (HALF) | Codec | Memory ms | File ms | Block ms | Whole-file peak MiB | Block peak MiB |
|---|---|---:|---:|---:|---:|---:|
| 1024×1024×4 | NONE | 1.882 | 3.632 | 2.550 | 8.03 | 0.03 |
| 1024×1024×4 | ZIP | 4.306 | 4.473 | 3.458 | 8.26 | 0.25 |
| 1024×1024×4 | PIZ | 13.686 | 13.436 | 12.370 | 9.82 | 1.81 |
| 2048×2048×4 | NONE | 25.183 | 29.506 | 6.670 | 32.06 | 0.05 |
| 2048×2048×4 | ZIP | 35.921 | 36.147 | 12.823 | 32.51 | 0.50 |
| 2048×2048×4 | PIZ | 53.804 | 53.911 | 50.211 | 34.33 | 2.32 |
| 1024×1024×32 | NONE | 52.729 | 56.883 | 8.110 | 64.16 | 0.14 |
| 1024×1024×32 | ZIP | 73.384 | 73.694 | 25.472 | 66.03 | 2.02 |
| 1024×1024×32 | PIZ | 136.434 | 135.413 | 102.366 | 69.45 | 5.43 |

All four-worker measurements are emitted by the same commands. On this host,
4-worker PIZ file reads measured 7.97 ms (1024²×4), 22.65 ms (2048²×4), and
70.06 ms (1024²×32). Small NONE blocks do not benefit from file-side parallel
queueing; this sweep is intended to make those costs visible.

### Photographic PIZ repeated loads

`make bench-reload EXR_RELOAD_FIXTURE=<file.exr>` times repeated warm-cache
loads of one file and reports minor page faults per load.
`make bench-reload-ab EXR_RELOAD_FIXTURE=<file.exr>` additionally builds the
`ef203db` baseline in a detached worktree, compiles the same benchmark source
against both libraries, and alternates fresh processes (median of 9 processes,
300 loads each, `THREADS=1`):

| Path | ef203db ms/load | current ms/load | ef203db faults/load | current faults/load |
|---|---:|---:|---:|---:|
| `exr_load_from_file` | 5.784 | 5.310 | 288.7 | 0.0 |
| `exr_load_from_file_ctx` | 5.280 | 5.246 | 0.0 | 0.0 |

The 660×440 photographic PIZ fixture previously cost about 22% more through
bounded source reads, almost all of it page faults. Whole-image loads now
allocate all flat channel planes from one block when the planes total at most
16 MiB (`exr_part.images_block`), so a repeated load hands the allocator a
single large chunk instead of four medium ones. That keeps the working set
resident across loads: measurements went from 735 to 0 minor faults per load
and the median load is now faster than the whole-file `ef203db` loader.
Allocations per load fell from 91 to 88 and peak tracked library bytes are
unchanged apart from 8-byte plane alignment.

Larger images keep per-channel planes: a single block at or above the
allocator's large-allocation cutoff is served by a fresh mapping every time and
re-faults the whole image (2048×2048×4 PIZ measured about 30% slower that way,
1024×1024×4 and 1024×1024×8 were unaffected). Keeping the block bounded avoids
that without touching allocator policy.

No global allocator policy (`mallopt`, `MALLOC_*` tunables) is used and the
bounded 64 KiB input window is unchanged; the improvement is a plain
allocation-layout change. `exr_load_from_file_ctx` with a caller-reused
`exr_context` remains the best option when a caller can keep one alive.
