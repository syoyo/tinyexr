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

### Photographic PIZ comparison still under investigation

For the original 660×440 photographic PIZ fixture, three fresh-process trials
of 300 serial loads measured a median 5.546 ms with the pre-streaming
`ef203db` library and 6.787 ms with bounded source reads (about 22% overhead,
down from the earlier roughly 34%). Both builds use the same compiler/flags.
A separate `perf stat` pass recorded 222,834 versus 91,431 page faults,
1.512 versus 1.436 seconds of user CPU, and 0.524 versus 0.219 seconds of system
CPU for the two 300-load runs. Allocation/page reuse is the remaining focus;
the generic larger-image sweeps above have near-equal serial memory/file PIZ
throughput. Global allocator policy has not been changed to influence results.
