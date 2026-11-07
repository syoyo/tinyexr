# tptex — portable C11 Ptex

A from-scratch, pure C11 port of [Ptex](https://github.com/wdas/ptex) (Disney),
portability first: no C++, no atomics/threads/`volatile`/`alloca`, no stdio outside
the optional `tptex_file.c`, explicit little-endian parsing (works on big-endian
hosts, which upstream rejects), overflow-checked sizes and hostile-input limits.

Status: half, utils, reader, **writer** done (in-memory, tiles, mips, metadata incl. large); incremental/edit writer, filters, cache pending.

* `include/tptex.h` — types, status, allocator, input, options, texture + metadata API
* `include/tptex_half.h`, `tptex_utils.h` — half conversion (bit-identical to upstream), reduce/average/etc.
* Deflate: vendored `deps/miniz` by default; define `TPTEX_ZLIB_HOOK` and pass `tptex_options.zlib` to use another.
* A texture is not thread-safe (lazy levels/metadata); use one per thread or a lock.
* Tiled faces are assembled whole on read; pixels are identical to upstream.

## Tests
    make ptex-c11-gate         # strict C11 syntax + portability greps
    make ptex-test             # unit tests (ASan+UBSan)
    make ptex-half-exhaustive  # all 2^32 float->half
    make ptex-compare          # opt-in: fetch pinned upstream 2.4.3 and diff half, utils, reader, writer
    TPTEX_SAN=1 make ptex-compare   # same, tptex + harness under ASan/UBSan

`ptex-compare` clones `wdas/ptex` at commit `4aa2c35f9f25f025014fbbbf41cef669881b4172`
(needs a C++ compiler and network once); default builds never do.

## License
BSD-3-Clause; derived portions retain Disney's notice (see `NOTICE`).

## Writer notes
`tptex_write.h` assembles the whole file in memory (no temp files/seeks) and hands it to a sink or returns a
buffer. Compressed bytes differ from upstream's zlib output, but `cmp_write` shows the decoded content,
reductions, face flags (incl. neighbourhood-constant), modes and metadata are identical. Deliberate
differences: a file is always produced (unwritten faces are constant black), and the 8-byte compatibility
barrier is always written so edit blocks appended later are found.
