#!/usr/bin/env python3
# Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
# SPDX-License-Identifier: BSD-3-Clause
"""Write a minimal 1x1 single-part deep-scanline EXR with no maxSamplesPerPixel.

The OpenEXR file-layout document calls maxSamplesPerPixel "Required for deep
data (deepscanline and deeptile) parts", yet the reference implementation never
looks at it and OpenEXR's own deep test images omit it. This file reproduces
that contradiction in 449 bytes.

Usage: python3 gen_deep_no_maxsamples.py [out.exr]
"""
import struct
import sys


def attr(name, typ, value):
    return name.encode() + b"\0" + typ.encode() + b"\0" + struct.pack("<I", len(value)) + value


def cstr(s):
    return s.encode() + b"\0"


def channel(name, pixel_type):
    # name, pixelType(i32), pLinear(u8), 3 reserved bytes, xSampling, ySampling
    return cstr(name) + struct.pack("<I", pixel_type) + b"\0\0\0\0" + struct.pack("<ii", 1, 1)


# HALF A, HALF Y, FLOAT Z (names must be sorted); chlist ends with a 0 byte.
chlist = channel("A", 1) + channel("Y", 1) + channel("Z", 2) + b"\0"
box = struct.pack("<iiii", 0, 0, 0, 0)          # dataWindow/displayWindow = (0,0)-(0,0)

attrs = b"".join([
    attr("channels", "chlist", chlist),
    attr("compression", "compression", b"\0"),           # NO_COMPRESSION
    attr("dataWindow", "box2i", box),
    attr("displayWindow", "box2i", box),
    attr("lineOrder", "lineOrder", b"\0"),               # INCREASING_Y
    attr("pixelAspectRatio", "float", struct.pack("<f", 1.0)),
    attr("screenWindowCenter", "v2f", struct.pack("<ff", 0.0, 0.0)),
    attr("screenWindowWidth", "float", struct.pack("<f", 1.0)),
    attr("type", "string", b"deepscanline"),
    attr("version", "int", struct.pack("<i", 1)),
    attr("chunkCount", "int", struct.pack("<i", 1)),
    attr("name", "string", b"a"),
    # NOTE: maxSamplesPerPixel intentionally absent.
])

header = struct.pack("<II", 0x01312F76, 2 | 0x800) + attrs + b"\0"  # version 2, deep bit
data_off = len(header) + 8                                         # one u64 offset entry

# Deep scan-line chunk: y, packed offset-table size, packed sample size,
# unpacked sample size, then the (uncompressed) sample-count table and samples.
samples = struct.pack("<HH", 0x3C00, 0x3C00) + struct.pack("<f", 1.0)   # A, Y, Z
chunk = (struct.pack("<i", 0)
         + struct.pack("<QQQ", 4, len(samples), len(samples))
         + struct.pack("<I", 1)     # cumulative sample count per pixel: 1
         + samples)

out = sys.argv[1] if len(sys.argv) > 1 else "deep_no_maxsamples.exr"
with open(out, "wb") as f:
    f.write(header + struct.pack("<Q", data_off) + chunk)
print("wrote %s (%d bytes)" % (out, len(header) + 8 + len(chunk)))
