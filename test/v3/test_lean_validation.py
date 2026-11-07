#!/usr/bin/env python3
# Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
# SPDX-License-Identifier: BSD-3-Clause
"""Regression checks for differential-gate infrastructure failures."""
import copy
import importlib.util
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("lean_diff", ROOT / "test/v3/lean_diff.py")
diff = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diff)


class ValidationTests(unittest.TestCase):
    def test_crashed_oracles_fail(self):
        result = subprocess.CompletedProcess([], -11, "", "crashed")
        with patch.object(diff, "run", return_value=result):
            self.assertTrue(diff.compare("example.exr"))

    def test_missing_reports_fail(self):
        result = subprocess.CompletedProcess([], 1, "", "")
        with patch.object(diff, "run", return_value=result):
            self.assertTrue(diff.compare("example.exr"))

    def test_timeouts_fail(self):
        with patch.object(diff, "run", return_value=None):
            self.assertTrue(diff.compare("example.exr"))

    def test_metadata_schema_rejections(self):
        data = (ROOT / "test/unit/regression/leangen-scanline.exr").read_bytes()
        attrs = {}
        cursor = 8
        while data[cursor]:
            end = data.index(0, cursor)
            name = data[cursor:end].decode()
            start = end + 1
            end = data.index(0, start)
            size = struct.unpack_from("<I", data, end + 1)[0]
            value = end + 5
            attrs[name] = (start, end, value)
            cursor = value + size
        cases = []
        for name, (start, end, _) in attrs.items():
            changed = bytearray(data)
            changed[start:end] = b"X" * (end - start)
            cases.append(("wrong type: " + name, changed))
        changed = bytearray(data)
        struct.pack_into("<i", changed, attrs["chunkCount"][2], -1)
        cases.append(("negative chunkCount", changed))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "metadata.exr"
            for label, changed in cases:
                with self.subTest(case=label):
                    path.write_bytes(changed)
                    lean = diff.lean_facts(str(path))
                    c = diff.harness_facts(str(path))
                    self.assertIsNone(lean["error"])
                    self.assertFalse(lean["ok"])
                    self.assertFalse(c["header_ok"])
                    self.assertEqual(diff.compare(str(path)), [])

    def test_raw_attribute_order_and_extensions(self):
        data = (ROOT / "test/unit/regression/leangen-scanline.exr").read_bytes()
        attrs, cursor, count = [], 8, None
        while data[cursor]:
            start = cursor
            end = data.index(0, cursor)
            name = data[cursor:end]
            end = data.index(0, end + 1)
            size = struct.unpack_from("<I", data, end + 1)[0]
            cursor = end + 5 + size
            attrs.append(data[start:cursor])
            if name == b"chunkCount":
                count = struct.unpack_from("<I", data, end + 5)[0]
        self.assertIsNotNone(count)
        table = cursor + 1
        extensions = [f"custom{i}".encode() + b"\0opaque\0" + struct.pack("<I", 3) + b"a\0b"
                      for i in range(20)]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "raw-headers.exr"
            long_attr = b"x" * 64 + b"\0opaque\0" + struct.pack("<I", 0)
            for label, emitted, long_names in [("reversed", attrs[::-1], False),
                                               ("extended", attrs + extensions, False),
                                               ("both", extensions + attrs[::-1], False),
                                               ("long-name", attrs + [long_attr], True)]:
                with self.subTest(case=label):
                    version = struct.unpack_from("<I", data, 4)[0] | (0x400 if long_names else 0)
                    prefix = data[:4] + struct.pack("<I", version) + b"".join(emitted) + b"\0"
                    delta = len(prefix) - table
                    offsets = [struct.unpack_from("<Q", data, table + 8 * i)[0] + delta
                               for i in range(count)]
                    path.write_bytes(prefix + b"".join(struct.pack("<Q", n) for n in offsets)
                                     + data[table + 8 * count:])
                    self.assertEqual(diff.compare(str(path)), [])
                    self.assertTrue(diff.harness_facts(str(path))["load_ok"])
                    result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stdout)

    def test_mixed_flat_deep_multipart(self):
        def attr(name, kind, value):
            return name + b"\0" + kind + b"\0" + struct.pack("<I", len(value)) + value
        headers, part_chunks = [], []
        for part, kind in enumerate(["scanline", "deepscanline"]):
            data = (ROOT / f"test/unit/regression/leangen-{kind}.exr").read_bytes()
            attrs, cursor, count = [], 8, None
            while data[cursor]:
                start = cursor
                end = data.index(0, cursor)
                name = data[cursor:end]
                end = data.index(0, end + 1)
                size = struct.unpack_from("<I", data, end + 1)[0]
                cursor = end + 5 + size
                if name not in (b"name", b"type", b"version"):
                    attrs.append(data[start:cursor])
                if name == b"chunkCount":
                    count = struct.unpack_from("<I", data, end + 5)[0]
            self.assertIsNotNone(count)
            attrs += [attr(b"name", b"string", f"part{part}".encode()),
                      attr(b"type", b"string", b"scanlineimage" if part == 0 else b"deepscanline"),
                      attr(b"version", b"int", struct.pack("<I", 1))]
            headers.append(b"".join(attrs[::-1]) + b"\0")
            offsets = [struct.unpack_from("<Q", data, cursor + 1 + i * 8)[0] for i in range(count)]
            chunks = [struct.pack("<I", part) + data[offset:end]
                      for offset, end in zip(offsets, offsets[1:] + [len(data)])]
            part_chunks.append(chunks)
        prefix = struct.pack("<II", 0x01312f76, 2 | 0x800 | 0x1000) + b"".join(headers) + b"\0"
        chunks = [chunk for group in part_chunks for chunk in group]
        cursor, offsets = len(prefix) + len(chunks) * 8, []
        for chunk in chunks:
            offsets.append(cursor)
            cursor += len(chunk)
        data = prefix + b"".join(struct.pack("<Q", n) for n in offsets) + b"".join(chunks)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "mixed.exr"
            path.write_bytes(data)
            self.assertEqual(diff.compare(str(path)), [])
            self.assertTrue(diff.harness_facts(str(path))["load_ok"])
            result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout)

    def test_missing_part_report_fails(self):
        result = subprocess.CompletedProcess([], 0, "file-ok true 1\n", "")
        with patch.object(diff, "run", return_value=result):
            self.assertIsNotNone(diff.lean_facts("example.exr")["error"])

    def test_empty_multipart_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "empty.exr"
            path.write_bytes(struct.pack("<II", 0x01312f76, 0x1002) + b"\0")
            self.assertFalse(diff.lean_facts(str(path))["ok"])
            self.assertFalse(diff.harness_facts(str(path))["header_ok"])
            self.assertEqual(diff.compare(str(path)), [])

    def test_changed_metadata_fails_comparison(self):
        path = str(ROOT / "test/unit/regression/leangen-scanline.exr")
        lean, c = diff.lean_facts(path), diff.harness_facts(path)
        self.assertIsNone(lean["error"])
        self.assertTrue(c["header_ok"])
        for field in ("window", "size", "channels", "compression_id", "tile", "channel_info"):
            changed = copy.deepcopy(c)
            changed["parts"][0][field] = "deliberately different"
            with self.subTest(field=field), patch.object(diff, "lean_facts", return_value=lean), patch.object(diff, "harness_facts", return_value=changed):
                self.assertTrue(diff.compare(path))

    def test_seeded_structures(self):
        generator = ROOT / "lean/.lake/build/bin/exrgen"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "seeded.exr"
            for kind in ("scanline", "tiled", "mipmap", "ripmap", "deepscanline", "deeptiled", "multipart"):
                previous = None
                for seed in (1, 7, 42):
                    with self.subTest(kind=kind, seed=seed):
                        subprocess.run([str(generator), str(path), str(seed), kind],
                                       check=True, capture_output=True)
                        data = path.read_bytes()
                        self.assertNotEqual(data, previous)
                        previous = data
                        self.assertEqual(diff.compare(str(path)), [])
                        self.assertTrue(diff.harness_facts(str(path))["load_ok"])
                        checked = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)],
                                                 capture_output=True, check=False)
                        self.assertEqual(checked.returncode, 0, checked.stdout)
                        reference = os.environ.get("LEAN_OPENEXR_TEST_BIN")
                        if reference:
                            count = int(kind == "deeptiled" or (kind == "deepscanline" and seed != 1))
                            result = subprocess.run([reference, str(path), str(count)], capture_output=True)
                            self.assertEqual(result.returncode, 0, result.stderr)

    def test_openexr_probe_checks_samples(self):
        binary = os.environ.get("LEAN_OPENEXR_TEST_BIN")
        if not binary:
            self.skipTest("independent OpenEXR oracle is exercised by make lean-openexr-test")
        data = bytearray((ROOT / "test/unit/regression/leangen-scanline.exr").read_bytes())
        cursor = 8
        while data[cursor]:
            cursor = data.index(0, cursor) + 1
            cursor = data.index(0, cursor) + 1
            size = struct.unpack_from("<I", data, cursor)[0]
            cursor += 4 + size
        offset = struct.unpack_from("<Q", data, cursor + 1)[0]
        struct.pack_into("<H", data, offset + 8, 0x3c00)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "nonzero.exr"
            path.write_bytes(data)
            result = subprocess.run([binary, str(path), "0"], capture_output=True)
            self.assertEqual(result.returncode, 1)
            self.assertIn(b"nonzero fixture sample", result.stderr)
        result = subprocess.run([binary, str(ROOT / "test/unit/regression/leangen-deeptiled.exr"), "0"], capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"sample-count mismatch", result.stderr)

    def test_openexr_reads_c_deep_edge_tiles(self):
        reference = os.environ.get("LEAN_OPENEXR_TEST_BIN")
        if not reference:
            self.skipTest("C/OpenEXR interoperability is exercised by make lean-openexr-test")
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.exr"
            output = Path(directory) / "rewritten.exr"
            subprocess.run([str(ROOT / "lean/.lake/build/bin/exrgen"), str(source), "42", "deeptiled"],
                           check=True, capture_output=True)
            for codec in ("NONE", "RLE", "ZIPS"):
                with self.subTest(codec=codec):
                    result = subprocess.run([str(ROOT / "build/rewrite_harness"), str(source), str(output), codec],
                                            capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertTrue(diff.harness_facts(str(output))["load_ok"])
                    result = subprocess.run([reference, str(output), "1"], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(output)], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stdout)

    def test_compact_legacy_deep_edge_tables_remain_readable(self):
        data = (ROOT / "test/unit/regression/leangen-deeptiled-edge.exr").read_bytes()
        cursor, count = 8, 0
        while data[cursor]:
            end = data.index(0, cursor)
            name = data[cursor:end]
            cursor = data.index(0, end + 1) + 1
            size = struct.unpack_from("<I", data, cursor)[0]
            cursor += 4
            if name == b"chunkCount":
                count = struct.unpack_from("<I", data, cursor)[0]
            cursor += size
        cursor += 1
        self.assertEqual(count, 6)
        offsets = [struct.unpack_from("<Q", data, cursor + 8 * i)[0] for i in range(count)]
        chunks = []
        for offset in offsets:
            tx, ty, _, _ = struct.unpack_from("<4i", data, offset)
            width, height = min(8, 14 - tx * 8), min(8, 19 - ty * 8)
            actual = width * height * 4
            packed_counts, packed_samples = struct.unpack_from("<QQ", data, offset + 16)
            header = bytearray(data[offset:offset + 40])
            struct.pack_into("<Q", header, 16, actual)
            counts = data[offset + 40:offset + 40 + actual]
            samples = data[offset + 40 + packed_counts:offset + 40 + packed_counts + packed_samples]
            chunks.append(header + counts + samples)
        new_offsets, start = [], cursor + count * 8
        for chunk in chunks:
            new_offsets.append(start)
            start += len(chunk)
        compact = data[:cursor] + b"".join(struct.pack("<Q", n) for n in new_offsets) + b"".join(chunks)
        self.assertLess(len(compact), len(data))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "compact-deep.exr"
            path.write_bytes(compact)
            self.assertTrue(diff.harness_facts(str(path))["load_ok"])
            self.assertEqual(diff.compare(str(path)), [])
            result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout)

    def test_subsampled_negative_origin_payload_sizes(self):
        def attr(name, kind, value):
            return name.encode() + b"\0" + kind.encode() + b"\0" + struct.pack("<I", len(value)) + value
        channels = [("B", 2, 2), ("G", 1, 1), ("R", 4, 3)]
        chlist = b"".join(name.encode() + b"\0" + struct.pack("<I4Bii", 1, 0, 0, 0, 0, xs, ys)
                          for name, xs, ys in channels) + b"\0"
        window = struct.pack("<4i", -4, -6, 3, -1)
        header = b"".join([
            attr("channels", "chlist", chlist), attr("compression", "compression", b"\0"),
            attr("dataWindow", "box2i", window), attr("displayWindow", "box2i", window),
            attr("lineOrder", "lineOrder", b"\0"), attr("pixelAspectRatio", "float", struct.pack("<f", 1)),
            attr("screenWindowCenter", "v2f", bytes(8)), attr("screenWindowWidth", "float", struct.pack("<f", 1)),
        ]) + b"\0"
        prefix = struct.pack("<II", 0x01312f76, 2) + header
        chunks, offsets = [], []
        cursor = len(prefix) + 6 * 8
        for y in range(-6, 0):
            samples = sum(sum(x % xs == 0 for x in range(-4, 4))
                          for _, xs, ys in channels if y % ys == 0)
            chunk = struct.pack("<ii", y, samples * 2) + bytes(samples * 2)
            offsets.append(cursor)
            chunks.append(chunk)
            cursor += len(chunk)
        data = prefix + b"".join(struct.pack("<Q", n) for n in offsets) + b"".join(chunks)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "subsampled.exr"
            path.write_bytes(data)
            self.assertEqual(diff.compare(str(path)), [])
            self.assertTrue(diff.harness_facts(str(path))["load_ok"])
            result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout)
            changed = bytearray(data)
            size = struct.unpack_from("<i", changed, offsets[0] + 4)[0]
            struct.pack_into("<i", changed, offsets[0] + 4, size + 2)
            path.write_bytes(changed)
            self.assertTrue(diff.lean_facts(str(path))["ok"])
            result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)], capture_output=True)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertFalse(diff.harness_facts(str(path))["load_ok"])

    def test_chunk_corruption_rejected(self):
        for kind in ("scanline", "tiled", "deepscanline", "deeptiled", "multipart"):
            original = (ROOT / f"test/unit/regression/leangen-{kind}.exr").read_bytes()
            cursor = 8
            while True:
                while original[cursor]:
                    cursor = original.index(0, cursor) + 1
                    cursor = original.index(0, cursor) + 1
                    size = struct.unpack_from("<I", original, cursor)[0]
                    cursor += 4 + size
                cursor += 1
                if kind != "multipart":
                    break
                if original[cursor] == 0:
                    cursor += 1
                    break
            offset = struct.unpack_from("<Q", original, cursor)[0]
            variants = []
            changed = bytearray(original)
            struct.pack_into("<i", changed, offset, -1)
            variants.append(("bad coordinate or part", changed))
            changed = bytearray(original)
            if kind in ("deepscanline", "deeptiled"):
                struct.pack_into("<Q", changed, offset + (16 if kind == "deeptiled" else 4), 0xffffffffffffffff)
            else:
                size_offset = offset + (16 if kind == "tiled" else 8 if kind == "multipart" else 4)
                struct.pack_into("<i", changed, size_offset, 2147483647)
            variants.append(("payload past EOF", changed))
            variants.append(("truncated payload", original[:-1]))
            if kind in ("deepscanline", "deeptiled"):
                changed = bytearray(original)
                struct.pack_into("<i", changed, offset + (40 if kind == "deeptiled" else 28), -1)
                variants.append(("negative cumulative count", changed))
                changed = bytearray(original)
                field = offset + (32 if kind == "deeptiled" else 20)
                size = struct.unpack_from("<Q", changed, field)[0]
                struct.pack_into("<Q", changed, field, size + 2)
                variants.append(("unpacked sample-size mismatch", changed))
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "chunk.exr"
                for label, data in variants:
                    with self.subTest(kind=kind, case=label):
                        path.write_bytes(data)
                        self.assertTrue(diff.lean_facts(str(path))["ok"])
                        result = subprocess.run([diff.DEFAULT_LEAN, "--chunks", str(path)],
                                                capture_output=True, check=False)
                        self.assertEqual(result.returncode, 1, result.stdout)

    def test_strict_optional_shared_attributes(self):
        data = (ROOT / "test/unit/regression/leangen-multipart.exr").read_bytes()
        headers = []
        cursor, chunks = 8, 0
        for _ in range(2):
            start = cursor
            while data[cursor]:
                end = data.index(0, cursor)
                name = data[cursor:end]
                end = data.index(0, end + 1)
                size = struct.unpack_from("<I", data, end + 1)[0]
                value = end + 5
                if name == b"chunkCount":
                    chunks += struct.unpack_from("<I", data, value)[0]
                cursor = value + size
            headers.append(data[start:cursor])
            cursor += 1
        self.assertEqual(data[cursor], 0)
        cursor += 1
        for name, type_name, size in ((b"chromaticities", b"chromaticities", 32),
                                     (b"timecode", b"timecode", 8)):
            def attr(value):
                return name + b"\0" + type_name + b"\0" + struct.pack("<I", size) + value
            shared = attr(bytes(size))
            changed = attr(bytes([1]) + bytes(size - 1))
            for second, expected in ((shared, 0), (changed, 1), (b"", 1)):
                prefix = data[:8] + headers[0] + shared + b"\0" + headers[1] + second + b"\0\0"
                delta = len(prefix) - cursor
                offsets = [struct.unpack_from("<Q", data, cursor + 8 * i)[0] + delta
                           for i in range(chunks)]
                rebuilt = prefix + b"".join(struct.pack("<Q", n) for n in offsets) + data[cursor + chunks * 8:]
                with tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / "shared.exr"
                    path.write_bytes(rebuilt)
                    result = subprocess.run([diff.DEFAULT_LEAN, "--strict", str(path)],
                                            capture_output=True, check=False)
                    with self.subTest(attribute=name, expected=expected):
                        self.assertEqual(result.returncode, expected, result.stdout)
                        self.assertTrue(diff.lean_facts(str(path))["ok"])

    def test_required_corpus_is_not_silently_skipped(self):
        with tempfile.TemporaryDirectory() as directory:
            for path in (directory, str(Path(directory) / "missing")):
                result = subprocess.run(
                    ["python3", str(ROOT / "test/v3/lean_diff.py"),
                     "--require-corpus", path,
                     str(ROOT / "test/unit/regression/leangen-scanline.exr")],
                    capture_output=True, check=False,
                )
                self.assertEqual(result.returncode, 2)
                self.assertIn(b"required corpus missing or empty", result.stderr)

    def test_axiom_audit_rejects_unapproved_trust(self):
        audit = (ROOT / "lean/AxiomAudit.lean").read_text()
        for declaration in (
            "axiom Exr.forbiddenAuditAxiom : False\n"
            "theorem Exr.forbiddenAuditTheorem : False := Exr.forbiddenAuditAxiom\n",
            "theorem Exr.forbiddenAuditTheorem : False := by sorry\n",
        ):
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "AuditNegative.lean"
                path.write_text(audit.replace("open Lean Elab Command",
                                             declaration + "\nopen Lean Elab Command"))
                result = subprocess.run(["lake", "env", "lean", str(path)],
                                        cwd=ROOT / "lean", capture_output=True, check=False)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(b"unexpected axiom", result.stdout)

    def test_codec_vector_negative_controls(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vectors.bin"
            subprocess.run([str(ROOT / "lean/.lake/build/bin/codecgen"), str(path), "42"],
                           check=True, capture_output=True)
            valid = path.read_bytes()
            binary = os.environ.get("LEAN_CODEC_TEST_BIN", str(ROOT / "build/codec_diff"))
            cursor, encoded = 8, {}
            for _ in range(struct.unpack_from("<I", valid, 4)[0]):
                kind = valid[cursor]
                count = struct.unpack_from("<I", valid, cursor + 2)[0]
                cursor += 6 + count * 4
                size = struct.unpack_from("<I", valid, cursor)[0]
                if size:
                    if kind != 19 or struct.unpack_from("<I", valid, cursor + 4 + size)[0]:
                        encoded.setdefault(kind, (cursor + 4, size))
                cursor += 4 + size
                cursor += 4 + struct.unpack_from("<I", valid, cursor)[0]
            self.assertEqual(set(encoded), set(range(21)))
            for kind, (offset, size) in encoded.items():
                with self.subTest(kind=kind):
                    changed = bytearray(valid)
                    # Flip a meaningful byte, preserving the length/count fields.
                    changed[offset + (4 if kind == 13 else 0)] ^= 1
                    path.write_bytes(changed)
                    result = subprocess.run([binary, str(path)], capture_output=True)
                    self.assertIn(result.returncode, (1, 2), result.stderr)
                    self.assertNotIn(b"AddressSanitizer", result.stderr)
                    self.assertNotIn(b"runtime error:", result.stderr)

    def test_invalid_vector_suites_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "vectors.bin"
            subprocess.run([str(ROOT / "lean/.lake/build/bin/codecgen"), str(path), "1"],
                           check=True, capture_output=True)
            valid = path.read_bytes()
            binary = os.environ.get("LEAN_CODEC_TEST_BIN", str(ROOT / "build/codec_diff"))
            result = subprocess.run([binary, str(path)], capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            count = struct.unpack_from("<I", valid, 10)[0]
            cursor = 14 + count * 4
            cursor += 4 + struct.unpack_from("<I", valid, cursor)[0]
            cursor += 4 + struct.unpack_from("<I", valid, cursor)[0]
            cases = [
                b"TEXV" + struct.pack("<I", 0),
                b"TEXV" + struct.pack("<I", 1) + bytes([255, 0])
                + struct.pack("<III", 0, 0, 0),
                b"TEXV" + struct.pack("<I", 1),
                b"TEXV" + struct.pack("<I", 1) + bytes([0, 1])
                + struct.pack("<III", 0, 0, 0),
                b"TEXV" + struct.pack("<I", 1) + bytes([0, 0])
                + struct.pack("<III", 0xffffffff, 0, 0),
                valid + b"trailing bytes",
                valid[:4] + struct.pack("<I", 1) + valid[8:cursor],
            ]
            for index, data in enumerate(cases):
                with self.subTest(case=index):
                    path.write_bytes(data)
                    result = subprocess.run([binary, str(path)], capture_output=True, check=False)
                    self.assertIn(result.returncode, (1, 2), result.stderr)
                    self.assertNotIn(b"AddressSanitizer", result.stderr)
                    self.assertNotIn(b"runtime error:", result.stderr)


if __name__ == "__main__":
    unittest.main()
