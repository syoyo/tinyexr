#!/usr/bin/env python3
"""
LEAN <-> tinyexr v3 differential structural check.

Runs the Lean-backed checker (`lean/.lake/build/bin/exrcheck`, built with
`make lean-check` or `lake build`) and the tinyexr v3 parse harness
(`test/v3/parse_harness`) over a corpus and compares the structural facts:

  * accept/reject decision (header level),
  * per-part type, tiling/deep flags,
  * chunk count (computed),
  * data window and channel count.

Documented expected differences:

  * DWAA / DWAB: tinyexr v3 intentionally does not decode them. The header
    still parses, so the comparison is header-level only; a full-load failure
    is not a Lean disagreement.
  * The `v2/*/htj2k*_{Balls,Ground,Leaves,Trunks}.exr` deep files are corrupt
    on the write side (OpenEXR's own `exrmultipart` cannot load them either);
    they are excluded from *pixel* expectations but must still agree on the
    header verdict.

Exit status: 0 when no disagreement remains, 1 otherwise.

Usage:
    test/v3/lean_diff.py [--lean PATH] [--harness PATH] [corpus ...]

Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
SPDX-License-Identifier: BSD-3-Clause
"""

import argparse
import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_LEAN = os.path.join(ROOT, "lean", ".lake", "build", "bin", "exrcheck")
DEFAULT_HARNESS = os.path.join(ROOT, "test", "v3", "parse_harness")

DWA_COMPRESSIONS = {"DWAA", "DWAB"}

PART_RE = re.compile(
    r"^part (\d+) (\w+) (true|false) (true|false) (\d+) (\d+) (\d+)$"
)
HARNESS_PART_RE = re.compile(
    r"^PART (\d+) type=(\w+) compression=(\w+) channels=(\d+) size=(\d+)x(\d+) "
    r"chunks=(\d+) tiled=(\d+) deep=(\d+)$"
)

LEAN_TYPE_MAP = {
    "scanlineimage": "scanline",
    "tiledimage": "tiled",
    "deepscanline": "deep_scanline",
    "deeptile": "deep_tiled",
}


def run(cmd, timeout=300):
    try:
        return subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return None


def add_metadata(lines, parts):
    """Read shared numeric metadata records, validating indices and arity."""
    seen = set()
    for line in lines:
        fields = line.split()
        if not fields or fields[0] not in ("COMPRESSION", "TILE", "CHANNEL"):
            continue
        tag = fields[0]
        idx = int(fields[1])
        if idx < 0 or idx >= len(parts):
            raise ValueError("part index out of range")
        part = parts[idx]
        key = (tag, idx, fields[2] if tag == "CHANNEL" else None)
        if key in seen:
            raise ValueError("duplicate metadata record")
        seen.add(key)
        if tag == "COMPRESSION" and len(fields) == 3:
            part["compression_id"] = int(fields[2])
        elif tag == "TILE":
            if fields[2:] == ["none"]:
                part["tile"] = None
            elif len(fields) == 6:
                part["tile"] = tuple(map(int, fields[2:]))
            else:
                raise ValueError("invalid tile report")
        elif tag == "CHANNEL" and len(fields) == 8:
            channels = part.setdefault("channel_info", [])
            if int(fields[2]) != len(channels):
                raise ValueError("channel index out of order")
            name = tuple(map(int, fields[3].split(".")))
            channels.append((name, *map(int, fields[4:])))
        else:
            raise ValueError("invalid metadata report")
    for part in parts:
        if ("compression_id" not in part or "tile" not in part
                or len(part.get("channel_info", [])) != part.get("channels")):
            raise ValueError("incomplete metadata report")


def lean_facts(path):
    res = run([DEFAULT_LEAN, path])
    if res is None:
        return {"ok": False, "error": "timeout", "parts": []}
    if res.returncode not in (0, 1) or not any(
        line.startswith("file-ok ") for line in res.stdout.splitlines()
    ):
        return {"ok": False, "error": "invalid checker result", "parts": []}
    ok = False
    parts = []
    for line in res.stdout.splitlines():
        if line.startswith("file-ok "):
            ok = line.split()[1] == "true"
        m = PART_RE.match(line)
        if m:
            idx, ptype, tiled, deep, chunks, declared, table = m.groups()
            if int(idx) != len(parts):
                return {"ok": False, "parts": [], "error": "invalid part index"}
            parts.append(
                {
                    "type": LEAN_TYPE_MAP.get(ptype, ptype),
                    "tiled": tiled == "true",
                    "deep": deep == "true",
                    "chunks": int(chunks),
                    "declared": int(declared),
                    "table": int(table),
                }
            )
    for line in res.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] in ("part-window", "part-channels"):
            try:
                part = parts[int(fields[1])]
                if fields[0] == "part-window":
                    x0, y0, x1, y1 = map(int, fields[2:])
                    part["size"] = (x1 - x0 + 1, y1 - y0 + 1)
                    part["window"] = (x0, y0, x1, y1)
                else:
                    part["channels"] = int(fields[2])
            except (ValueError, IndexError):
                return {"ok": False, "parts": [], "error": "invalid part report"}
    reports = [line.split() for line in res.stdout.splitlines() if line.startswith("file-ok ")]
    if (len(reports) != 1 or len(reports[0]) != 3
            or reports[0][1] not in ("true", "false")
            or not reports[0][2].isdigit()
            or (ok and (int(reports[0][2]) != len(parts) or not parts))
            or res.returncode != (0 if ok else 1)):
        return {"ok": False, "parts": [], "error": "inconsistent checker result"}
    if ok:
        try:
            add_metadata(res.stdout.splitlines(), parts)
        except (ValueError, IndexError):
            return {"ok": False, "parts": [], "error": "invalid metadata report"}
    return {"ok": ok, "parts": parts, "error": None}


def harness_facts(path):
    res = run([DEFAULT_HARNESS, path])
    if res is None:
        return {"header_ok": False, "load_ok": False, "parts": [], "timeout": True}
    if res.returncode not in (0, 1) or not any(
        line.startswith("HEADER_RESULT ") for line in res.stdout.splitlines()
    ):
        return {"error": "invalid harness result", "timeout": False}
    header_ok = False
    load_ok = False
    parts = []
    compressions = []
    for line in res.stdout.splitlines():
        if line.startswith("HEADER_RESULT "):
            header_ok = line.split()[1] == "0"
        if line.startswith("LOAD_RESULT "):
            load_ok = line.split()[1] == "0"
        m = HARNESS_PART_RE.match(line)
        if m:
            idx, ptype, comp, chans, w, h, chunks, tiled, deep = m.groups()
            if int(idx) != len(parts):
                return {"error": "invalid part index", "timeout": False}
            compressions.append(comp)
            parts.append(
                {
                    "type": ptype,
                    "compression": comp,
                    "channels": int(chans),
                    "size": (int(w), int(h)),
                    "chunks": int(chunks),
                    "tiled": tiled == "1",
                    "deep": deep == "1",
                }
            )
    for line in res.stdout.splitlines():
        fields = line.split()
        if fields and fields[0] == "WINDOW":
            try:
                parts[int(fields[1])]["window"] = tuple(map(int, fields[2:]))
            except (ValueError, IndexError):
                return {"error": "invalid window report", "timeout": False}
    headers = [line for line in res.stdout.splitlines() if line.startswith("HEADER_RESULT ")]
    loads = [line for line in res.stdout.splitlines() if line.startswith("LOAD_RESULT ")]
    counts = [line.split() for line in res.stdout.splitlines() if line.startswith("PARTS ")]
    if (len(headers) != 1 or len(loads) != 1
            or re.fullmatch(r"HEADER_RESULT -?\d+ .+", headers[0]) is None
            or re.fullmatch(r"LOAD_RESULT -?\d+ .+", loads[0]) is None
            or res.returncode != (0 if load_ok else 1)
            or (header_ok and (len(counts) != 1 or len(counts[0]) != 2
                or not counts[0][1].isdigit() or int(counts[0][1]) != len(parts)
                or not parts))):
        return {"error": "inconsistent harness result", "timeout": False}
    if header_ok:
        try:
            add_metadata(res.stdout.splitlines(), parts)
        except (ValueError, IndexError):
            return {"error": "invalid metadata report", "timeout": False}
    return {
        "header_ok": header_ok,
        "load_ok": load_ok,
        "parts": parts,
        "compressions": compressions,
        "timeout": False,
    }


def compare(path):
    """Return a list of disagreement strings (empty = agreement)."""
    lf = lean_facts(path)
    cf = harness_facts(path)
    diffs = []

    if lf["error"] is not None:
        return [f"{path}: Lean checker failure: {lf['error']}"]

    if cf.get("error") is not None:
        return [f"{path}: C harness failure: {cf['error']}"]

    if cf["timeout"]:
        return [f"{path}: tinyexr harness timeout"]

    # Header-level acceptance must agree. DWAA/DWAB are header-compatible:
    # tinyexr parses the header but refuses the full load.
    if lf["ok"] != cf["header_ok"]:
        diffs.append(
            f"{path}: accept mismatch lean={lf['ok']} tinyexr_header={cf['header_ok']}"
        )

    # Per-part facts are only comparable when both sides accepted the header.
    if not (lf["ok"] and cf["header_ok"]):
        return diffs

    if len(lf["parts"]) != len(cf["parts"]):
        diffs.append(
            f"{path}: part count lean={len(lf['parts'])} tinyexr={len(cf['parts'])}"
        )
        return diffs

    for i, (lp, cp) in enumerate(zip(lf["parts"], cf["parts"])):
        for field in ("size", "window", "channels", "compression_id", "tile", "channel_info"):
            if field not in lp or field not in cp or lp[field] != cp[field]:
                diffs.append(f"{path}: part {i} {field} lean={lp.get(field)} tinyexr={cp.get(field)}")
        if lp["type"] != cp["type"]:
            diffs.append(f"{path}: part {i} type lean={lp['type']} tinyexr={cp['type']}")
        if lp["tiled"] != cp["tiled"]:
            diffs.append(f"{path}: part {i} tiled lean={lp['tiled']} tinyexr={cp['tiled']}")
        if lp["deep"] != cp["deep"]:
            diffs.append(f"{path}: part {i} deep lean={lp['deep']} tinyexr={cp['deep']}")
        if lp["chunks"] != cp["chunks"]:
            diffs.append(
                f"{path}: part {i} chunks lean={lp['chunks']} tinyexr={cp['chunks']}"
            )
        if lp["table"] != cp["chunks"]:
            diffs.append(
                f"{path}: part {i} offset-table lean={lp['table']} tinyexr={cp['chunks']}"
            )
    return diffs


def collect(paths):
    files = []
    for p in paths:
        if not p:
            continue
        if os.path.isdir(p):
            files.extend(sorted(glob.glob(os.path.join(p, "**", "*.exr"), recursive=True)))
        elif any(ch in p for ch in "*?["):
            files.extend(sorted(glob.glob(p, recursive=True)))
        elif os.path.exists(p):
            files.append(p)
        else:
            # e.g. ~/work/openexr-images or /tmp/exrgen on a CI runner
            print(f"note: skipping missing corpus path {p}", file=sys.stderr)
    return files


def main():
    global DEFAULT_LEAN, DEFAULT_HARNESS
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default=DEFAULT_LEAN)
    ap.add_argument("--harness", default=DEFAULT_HARNESS)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--require-corpus", action="append", default=[], metavar="PATH",
                    help="require a nonempty corpus at PATH and include it")
    ap.add_argument("corpus", nargs="*")
    args = ap.parse_args()

    DEFAULT_LEAN = args.lean
    DEFAULT_HARNESS = args.harness

    if not os.path.exists(DEFAULT_LEAN):
        print(f"error: Lean checker not found at {DEFAULT_LEAN}", file=sys.stderr)
        print("build it with: cd lean && lake build exrcheck", file=sys.stderr)
        return 2
    if not os.path.exists(DEFAULT_HARNESS):
        print(f"error: parse harness not found at {DEFAULT_HARNESS}", file=sys.stderr)
        print("build it with: make parse-test-harness", file=sys.stderr)
        return 2

    corpus = args.corpus or [
        os.path.join(ROOT, "test", "unit", "regression"),
        os.path.join(os.path.expanduser("~"), "work", "openexr-images"),
        "/tmp/exrgen",
    ]
    for path in args.require_corpus:
        if not os.path.exists(path) or not collect([path]):
            print(f"error: required corpus missing or empty: {path}", file=sys.stderr)
            return 2
    files = sorted(set(collect(corpus + args.require_corpus)))
    if not files:
        print("error: no .exr files found", file=sys.stderr)
        return 2

    diffs = []
    checked = 0
    for path in files:
        checked += 1
        diffs.extend(compare(path))

    if diffs:
        print(f"DISAGREEMENTS ({len(diffs)}):")
        for d in diffs:
            print("  " + d)
    print(f"checked {checked} files; {len(diffs)} disagreements")
    return 0 if not diffs else 1


if __name__ == "__main__":
    sys.exit(main())
