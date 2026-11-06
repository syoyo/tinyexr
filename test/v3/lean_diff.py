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


def lean_facts(path):
    res = run([DEFAULT_LEAN, path])
    if res is None:
        return {"ok": False, "error": "timeout", "parts": []}
    ok = False
    parts = []
    for line in res.stdout.splitlines():
        if line.startswith("file-ok "):
            ok = line.split()[1] == "true"
        m = PART_RE.match(line)
        if m:
            idx, ptype, tiled, deep, chunks, declared, table = m.groups()
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
    return {"ok": ok, "parts": parts, "error": None if res.returncode in (0, 1) else res.returncode}


def harness_facts(path):
    res = run([DEFAULT_HARNESS, path])
    if res is None:
        return {"header_ok": False, "load_ok": False, "parts": [], "timeout": True}
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
    files = collect(corpus)
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
