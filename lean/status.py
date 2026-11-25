#!/usr/bin/env python3
# TinyEXR - Lean formalization status summary.
# Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
# SPDX-License-Identifier: BSD-3-Clause

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent

AREAS = {
    "Exr": [ROOT / "Exr", ROOT / "ExrSpec.lean", ROOT / "ExrCheck.lean",
            ROOT / "ExrGen.lean", ROOT / "CodecGen.lean"],
    "Texcomp": [ROOT / "Texcomp"],
    "Tocio": [ROOT / "Tocio"],
    "Tir": [ROOT / "Tir"],
    "Math": [ROOT / "Math"],
}

DECL = re.compile(r"^\s*(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+", re.M)


def lean_files(paths):
    files = []
    for path in paths:
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
        elif path.is_file() and path.suffix == ".lean":
            files.append(path)
    # A file may be reached through more than one configured path.
    return sorted(set(files))


def count(paths):
    files = lean_files(paths)
    lines = 0
    theorems = 0
    for path in files:
        text = path.read_text(encoding="utf-8")
        lines += len(text.splitlines())
        theorems += len(DECL.findall(text))
    return len(files), lines, theorems


def diff_targets():
    text = (REPO / "Makefile").read_text(encoding="utf-8")
    return sorted(set(re.findall(r"^([A-Za-z0-9_-]+-diff):", text, re.M)))


def main():
    head = subprocess.check_output(
        ["git", "rev-parse", "--short", "HEAD"], cwd=REPO, text=True
    ).strip()
    branch = subprocess.check_output(
        ["git", "branch", "--show-current"], cwd=REPO, text=True
    ).strip()
    print(f"Lean status: {branch}@{head}")
    print(f"{'Area':<10} {'Files':>7} {'Lines':>9} {'Theorems':>10}")
    total_files = total_lines = total_theorems = 0
    for name, paths in AREAS.items():
        files, lines, theorems = count(paths)
        total_files += files
        total_lines += lines
        total_theorems += theorems
        print(f"{name:<10} {files:>7} {lines:>9} {theorems:>10}")
    root_files = [p for p in ROOT.glob("*.lean") if p.name != "lakefile.lean"]
    root_files = [p for p in root_files if all(p not in lean_files(paths) for paths in AREAS.values())]
    files, lines, theorems = count(root_files)
    total_files += files
    total_lines += lines
    total_theorems += theorems
    print(f"{'Root misc':<10} {files:>7} {lines:>9} {theorems:>10}")
    print(f"{'Total':<10} {total_files:>7} {total_lines:>9} {total_theorems:>10}")
    print(f"Differential targets: {len(diff_targets())}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
