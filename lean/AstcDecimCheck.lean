/-
  TinyEXR - ASTC weight-decimation differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_decim_vectors.c`
  (`T ...` tap lines, `D ...` cache-entry lines) and compares
  `Texcomp.astcTexelWeights2d` / `astcDecimEntry` with the C
  `tc_astc_texel_weights_2d` / `tc_astc_get_decim_cache`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcDecim

open Texcomp

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

/-- Read `n` `(q, w)` pairs starting at field `start`. -/
def pairsFrom (xs : List String) (start n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun i => (natAt xs (start + 2 * i), natAt xs (start + 2 * i + 1)))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_decim_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut taps := 0
  let mut entries := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "T" then
      taps := taps + 1
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let x := natAt head 5
      let y := natAt head 6
      let t2 := fields (sections.getD 1 "")
      let n := natAt t2 0
      let want := pairsFrom t2 1 n
      let got := astcTexelWeights2d bx bh wx wy x y
      if got != want then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} T {bx} {bh} {wx} {wy} {x} {y}: got {got}, want {want}"
    else if kind == "D" then
      entries := entries + 1
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let wantDirect := natAt head 5 != 0
      let count := natAt head 6
      let tapFields := fields (sections.getD 1 "")
      let wantTaps := (List.range count).map (fun i => pairsFrom tapFields (i * 8) 4)
      let contribFields := fields (sections.getD 2 "")
      let wantContribs := (List.range 64).map (fun k => natAt contribFields k)
      let (gotTaps, gotContribs, gotDirect) := astcDecimEntry bx bh wx wy
      if gotTaps != wantTaps || gotContribs != wantContribs || gotDirect != wantDirect then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} D {bx} {bh} {wx} {wy}: entry mismatch"
  IO.println s!"{taps} taps + {entries} cache entries checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc decimation mismatch")
