/-
  TinyEXR - ASTC weight LUT + infill differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_infill_vectors.c` (`W` quant LUT
  lines, `G` grid-infill lines, `Q` quantised-infill lines) and compares
  `Texcomp.astcWqQ/astcWqWt/astcWqErr`, `astcInfillWeightsGrid` and
  `astcInfillWeights` with the C tables and `tc_astc_infill_weights*`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcWeightInfill

open Texcomp

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def valsFrom (xs : List String) (start n : Nat) : List Nat :=
  (List.range n).map (fun i => natAt xs (start + i))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_infill_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut luts := 0
  let mut grids := 0
  let mut quants := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "W" then
      luts := luts + 1
      let qm := natAt head 1
      let wantQ := valsFrom (fields (sections.getD 1 "")) 0 65
      let wantWt := valsFrom (fields (sections.getD 2 "")) 0 65
      let wantErr := valsFrom (fields (sections.getD 3 "")) 0 65
      let gotQ := (List.range 65).map (fun i => astcWqQ qm i)
      let gotWt := (List.range 65).map (fun i => astcWqWt qm i)
      let gotErr := (List.range 65).map (fun i => astcWqErr qm i)
      if gotQ != wantQ || gotWt != wantWt || gotErr != wantErr then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} W {qm}: LUT mismatch"
    else if kind == "G" then
      grids := grids + 1
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let wantGrid := valsFrom (fields (sections.getD 1 "")) 0 (wx * wy)
      let wantWt := valsFrom (fields (sections.getD 2 "")) 0 (bx * bh)
      let got := astcInfillWeightsGrid wantGrid bx bh wx wy
      if got != wantWt then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} G {bx} {bh} {wx} {wy}: mismatch"
    else if kind == "Q" then
      quants := quants + 1
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let wantWeights := valsFrom (fields (sections.getD 1 "")) 0 (wx * wy)
      let wantWt := valsFrom (fields (sections.getD 2 "")) 0 (bx * bh)
      let got := astcInfillWeights wantWeights bx bh wx wy qm
      if got != wantWt then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} Q {bx} {bh} {wx} {wy} qm {qm}: mismatch"
  IO.println s!"{luts} weight LUTs + {grids} grid infills + {quants} quantised infills checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc weight infill mismatch")
