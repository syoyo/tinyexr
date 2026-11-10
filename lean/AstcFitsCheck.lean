/-
  TinyEXR - ASTC fit-path differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_fits_vectors.c` and compares
  `Texcomp.astcAxisExtremes`, `astcProjectWeight`,
  `astcPartitionProject`, `astcWeightsFromIdeal{,_pt}`,
  `astcFitFromIdeal{,_pt}`, `astcRgbSseFromStats`,
  `astcScrambleWeights` and `astcInvertWeights`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcFits

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def decInt (s : String) : Int :=
  if s.startsWith "-" then -Int.ofNat (decNat (s.drop 1).toString) else Int.ofNat (decNat s)

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def valsFrom (xs : List String) (start n : Nat) : List Nat :=
  (List.range n).map (fun i => natAt xs (start + i))

def blockFrom (xs : List String) (start count : Nat) : List (List Nat) :=
  (List.range count).map (fun i => valsFrom xs (start + i * 4) 4)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_fits_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "A" then
      let count := natAt head 1
      let axis := natAt head 2
      let block := blockFrom head 3 count
      let want := valsFrom (fields (sections.getD 1 "")) 0 2
      let got := astcAxisExtremes block count axis
      if (got.1, got.2) != (want.getD 0 0, want.getD 1 0) then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} A: got {(got.1, got.2)}, want {want}"
    else if kind == "PW" then
      let dot64 := natAt head 1
      let recip := natAt head 2
      let want := natAt (fields (sections.getD 1 "")) 0
      let got := astcProjectWeight dot64 recip
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} PW {dot64} {recip}: got {got}, want {want}"
    else if kind == "P" then
      let count := natAt head 1
      let pc := natAt head 2
      let partOf := valsFrom head 3 count
      let lo := (List.range 4).map (fun p => valsFrom head (3 + count + p * 4) 4)
      let hi := (List.range 4).map (fun p => valsFrom head (3 + count + 16 + p * 4) 4)
      let block := blockFrom head (3 + count + 32) count
      let wantEndpoints := natAt head (3 + count + 32 + count * 4) != 0
      let wantAll := natAt (fields (sections.getD 1 "")) 0 != 0
      let wantIdeal := valsFrom (fields (sections.getD 2 "")) 0 count
      let wantActive := valsFrom (fields (sections.getD 3 "")) 0 count
      let (ideal, active, allAct, e0t, e1t) :=
        astcPartitionProject block count partOf lo hi pc wantEndpoints
      let okE :=
        if wantEndpoints then
          e0t == blockFrom (fields (sections.getD 4 "")) 0 count &&
            e1t == blockFrom (fields (sections.getD 5 "")) 0 count
        else e0t.isEmpty && e1t.isEmpty
      if ideal != wantIdeal || active != wantActive || allAct != wantAll || !okE then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} P {count} {pc}: ok={okE} ideal={ideal == wantIdeal} active={active == wantActive} all={allAct == wantAll}\n  got {(ideal.take 8)} want {(wantIdeal.take 8)}\n  lo {lo}\n  hi {hi}\n  partOf {(partOf.take 8)}"
    else if kind == "W" || kind == "WP" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let ideal := valsFrom head 7 count
      let (wantOut, wantWt) :=
        if kind == "W" then
          (valsFrom (fields (sections.getD 1 "")) 0 (wx * wy),
           valsFrom (fields (sections.getD 2 "")) 0 count)
        else
          (valsFrom (fields (sections.getD 2 "")) 0 (wx * wy),
           valsFrom (fields (sections.getD 3 "")) 0 count)
      let active :=
        if kind == "W" then none else some (valsFrom (fields (sections.getD 1 "")) 0 count)
      let (outW, wt) := astcWeightsFromIdeal bx bh wx wy qm ideal active count
      if outW != wantOut || wt != wantWt then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} {kind} {bx}x{bh} {wx}x{wy} qm{qm}: out={outW == wantOut} wt={wt == wantWt}\n  got {outW.take 8} want {wantOut.take 8}"
    else if kind == "F" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let ideal := valsFrom head 7 count
      let block := blockFrom (fields (sections.getD 1 "")) 0 count
      let s2 := fields (sections.getD 2 "")
      let lo := valsFrom s2 0 4
      let hi := valsFrom s2 4 4
      let want := natAt (fields (sections.getD 3 "")) 0
      let got := astcFitFromIdeal bx bh wx wy qm count block ideal lo hi
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} F {bx}x{bh}: got {got}, want {want}"
    else if kind == "FP" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let ideal := valsFrom head 7 count
      let active := valsFrom (fields (sections.getD 1 "")) 0 count
      let block := blockFrom (fields (sections.getD 2 "")) 0 count
      let e0t := blockFrom (fields (sections.getD 3 "")) 0 count
      let e1t := blockFrom (fields (sections.getD 4 "")) 0 count
      let want := natAt (fields (sections.getD 5 "")) 0
      let got := astcFitFromIdealPt bx bh wx wy qm count block ideal active e0t e1t
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} FP {bx}x{bh}: got {got}, want {want}"
    else if kind == "S" then
      let count := natAt head 1
      let sums := valsFrom head 2 3
      let sumsq := valsFrom (fields (sections.getD 1 "")) 0 3
      let want := decInt ((fields (sections.getD 2 "")).getD 0 "0")
      let got := astcRgbSseFromStats sums sumsq count
      let gotI := match got with
        | some v => Int.ofNat v
        | none => -1
      if gotI != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} S: got {gotI}, want {want}"
    else if kind == "X" then
      let qm := natAt head 1
      let w := valsFrom head 2 64
      let wantS := valsFrom (fields (sections.getD 1 "")) 0 64
      let wantI := valsFrom (fields (sections.getD 2 "")) 0 64
      let gotS := astcScrambleWeights w 64 qm
      let gotI := astcInvertWeights w 64 qm
      if gotS != wantS || gotI != wantI then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} X {qm}: mismatch"
  IO.println s!"{lines.length} fit-path vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc fits mismatch")
