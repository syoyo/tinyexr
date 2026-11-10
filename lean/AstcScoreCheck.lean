/-
  TinyEXR - ASTC score-from-ideal / score-batch differential checker.

  Reads vectors emitted by `test/v3/astc_score_vectors.c` and compares
  `Texcomp.astcScoreFromIdeal` and `astcScoreBatch` with the C
  `tc_astc_score_from_ideal` and `tc_astc_score_batch`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcScore

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def valsFrom (xs : List String) (start n : Nat) : List Nat :=
  (List.range n).map (fun i => natAt xs (start + i))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_score_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "SF" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let ideal := valsFrom head 7 count
      let want := natAt (fields (sections.getD 1 "")) 0
      let got := astcScoreFromIdeal bx bh wx wy qm ideal none count
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} SF {bx}x{bh}: got {got}, want {want}"
    else if kind == "SFA" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let ideal := valsFrom head 7 count
      let active := valsFrom (fields (sections.getD 1 "")) 0 count
      let want := natAt (fields (sections.getD 2 "")) 0
      let got := astcScoreFromIdeal bx bh wx wy qm ideal (some active) count
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} SFA {bx}x{bh}: got {got}, want {want}"
    else if kind == "SB" then
      let bx := natAt head 1
      let bh := natAt head 2
      let wx := natAt head 3
      let wy := natAt head 4
      let qm := natAt head 5
      let count := natAt head 6
      let n := natAt head 7
      let ideals := (List.range n).map (fun bi =>
        valsFrom (fields (sections.getD (1 + bi) "")) 0 count)
      let wants := (fields (sections.getD (1 + n) "")).map decNat
      let got := astcScoreBatch bx bh wx wy qm ideals count
      if got != wants then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} SB {bx}x{bh} n{n}: got {got}, want {wants}"
  IO.println s!"{lines.length} score vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc score mismatch")
