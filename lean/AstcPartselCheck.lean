/-
  TinyEXR - ASTC partition-search / classification differential checker.

  Reads vectors emitted by `test/v3/astc_partsel_vectors.c` and compares
  `Texcomp.astcAxisExtremesRgba`, `astcBitmapMismatch`,
  `astcBlockIsOpaque` / `astcBlockIsLuminance` / `astcBlockIsRgbScale` and
  `astcFindBestPartition`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcPartitionSearch

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
  let path := args.getD 0 "/tmp/opencode/astc_partsel_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "AX" then
      let count := natAt head 1
      let block := blockFrom head 2 count
      let t1 := fields (sections.getD 1 "")
      let wantLo := valsFrom t1 0 4
      let wantHi := valsFrom t1 4 4
      let (lo, hi) := astcAxisExtremesRgba block count
      if lo != wantLo || hi != wantHi then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} AX: got {lo} {hi}, want {wantLo} {wantHi}"
    else if kind == "BM" then
      let bbits := valsFrom head 1 3
      let seed := valsFrom head 4 3
      let mask := valsFrom head 7 3
      let words := natAt head 10
      let want := natAt (fields (sections.getD 1 "")) 0
      let got := astcBitmapMismatch bbits seed mask words
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} BM: got {got}, want {want}"
    else if kind == "PR" then
      let count := natAt head 1
      let block := blockFrom head 2 count
      let t1 := fields (sections.getD 1 "")
      let wantOp := natAt t1 0 != 0
      let wantLum := natAt t1 1 != 0
      let wantSc := natAt t1 2 != 0
      let gotOp := astcBlockIsOpaque block count
      let gotLum := astcBlockIsLuminance block count
      let gotSc := astcBlockIsRgbScale block count
      if gotOp != wantOp || gotLum != wantLum || gotSc != wantSc then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} PR {count}: got {gotOp} {gotLum} {gotSc}, want {wantOp} {wantLum} {wantSc}"
    else if kind == "S" then
      let bx := natAt head 1
      let bh := natAt head 2
      let pc := natAt head 3
      let block := blockFrom head 4 (bx * bh)
      let t1 := fields (sections.getD 1 "")
      let wantRet := natAt t1 0 != 0
      let wantIdx := decInt (t1.getD 1 "0")
      let got := astcFindBestPartition block bx bh pc
      let gotI := match got with
        | some (i, r) => (Int.ofNat i, r)
        | none => (-1, false)
      let wantI := (wantIdx, wantRet)
      if gotI != wantI then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} S {bx}x{bh} pc{pc}: got {gotI}, want {wantI}"
  IO.println s!"{lines.length} partition-search vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc partsel mismatch")
