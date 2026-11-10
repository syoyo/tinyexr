/-
  TinyEXR - ASTC least-squares / evaluation differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_lsq_vectors.c` and compares
  `Texcomp.astcDivRoundS64`, `astcLsqEndpoints{,_partition}`,
  `astcEval{Single,Partition,Dual}Sse`, `astcBlockHasRgbClusters` and
  `astcPartitionRgbScaleOk`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcEval

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
  let path := args.getD 0 "/tmp/opencode/astc_lsq_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "R" then
      let num := decInt (head.getD 1 "0")
      let den := decInt (head.getD 2 "0")
      let want := decInt ((fields (sections.getD 1 "")).getD 0 "0")
      let got := astcDivRoundS64 num den
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} R {num} {den}: got {got}, want {want}"
    else if kind == "L" then
      let count := natAt head 1
      let wt := valsFrom head 2 count
      let block := blockFrom head (2 + count) count
      let t1 := fields (sections.getD 1 "")
      let wantOk := natAt t1 0 != 0
      let wantLo := valsFrom t1 1 4
      let wantHi := valsFrom t1 5 4
      let got := astcLsqEndpoints block count wt
      let ok := match got with
        | some (lo, hi) => wantOk && lo == wantLo && hi == wantHi
        | none => !wantOk
      if !ok then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} L {count}: got {repr got}, want ok {wantOk} {wantLo} {wantHi}"
    else if kind == "LP" then
      let count := natAt head 1
      let part := natAt head 2
      let partOf := valsFrom head 3 count
      let wt := valsFrom head (3 + count) count
      let block := blockFrom head (3 + 2 * count) count
      let t1 := fields (sections.getD 1 "")
      let wantOk := natAt t1 0 != 0
      let wantLo := valsFrom t1 1 4
      let wantHi := valsFrom t1 5 4
      let got := astcLsqEndpointsPartition block count partOf part wt
      let ok := match got with
        | some (lo, hi) => wantOk && lo == wantLo && hi == wantHi
        | none => !wantOk
      if !ok then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} LP {count} {part}: got {repr got}, want ok {wantOk}"
    else if kind == "E" then
      let count := natAt head 1
      let fmt := natAt head 2
      let qm := natAt head 3
      let wt := valsFrom head 4 count
      let lo := valsFrom head (4 + count) 4
      let hi := valsFrom head (4 + count + 4) 4
      let block := blockFrom head (4 + count + 8) count
      let want := natAt (fields (sections.getD 1 "")) 0
      let got := astcEvalSingleSse block count wt fmt qm lo hi
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} E {count} f{fmt} qm{qm}: got {got}, want {want}"
    else if kind == "ED" then
      let count := natAt head 1
      let fmt := natAt head 2
      let qm := natAt head 3
      let wtc := valsFrom head 4 count
      let wta := valsFrom head (4 + count) count
      let lo := valsFrom head (4 + 2 * count) 4
      let hi := valsFrom head (4 + 2 * count + 4) 4
      let block := blockFrom head (4 + 2 * count + 8) count
      let want := natAt (fields (sections.getD 1 "")) 0
      let got := astcEvalDualSse block count wtc wta fmt qm lo hi
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} ED {count} f{fmt} qm{qm}: got {got}, want {want}"
    else if kind == "EP" then
      let count := natAt head 1
      let pc := natAt head 2
      let partOf := valsFrom head 3 count
      let formats := valsFrom head (3 + count) 4
      let partLo := (List.range 4).map (fun p => valsFrom head (3 + count + 4 + p * 4) 4)
      let partHi := (List.range 4).map (fun p => valsFrom head (3 + count + 4 + 16 + p * 4) 4)
      let qm := natAt head (3 + count + 4 + 32)
      let wt := valsFrom head (3 + count + 4 + 32 + 1) count
      let block := blockFrom head (3 + count + 4 + 32 + 1 + count) count
      let want := decInt ((fields (sections.getD 1 "")).getD 0 "0")
      let got := astcEvalPartitionSse block count partOf pc formats partLo partHi qm wt
      let gotI := match got with
        | some v => Int.ofNat v
        | none => -1
      if gotI != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} EP {count} pc{pc}: got {gotI}, want {want}"
    else if kind == "C" then
      let count := natAt head 1
      let wanted := natAt head 2
      let block := blockFrom head 3 count
      let want := natAt (fields (sections.getD 1 "")) 0 != 0
      let got := astcBlockHasRgbClusters block count wanted
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} C {count} {wanted}: got {got}, want {want}"
    else if kind == "K" then
      let lo := valsFrom head 1 3
      let hi := valsFrom (fields (sections.getD 1 "")) 0 3
      let want := natAt (fields (sections.getD 2 "")) 0 != 0
      let got := astcPartitionRgbScaleOk lo hi
      if got != want then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1} K {lo} {hi}: got {got}, want {want}"
  IO.println s!"{lines.length} least-squares/eval vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc lsq mismatch")
