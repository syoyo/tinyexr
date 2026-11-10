/-
  TinyEXR - ASTC endpoint plumbing differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_endpoints_vectors.c`
  (`T` type-code/value-count, `L` colour-quant choice, `E` endpoint emit)
  and compares `Texcomp.astcPartitionEndpointTypeCode`,
  `astcPartitionEndpointValueCount`, `astcChooseColorQuant` /
  `astcColorQuantLut` and `astcEmitPartitionEndpointValues`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcEndpoints

open Texcomp

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def valsFrom (xs : List String) (start n : Nat) : List Nat :=
  (List.range n).map (fun i => natAt xs (start + i))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_endpoints_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut types := 0
  let mut quants := 0
  let mut emits := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let kind := head.getD 0 ""
    if kind == "T" then
      types := types + 1
      let pc := natAt head 1
      let formats := valsFrom head 2 pc
      let wantCode := natAt (fields (sections.getD 1 "")) 0
      let wantCount := natAt (fields (sections.getD 1 "")) 1
      let gotCode := astcPartitionEndpointTypeCode pc formats
      let gotCount := astcPartitionEndpointValueCount pc formats
      if gotCode != wantCode || gotCount != wantCount then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} T {pc} {formats}: got {gotCode} {gotCount}, want {wantCode} {wantCount}"
    else if kind == "L" then
      quants := quants + 1
      let vc := natAt head 1
      let bits := natAt head 2
      let t2 := fields (sections.getD 1 "")
      let wantOk := natAt t2 0 != 0
      let wantQm := natAt t2 1
      let got := astcChooseColorQuant vc bits
      let want := if wantOk then some wantQm else none
      if got != want then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} L {vc} {bits}: got {repr got}, want {repr want}"
    else if kind == "E" then
      emits := emits + 1
      let qm := natAt head 1
      let pc := natAt head 2
      let formats := valsFrom head 3 pc
      let loStart := 3 + pc
      let lo := (List.range 4).map (fun i => valsFrom head (loStart + i * 4) 4)
      let hi := (List.range 4).map (fun i => valsFrom head (loStart + 16 + i * 4) 4)
      let want := fields (sections.getD 1 "")
      let wantVals := valsFrom want 0 want.length
      let got := astcEmitPartitionEndpointValues qm pc formats lo hi
      if got != wantVals then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} E {qm} {pc} {formats}: got {got.length}, want {wantVals.length}"
  IO.println s!"{types} type codes + {quants} colour-quant choices + {emits} endpoint emits checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc endpoints mismatch")
