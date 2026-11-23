/-
  TinyEXR - tir axis-measure differential checker (C vectors vs Lean model).

  Reads vectors emitted by `test/v3/tir_vectors.c` (destination width, the
  C `fast_lo`/`fast_hi`/`n_exc` fields, and the per-output fast bit string),
  replays `Tir.measureScan` on the same bits and reports mismatches.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tir.Table

open Tir

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 5 then false else
  let d := (f.getD 0 "0").toNat!
  let wantLo := (f.getD 1 "0").toNat!
  let wantHi := (f.getD 2 "0").toNat!
  let wantExc := (f.getD 3 "0").toNat!
  let bits := (f.getD 4 "").toList
  let cls : Nat → Bool := fun i => bits.getD i '0' == '1'
  let st := measureScan d cls d
  st.fastLo == wantLo && st.fastHi == wantHi && countExc cls d == wantExc

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tir_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} tir vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "tir differential mismatch")
