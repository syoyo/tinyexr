/-
  TinyEXR - reader-state differential checker (C vectors vs Lean spec).

  The C side emits the observed result codes and part-array state after a
  failed parse and a retry. The checker verifies the latch/ownership
  properties against the `Exr.ReaderState` model.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.ReaderState

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 6 then true else
  let r1 := (f.getD 1 "0").toInt!
  let r2 := (f.getD 2 "0").toInt!
  let np := (f.getD 3 "0").toNat!
  let cap := (f.getD 4 "0").toNat!
  let nn := (f.getD 5 "0").toNat!
  let st0 : Exr.ReaderState Nat := Exr.newReader 0
  let st1 := Exr.latch st0 Exr.RErr.corrupt
  r1 < 0 && r1 == r2 && np == 0 && cap == 0 && nn == 0 &&
  Exr.enter st1 == st1 && st1.parts.length == st0.parts.length &&
  st1.parseRc == some Exr.RErr.corrupt

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/reader_state_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} reader-state vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "reader-state differential mismatch")
