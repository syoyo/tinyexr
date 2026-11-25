/-
  TinyEXR - B44 perceptual table boundary differential checker.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.B44Tables

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def hv (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def pn (s : String) : Nat := s.foldl (fun a c => a * 16 + hv c) 0

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 3 then false else
    let i := pn (f.getD 0 "0")
    let e := UInt16.ofNat (pn (f.getD 1 "0"))
    let l := UInt16.ofNat (pn (f.getD 2 "0"))
    (f.getD 1 "-" == "-" || Exr.B44.expTableBoundary i == e) &&
      (f.getD 2 "-" == "-" || Exr.B44.logTableBoundary i == l)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/b44_table_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := (content.splitOn "\n").filter (fun s => s != "")
  let mut bad := 0
  for (i, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 5 then IO.println s!"mismatch at line {i + 1}: {line}"
  IO.println s!"{ls.length} B44 table boundary vectors checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "B44 table boundary mismatch")
