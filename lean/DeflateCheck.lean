/-
  TinyEXR - DEFLATE payload differential checker (C vectors vs Lean model).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Deflate

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0

def parseBytes (s : String) : List UInt8 :=
  let cs := s.toList
  (List.range (cs.length / 2)).map (fun i => UInt8.ofNat (parseNat (String.ofList ((cs.drop (i * 2)).take 2))))

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 2 then true else
  match Exr.decodeZlib (parseBytes (f.getD 0 "")) with
  | some out => out == parseBytes (f.getD 1 "")
  | none => false

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/deflate_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line.take 160}"
  IO.println s!"{ls.length} DEFLATE vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "DEFLATE differential mismatch")
