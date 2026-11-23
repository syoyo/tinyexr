/-
  TinyEXR - JPH wrapper differential checker (C vectors vs Lean model).

  Reads marker/geometry vectors emitted by `test/v3/jph_vectors.c`, parses
  the corresponding fixture with the Lean `Exr.scanJph` model and compares
  the marker sequence, SIZ geometry and profile verdict.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Jph

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0

def findSoc (data : List UInt8) : Option Nat :=
  (List.range data.length).find? (fun i =>
    i + 3 < data.length && data.getD i 0 == 0xff &&
    data.getD (i + 1) 0 == 0x4f && data.getD (i + 2) 0 == 0xff &&
    data.getD (i + 3) 0 == 0x51)

def checkLine (line : String) : IO Bool := do
  let f := fields line
  if f.length < 11 then return true else
  let path := f.getD 0 ""
  let rest := f.drop 1
  let wantMarks := (rest.take (rest.length - 9)).map parseNat
  let want := (rest.drop (rest.length - 9)).map (fun s => s.toNat!)
  try
    let bytes ← IO.FS.readBinFile path
    let data := bytes.toList
    match findSoc data with
    | none => return false
    | some i =>
        match Exr.scanJph (data.drop i) with
        | none => return false
        | some p =>
            let gotMarks := p.marks.map Exr.markCode
            let s := p.siz
            let got := [s.xsiz, s.ysiz, s.csiz, s.xtsiz, s.ytsiz,
                        Exr.jphTileCount s,
                        (p.cod.getD Exr.defaultCod).ndecomp,
                        p.qcdCount.getD 0,
                        if Exr.jphProfileValid p then 1 else 0]
            return (gotMarks == wantMarks && got == want)
  catch _ => return false

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/jph_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    let ok ← checkLine line
    if !ok then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} JPH vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "JPH differential mismatch")
