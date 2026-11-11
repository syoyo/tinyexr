/-
  TinyEXR - ASTC LDR image-level decoder differential checker.

  Replays the C-generated vectors (test/v3/astc_ldrdec_vectors.c) against
  `astcDecodeImageRgba8` and requires bit-identical output (and matching
  success/failure).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcLdrImgDec

open Texcomp

set_option linter.unusedVariables false

def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def natAt (xs : List String) (i : Nat) : Nat :=
  decNat (xs.getD i "0")
where
  decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_ldrdec_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let w := natAt head 1
    let h := natAt head 2
    let bdx := natAt head 3
    let bdy := natAt head 4
    let wantOk := natAt head 5 != 0
    let blocksz := head.length - 6
    let blocks : List (List Nat) :=
      (List.range ((head.length - 6) / 16)).map (fun i =>
        (List.range 16).map (fun c => hexNat (head.getD (6 + i * 16 + c) "0")))
    let rgba := ((fields (sections.getD 1 "")).map hexNat)
    let got := astcDecodeImageRgba8 blocks w h bdx bdy
    let ok :=
      if wantOk then
        match got with
        | some img =>
          let flat := img.foldl (fun acc t => acc ++ t) []
          flat == rgba
        | none => false
      else
        got.isNone
    if !ok then
      bad := bad + 1
      if bad <= 4 then
        IO.eprintln s!"line {idx + 1} {w}x{h} {bdx}x{bdy} wantOk {wantOk} got {repr got}"
    if wantOk then pure ()
  IO.println s!"{lines.length} LDR decode images checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "astc ldr decode mismatch")
