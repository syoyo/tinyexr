/-
  TinyEXR - ASTC HDR image-level encoder differential checker.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcHdrEnc

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
  let path := args.getD 0 "/tmp/opencode/astc_hdrimg_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let tag := (String.Pos.Raw.get? (head.getD 0 " ") (String.Pos.Raw.mk 1)) |>.getD ' '
    let w := natAt head 1
    let h := natAt head 2
    let nch := if tag == 'A' then 4 else 3
    let n := w * h * nch
    let pix : List (List Nat) := (List.range (w * h)).map (fun i =>
      (List.range nch).map (fun c => hexNat (head.getD (3 + i * nch + c) "0")))
    let want := ((fields (sections.getD 1 "")).map hexNat)
    let got :=
      if tag == 'A' then astcEncodeHdrRgbaF pix w h
      else astcEncodeHdrRgbF pix w h
    if got != want then
      bad := bad + 1
      if bad <= 3 then
        IO.eprintln s!"line {idx + 1} tag {tag} w {w} h {h}: got {got.length} bytes, want {want.length}"
        IO.eprintln s!"  got  {(got.take 20)}"
        IO.eprintln s!"  want {(want.take 20)}"
  IO.println s!"{lines.length} HDR images checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "astc hdr image mismatch")
