/-
  TinyEXR - ASTC LDR image-level compress driver differential checker.

  Replays the C-generated vectors (test/v3/astc_ldrimg_vectors.c) against
  `astcCompressRgba8` and requires bit-identical output.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcLdrImg

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
  let path := args.getD 0 "/tmp/opencode/astc_ldrimg_vectors.txt"
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
    let quality := natAt head 5
    let uastc := natAt head 6
    let n := w * h * 4
    let pix : List (List Nat) := (List.range (w * h)).map (fun i =>
      (List.range 4).map (fun c => hexNat (head.getD (7 + i * 4 + c) "0")))
    let want := ((fields (sections.getD 1 "")).map hexNat)
    let got := astcCompressRgba8 pix w h bdx bdy quality uastc
    if got != want then
      bad := bad + 1
      if bad <= 3 then
        IO.eprintln s!"line {idx + 1} w {w} h {h} q {quality} uastc {uastc}: got {got.length} bytes, want {want.length}"
        IO.eprintln s!"  got  {(got.take 20)}"
        IO.eprintln s!"  want {(want.take 20)}"
  IO.println s!"{lines.length} LDR images checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "astc ldr image mismatch")
