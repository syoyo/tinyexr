/-
  TinyEXR - texcomp uni differential checker (C writer vs Lean model).

  Line format (test/v3/astc_uni_vectors.c):
    U <w> <h> <ok> <compress 0/1> | <rgba> | <uni blocks> | <decoded rgba>
  compress=1: <rgba> is the encoder input and <uni blocks> its C output.
  compress=0: <uni blocks> are random bytes; <ok>/<decoded> come from the C
  decoder. The ASTC transcode (byte copy) is checked on every line.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Uni

open Texcomp

def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/astc_uni_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sec := line.splitOn "|"
    let head := fields (sec.getD 0 "")
    let w := decNat (head.getD 1 "0")
    let h := decNat (head.getD 2 "0")
    let wantOk := decNat (head.getD 3 "0") != 0
    let comp := decNat (head.getD 4 "0") != 0
    let rgba := (fields (sec.getD 1 "")).map hexNat
    let uni := (fields (sec.getD 2 "")).map hexNat
    let dec := (fields (sec.getD 3 "")).map hexNat
    let mut okLine := true
    if comp then
      let pix := (List.range (w * h)).map (fun i => (List.range 4).map (fun c => rgba.getD (i * 4 + c) 0))
      okLine := okLine && (uniCompressRgba8 pix w h == uni)
    okLine := okLine && (uni.length == uniCompressedSize w h)
    okLine := okLine && (uniTranscodeAstc uni w h == uni)
    match uniDecompressRgba8 uni w h with
    | some img => okLine := okLine && wantOk && (img.foldl (· ++ ·) [] == dec)
    | none => okLine := okLine && !wantOk
    if !okLine then
      bad := bad + 1
      if bad <= 4 then IO.eprintln s!"line {idx + 1} {w}x{h} compress={comp} wantOk={wantOk}: mismatch"
  IO.println s!"{lines.length} uni images checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "uni mismatch")
