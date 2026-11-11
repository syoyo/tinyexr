/-
  TinyEXR - ASTC HDR block encoder differential checker.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcHdrEnc

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
def decInt (s : String) : Int :=
  if s.startsWith "-" then -Int.ofNat (decNat (s.drop 1).toString)
  else Int.ofNat (decNat s)def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")
def intAt (xs : List String) (i : Nat) : Int := decInt (xs.getD i "0")
def intsFrom (xs : List String) (start n : Nat) : List Int :=
  (List.range n).map (fun i => intAt xs (start + i))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_hdrenc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let tag := (String.Pos.Raw.get? (head.getD 0 " ")
      (String.Pos.Raw.mk 1)) |>.getD ' '
    let nch : Nat := if tag == '4' then 4 else 3
    let lns := ((List.range 16).map (fun i =>
      intsFrom head (1 + i * nch) nch))
    let t1 := fields (sections.getD 1 "")
    let wantOk := natAt t1 0 != 0
    let got : Option (List Nat × Nat) :=
      if tag == '1' then astcEncodeHdrCem11Block lns
      else if tag == '2' then astcEncodeHdrCem11TwoSubsetBlock lns
      else if tag == '3' then astcEncodeHdrCem7Block lns
      else astcEncodeHdrCem15Block ((List.range 16).map (fun i =>
        intsFrom head (1 + i * 4) 4))
    let ok :=
      if wantOk then
        match got with
        | some (bytes, sse) =>
          let wantBytes := ((t1.drop 1).take 16).map hexNat
          let wantSse := natAt t1 17
          bytes == wantBytes && sse == wantSse
        | none => false
      else
        got.isNone
    if !ok then
      bad := bad + 1
      if bad <= 6 then IO.eprintln s!"line {idx + 1} tag {tag}: got {repr got} wantOk {wantOk}"
    if !wantOk then pure ()
  IO.println s!"{lines.length} HDR encoder blocks checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "astc hdr encoder mismatch")
