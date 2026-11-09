/-
  TinyEXR - ASTC HDR endpoint pack differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_pack_vectors.c`
  (`cem11 <x0..x2> <y0..y2> | <6 bytes>` and `alpha <a0> <a1> | <2 bytes>`)
  and compares the Lean packers (`Texcomp.cem11Pack`, `Texcomp.hdrAlphaPack`)
  against the C output byte-for-byte, at colour quant level 20.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcHdrPack

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexB (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decInt (s : String) : Int :=
  let neg := s.startsWith "-"
  let digits := if neg then s.drop 1 else s
  let v : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  if neg then -v else v

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_pack_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let inToks := fields (sections.getD 0 "")
    let outToks := fields (sections.getD 1 "")
    let kind := inToks.getD 0 ""
    if kind == "cem11" then
      let a := (List.range 3).map (fun i => (decInt (inToks.getD (1 + i) "")).toNat)
      let b := (List.range 3).map (fun i => (decInt (inToks.getD (4 + i) "")).toNat)
      let (p0, p1, p2, p3, p4, p5) := cem11Pack a b 20
      let want := (List.range 6).map (fun i => hexB (outToks.getD i ""))
      let got := [p0, p1, p2, p3, p4, p5]
      if got != want then
        bad := bad + 1
        if bad <= 10 then
          IO.eprintln s!"line {idx + 1} cem11 {a} {b}: got {got}, want {want}"
    else if kind == "cem7" then
      let a := (List.range 3).map (fun i => (decInt (inToks.getD (1 + i) "")).toNat)
      let b := (List.range 3).map (fun i => (decInt (inToks.getD (4 + i) "")).toNat)
      let (p0, p1, p2, p3) := cem7Pack a b 20
      let want := (List.range 4).map (fun i => hexB (outToks.getD i ""))
      let got := [p0, p1, p2, p3]
      if got != want then
        bad := bad + 1
        if bad <= 10 then
          IO.eprintln s!"line {idx + 1} cem7 {a} {b}: got {got}, want {want}"
    else if kind == "alpha" then
      let a0 := decInt (inToks.getD 1 "")
      let a1 := decInt (inToks.getD 2 "")
      let (p0, p1) := hdrAlphaPack a0 a1
      let want := (List.range 2).map (fun i => hexB (outToks.getD i ""))
      if [p0, p1] != want then
        bad := bad + 1
        if bad <= 10 then
          IO.eprintln s!"line {idx + 1} alpha {a0} {a1}: got {[p0, p1]}, want {want}"
    else
      IO.eprintln s!"line {idx + 1}: unknown kind {kind}"
      bad := bad + 1
  IO.println s!"{lines.length} vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc pack differential mismatch")
