/-
  TinyEXR - BC6H encoder kernel differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc6h_kernel_vectors.c` and compares the
  Lean kernels in `Texcomp.Bc6hKernels` with the C primitives.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc6hKernels

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decInt (s : String) : Int :=
  let neg := s.startsWith "-"
  let digits := if neg then s.drop 1 else s
  let v : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  if neg then -v else v

def decNat (s : String) : Nat := (decInt s).toNat

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def f32of (s : String) : Float32 := Float32.ofBits (UInt32.ofNat (hexNat s))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc6h_kernel_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut checked := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let kind := toks.getD 0 ""
    checked := checked + 1
    if kind == "half" then
      let got := bc6hFloatToHalfBits (UInt32.ofNat (hexNat (toks.getD 1 "")))
      let want := hexNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} half {toks.getD 1 ""}: got {got}, want {want}"
    else if kind == "qu" then
      let got := bc6hQuantUf16 (UInt32.ofNat (hexNat (toks.getD 1 "")))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} qu: got {got}, want {want}"
    else if kind == "qs" then
      let got := bc6hQuantSf16 (UInt32.ofNat (hexNat (toks.getD 1 "")))
      let want := decInt (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} qs: got {got}, want {want}"
    else if kind == "uq" then
      let got := bc6hUnquantUf16ToMag (decNat (toks.getD 1 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} uq: got {got}, want {want}"
    else if kind == "usq" then
      let got := bc6hUnquantSf16ToSmag (decInt (toks.getD 1 ""))
      let want := decInt (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} usq: got {got}, want {want}"
    else if kind == "e3" then
      let a := [decNat (toks.getD 1 ""), decNat (toks.getD 2 ""), decNat (toks.getD 3 "")]
      let got := bc6hErr3Mag a (decNat (toks.getD 4 "")) (decNat (toks.getD 5 ""))
        (decNat (toks.getD 6 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} e3: got {got}, want {want}"
    else if kind == "e3s" then
      let a := [decInt (toks.getD 1 ""), decInt (toks.getD 2 ""), decInt (toks.getD 3 "")]
      let got := bc6hErr3Smag a (decInt (toks.getD 4 "")) (decInt (toks.getD 5 ""))
        (decInt (toks.getD 6 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} e3s: got {got}, want {want}"
    else if kind == "psn" then
      let got := bc6hPackSignedN (decInt (toks.getD 1 "")) (decNat (toks.getD 2 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} psn: got {got}, want {want}"
    else if kind == "ps10" then
      let got := bc6hPackSigned10 (decInt (toks.getD 1 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} ps10: got {got}, want {want}"
    else if kind == "pal" then
      let lo := [decNat (toks.getD 1 ""), decNat (toks.getD 2 ""), decNat (toks.getD 3 "")]
      let hi := [decNat (toks.getD 4 ""), decNat (toks.getD 5 ""), decNat (toks.getD 6 "")]
      let got := (bc6hPal16Uf16 lo hi).flatten.map Int.toNat
      let want := outp.map decNat
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} pal: got {got}, want {want}"
    else if kind == "sel" then
      let target := (List.range 16).map (fun i =>
        [decNat (toks.getD (1 + i * 3) ""), decNat (toks.getD (2 + i * 3) ""),
         decNat (toks.getD (3 + i * 3) "")])
      let lo := [decNat (toks.getD 49 ""), decNat (toks.getD 50 ""), decNat (toks.getD 51 "")]
      let hi := [decNat (toks.getD 52 ""), decNat (toks.getD 53 ""), decNat (toks.getD 54 "")]
      let (got, err) := bc6hChooseSelectorsUf16 target lo hi
      let want := (List.range 16).map (fun i => decNat (outp.getD i ""))
      let wantErr := decNat (outp.getD 16 "")
      if got != want || err != wantErr then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} sel: got {got} err {err}, want {want} err {wantErr}"
    else if kind == "qn" then
      let got := bc6hQuantUf16N (UInt32.ofNat (hexNat (toks.getD 1 ""))) (decNat (toks.getD 2 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} qn: got {got}, want {want}"
    else if kind == "un" then
      let got := bc6hUnquantNToMag (decNat (toks.getD 1 "")) (decNat (toks.getD 2 ""))
      let want := decNat (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} un: got {got}, want {want}"
    else if kind == "qsn" then
      let got := bc6hQuantSf16N (UInt32.ofNat (hexNat (toks.getD 1 ""))) (decNat (toks.getD 2 ""))
      let want := decInt (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} qsn: got {got}, want {want}"
    else if kind == "uns" then
      let got := bc6hUnquantNToSmag (decInt (toks.getD 1 "")) (decNat (toks.getD 2 ""))
      let want := decInt (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} uns: got {got}, want {want}"
    else if kind == "rdiv" then
      let got := bc6hRdiv (decInt (toks.getD 1 "")) (decInt (toks.getD 2 ""))
      let want := decInt (outp.getD 0 "")
      if got != want then
        bad := bad + 1
        if bad <= 8 then IO.eprintln s!"line {idx + 1} rdiv: got {got}, want {want}"
    else
      bad := bad + 1
      if bad <= 8 then IO.eprintln s!"line {idx + 1}: unknown kind {kind}"
  IO.println s!"{checked} values checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc6h kernel mismatch")
