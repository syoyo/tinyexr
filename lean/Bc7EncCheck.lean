/-
  TinyEXR - BC7 full block-encoder differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc7_enc_vectors.c`
  (`enc <16 x RGBA hex> | <16 block bytes>`) and compares
  `Texcomp.bc7EncodeBlockDefault` with `tc_bc7_compress_rgba8` at the
  default options (all modes enabled, MEDIUM quality, quick = 2, no PCA).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc7EncodeAll

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexByte (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def slice (s : String) (a b : Nat) : String :=
  String.ofList (((s.toList).drop a).take (b - a))

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc7_enc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let kind := head.getD 0 ""
    let quick := !(kind == "enc1")   -- enc1 marks the non-quick (exhaustive) run
    let hexpx := head.getD 1 ""
    let px := (List.range 16).map (fun i =>
      let o := i * 8
      [hexByte (slice hexpx o (o + 2)), hexByte (slice hexpx (o + 2) (o + 4)),
       hexByte (slice hexpx (o + 4) (o + 6)), hexByte (slice hexpx (o + 6) (o + 8))])
    let got := bc7EncodeBlockQuick quick px
    let want := (List.range 16).map (fun i => hexByte (outp.getD i ""))
    if got != want then
      bad := bad + 1
      if bad <= 5 then
        IO.eprintln s!"line {idx + 1}: got {got}\n  want {want}"
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc7 encode mismatch")
