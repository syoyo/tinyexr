/-
  TinyEXR - BC6H per-block mode-selection differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc6h_block_vectors.c`
  (`u|s <48 float bits> | <16 bytes>`) and compares
  `Texcomp.bc6hEncodeBlockUf16` / `bc6hEncodeBlockSf16` with the C
  `tc_encode_bc6h_block_uf16` / `tc_encode_bc6h_block_sf16`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc6hEncodeBlock

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc6h_block_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let kind := toks.getD 0 ""
    let px := (List.range 16).map (fun i =>
      (List.range 3).map (fun c =>
        UInt32.ofNat (hexNat (toks.getD (1 + i * 3 + c) ""))))
    let got := if kind == "u" then bc6hEncodeBlockUf16 px else bc6hEncodeBlockSf16 px
    let want := (List.range 16).map (fun i => hexNat (outp.getD i ""))
    if got != want then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} {kind}: got {got}\n  want {want}"
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc6h block driver mismatch")
