/-
  TinyEXR - BC4/BC5 encoder differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc4_enc_vectors.c`
  (`bc4 <16 bytes> | <8>`, `bc5 <16 r> <16 g> | <16>`,
  `bc5s <16 r> <16 g> | <16>`) and compares the Lean encoders
  (`Texcomp.encodeBc4Block`, `encodeBc5Block`, `encodeBc5BlockSnorm`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc4Encode

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexByte (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def slice (s : String) (a b : Nat) : String :=
  String.ofList (((s.toList).drop a).take (b - a))

/-- Parse a run of `n` two-digit hex bytes. -/
def hexBytes (s : String) (n : Nat) : List Nat :=
  (List.range n).map (fun i => hexByte (slice s (i * 2) (i * 2 + 2)))

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc4_enc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let kind := head.getD 0 ""
    let (got, wantCount) ←
      if kind == "bc4" then
        pure (encodeBc4Block (hexBytes (head.getD 1 "") 16), 8)
      else if kind == "bc5" then
        pure (encodeBc5Block (hexBytes (head.getD 1 "") 16) (hexBytes (head.getD 2 "") 16), 16)
      else if kind == "bc5s" then
        pure (encodeBc5BlockSnorm (hexBytes (head.getD 1 "") 16) (hexBytes (head.getD 2 "") 16), 16)
      else
        pure ([], 0)
    let want := (List.range wantCount).map (fun i => hexByte (outp.getD i ""))
    if got != want then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} {kind}: got {got}, want {want}"
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc4/bc5 encode mismatch")
