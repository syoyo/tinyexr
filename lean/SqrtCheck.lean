/-
  TinyEXR - correctly-rounded sqrtf differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/sqrt_vectors.c`
  (`sqrt <input bits> <exact bits> <libm bits>`) and compares
  `Tocio.sqrtfExactBits` with the freestanding `toc_sqrtf_exact`. The
  generator itself asserts that the C implementation equals libm's
  `sqrtf` on every input, so this also pins the Lean model to libm.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Math

open Tocio

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
  let path := args.getD 0 "/tmp/opencode/sqrt_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let toks := fields line
    let u := UInt32.ofNat (hexNat (toks.getD 1 ""))
    let want := hexNat (toks.getD 2 "")
    let got := (sqrtfExactBits u).toNat
    if got != want then
      bad := bad + 1
      if bad <= 8 then
        IO.eprintln s!"line {idx + 1} sqrt {toks.getD 1 ""}: got {got}, want {want}"
  IO.println s!"{lines.length} sqrt inputs checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "sqrtf exact mismatch")
