/-
  TinyEXR - BC6H mode-0 encoder differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc6h_mode0_vectors.c`
  (`m0 <16x3 float bits> | ok <16 bytes> <sse>` or `... | fail`) and
  compares `Texcomp.bc6hEncMode0Uf16` with the C `tc_bc6h_mode0_uf16`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc6hEncMode0

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc6h_mode0_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut okCount := 0
  let mut failCount := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let px := (List.range 16).map (fun i =>
      (List.range 3).map (fun c =>
        UInt32.ofNat (hexNat (toks.getD (1 + i * 3 + c) ""))))
    let status := outp.getD 0 ""
    match bc6hEncMode0Uf16 px with
    | none =>
      if status == "fail" then failCount := failCount + 1
      else
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1}: C ok, Lean fail"
    | some (bytes, err) =>
      if status != "ok" then
        bad := bad + 1
        if bad <= 6 then IO.eprintln s!"line {idx + 1}: C fail, Lean ok"
      else
        okCount := okCount + 1
        let want := (List.range 16).map (fun i => hexNat (outp.getD (1 + i) ""))
        let wantErr := decNat (outp.getD 17 "")
        if bytes != want || err != wantErr then
          bad := bad + 1
          if bad <= 6 then
            IO.eprintln s!"line {idx + 1}: got {bytes} err {err}\n  want {want} err {wantErr}"
  IO.println s!"{lines.length} blocks checked ({okCount} encoded, {failCount} no-fit), {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc6h mode0 mismatch")
