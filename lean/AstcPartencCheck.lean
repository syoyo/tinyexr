/-
  TinyEXR - ASTC partition RGB block encoder differential checker.

  Reads vectors emitted by `test/v3/astc_partenc_vectors.c`
  (`R <pc> <bx> <by> <quality> <block 4*count> | <ok> <16 bytes> <err>`)
  and compares `Texcomp.astcEncodePartitionRgbBlock` with
  `tc_encode_astc_partition_rgb_block`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcPartitionRgb

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def valsFrom (xs : List String) (start n : Nat) : List Nat :=
  (List.range n).map (fun i => natAt xs (start + i))

def blockFrom (xs : List String) (start count : Nat) : List (List Nat) :=
  (List.range count).map (fun i => valsFrom xs (start + i * 4) 4)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_partenc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut okCount := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let pc := natAt head 1
    let bx := natAt head 2
    let bh := natAt head 3
    let quality := natAt head 4
    let count := bx * bh
    let block := blockFrom head 5 count
    let t1 := fields (sections.getD 1 "")
    let wantOk := natAt t1 0 != 0
    let got := astcEncodePartitionRgbBlock block count pc quality bx bh
    let ok :=
      if wantOk then
        match got with
        | some (bytes, err) =>
          let wantBytes := ((t1.drop 1).take 16).map hexNat
          let wantErr := natAt t1 17
          bytes == wantBytes && err == wantErr
        | none => false
      else
        got.isNone
    if !ok then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} pc{pc} {bx}x{bh} q{quality} got {repr got} wantOk {wantOk}"
    if wantOk then okCount := okCount + 1
  IO.println s!"{lines.length} partition RGB blocks checked ({okCount} successful), {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc partition rgb mismatch")
