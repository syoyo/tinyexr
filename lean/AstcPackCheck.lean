/-
  TinyEXR - ASTC pack-partition-RGB differential checker.

  Reads vectors emitted by `test/v3/astc_pack_vectors.c`
  (`P <blockMode> <partitionCount> <piSeed> <endpointFormatsMatched>
  <endpointHighpartSize> <endpointFormats...> <colorQuantMethod>
  <endpointValueCount> <weightBits> <weightbuf16> <colorValues...> | <16 bytes>`)
  and compares `Texcomp.astcPackPartitionRgb` with
  `tc_astc_pack_partition_rgb`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcPack

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

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_pack_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let blockMode := natAt head 1
    let partitionCount := natAt head 2
    let piSeed := natAt head 3
    let matched := natAt head 4
    let endpointHighpartSize := natAt head 5
    let endpointFormats := valsFrom head 6 partitionCount
    let colorQuantMethod := natAt head (6 + partitionCount)
    let endpointValueCount := natAt head (7 + partitionCount)
    let weightBits := natAt head (8 + partitionCount)
    let weightbufStart := 9 + partitionCount
    let weightbuf := valsFrom head weightbufStart 16
    let colorValuesStart := weightbufStart + 16
    let colorValues := valsFrom head colorValuesStart endpointValueCount
    let wantBytes := (fields (sections.getD 1 "")).map hexNat
    let got := astcPackPartitionRgb blockMode partitionCount piSeed
      matched endpointFormats endpointHighpartSize colorValues
      weightbuf colorQuantMethod endpointValueCount weightBits
    if got != wantBytes then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1}: mismatch got {got.take 4} want {wantBytes.take 4}"
  IO.println s!"{lines.length} pack vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc pack mismatch")