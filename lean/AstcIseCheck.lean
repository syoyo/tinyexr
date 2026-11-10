/-
  TinyEXR - ASTC ISE encode bits differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_ise_vectors.c`
  (`I <ql> <vc> <bitOffset> | <values> | <16 bytes> | <finalBitOffset>`)
  and compares `Texcomp.astcIseEncodeBits` with `tc_astc_ise_encode_bits`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcEncode

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

def parseHexBytes (s : String) : List Nat :=
  (List.range (s.length / 2)).map (fun i =>
    let c1 := ((s.drop (i * 2)).take 1).toString
    let c2 := ((s.drop (i * 2 + 1)).take 1).toString
    let v1 := if c1 == "a" || c1 == "A" then 10
              else if c1 >= "0" && c1 <= "9" then decNat c1 else 0
    let v2 := if c2 == "a" || c2 == "A" then 10
              else if c2 >= "0" && c2 <= "9" then decNat c2 else 0
    v1 * 16 + v2)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_ise_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let ql := natAt head 1
    let vc := natAt head 2
    let bitOff := natAt head 3
    let vals := valsFrom (fields (sections.getD 1 "")) 0 vc
    let bytes := (fields (sections.getD 2 "")).map (fun s => decNat s)  -- wrong: bytes are hex
    -- parse bytes as hex pairs from the joined string
    let wantBytes := (fields (sections.getD 2 "")).map hexNat
    let wantOff := natAt (fields (sections.getD 3 "")) 0
    let out0 := List.replicate 16 0
    let (gotBytes, gotOff) := astcIseEncodeBits ql vc vals out0 bitOff 16
    if gotBytes != wantBytes || gotOff != wantOff then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} I {ql} {vc}: secs={sections.length} got {gotBytes.take 4} want {wantBytes.take 4} off {gotOff} vs {wantOff}"
  IO.println s!"{lines.length} ISE encode vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc ise encode mismatch")
