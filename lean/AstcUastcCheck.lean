/-
  TinyEXR - ASTC UASTC LDR block encoder differential checker.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcUastc

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")
def valsFrom (xs : List String) (start n : Nat) : List Nat := (List.range n).map (fun i => natAt xs (start + i))
def blockFrom (xs : List String) (start count : Nat) : List (List Nat) := (List.range count).map (fun i => valsFrom xs (start + i * 4) 4)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_uastc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let bx := natAt head 1
    let by_ := natAt head 2
    let quality := natAt head 3
    let count := bx * by_
    let block := blockFrom head 4 count
    let want := ((fields (sections.getD 1 "")).take 16).map hexNat
    let got := astcEncodeUastcLdrBlock block count quality bx by_
    if got != want then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1}: bx {bx} by {by_} q {quality}"
        IO.eprintln s!"  got  {repr got}"
        IO.eprintln s!"  want {want}"
  IO.println s!"{lines.length} UASTC blocks checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "astc uastc mismatch")
