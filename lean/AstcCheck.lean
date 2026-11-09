/-
  TinyEXR - ASTC differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_vectors.c`
  (`<flag> <blockhex> | <16 x R G B A hex>`), decodes each block with
  `Texcomp.astcDecodeBlock`, and reports mismatches.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcDecode

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseHex4 (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def parseBlock (s : String) : List Nat :=
  (List.range 16).map (fun i =>
    parseHex4 ((s.drop (i * 2) |>.take 2).toString))

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) (n : Nat) : IO Bool := do
  let sections := line.splitOn "|"
  let head := sections.getD 0 ""
  let tail := sections.getD 1 ""
  let hp := fields head
  let block := parseBlock (hp.getD 1 "")
  let tp := fields tail
  let mut ok := true
  for k in List.range 16 do
    let (r, g, b, a) := astcDecodeBlock block 4 4 ⟨k % 16, Nat.mod_lt k (by decide)⟩
    let er := parseHex4 (tp.getD (k * 4 + 0) "")
    let eg := parseHex4 (tp.getD (k * 4 + 1) "")
    let eb := parseHex4 (tp.getD (k * 4 + 2) "")
    let ea := parseHex4 (tp.getD (k * 4 + 3) "")
    if r.toNat != er || g.toNat != eg || b.toNat != eb || a.toNat != ea then
      IO.eprintln s!"line {n} texel {k}: got {r.toNat} {g.toNat} {b.toNat} {a.toNat}, want {er} {eg} {eb} {ea}"
      ok := false
  return ok

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let ok ← checkLine line (idx + 1)
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc differential mismatch")
