/-
  TinyEXR - ASTC HDR differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_hdr_vectors.c`
  (`0 <blockhex> | <16 x R G B A hex>`), decodes each block with
  `Texcomp.astcDecodeBlockHdr`, and compares float bits.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcHdr

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseBits (s : String) : UInt32 :=
  UInt32.ofNat (s.foldl (fun acc c => acc * 16 + hexVal c) 0)

def f32 (s : String) : Float32 := Float32.ofBits (parseBits s)

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

/-- Read a 16-byte block from hex. -/
def parseBlock (s : String) : List Nat :=
  let cs := s.toList
  (List.range 16).map (fun i =>
    parseBits (String.ofList [cs.getD (i * 2) ' ', cs.getD (i * 2 + 1) ' ']) |>.toNat)

def fin16 (t : Nat) : Fin 16 := ⟨t % 16, Nat.mod_lt t (by decide)⟩

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_hdr_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let outtoks := fields (sections.getD 1 "")
    let blk := parseBlock (toks.getD 1 "")
    let ok := (List.range 16).all (fun t =>
      let texel := astcDecodeBlockHdr blk 4 4 (fin16 t)
      let (r, g, b, a) := texel
      let er := f32 (outtoks.getD (t * 4 + 0) "")
      let eg := f32 (outtoks.getD (t * 4 + 1) "")
      let eb := f32 (outtoks.getD (t * 4 + 2) "")
      let ea := f32 (outtoks.getD (t * 4 + 3) "")
      Float32.toBits r == Float32.toBits er &&
        Float32.toBits g == Float32.toBits eg &&
        Float32.toBits b == Float32.toBits eb &&
        Float32.toBits a == Float32.toBits ea)
    if !ok then
      bad := bad + 1
      let texel := astcDecodeBlockHdr blk 4 4 (fin16 0)
      IO.eprintln s!"line {idx + 1}: texel0 got {texel.1} {texel.2.1} {texel.2.2.1} {texel.2.2.2}"
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc hdr differential mismatch")
