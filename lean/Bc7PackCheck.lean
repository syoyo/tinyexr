/-
  TinyEXR - BC7 pack/palette differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc7_pack_vectors.c` and compares
  `Texcomp.bc7PackCandidate` / `bc7FillPalette` with the C
  `tc_pack_candidate` / `tc_fill_palette` for randomly generated
  candidates across all 8 block modes.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc7Encode

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexByte (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

/-- Parse a candidate from `<mode> <part> <isel> <rot> <12 lo> <12 hi>
  <6 pbits> <16 sel> <16 asel>` starting at index 1. -/
def parseCand (t : List String) : Bc7Candidate :=
  let g := fun i => decNat (t.getD i "")
  let lo := (List.range 3).map (fun s => (List.range 4).map (fun k => g (5 + s * 4 + k)))
  let hi := (List.range 3).map (fun s => (List.range 4).map (fun k => g (17 + s * 4 + k)))
  let pb := (List.range 3).map (fun s => (List.range 2).map (fun k => g (29 + s * 2 + k)))
  let sel := (List.range 16).map (fun i => g (35 + i))
  let asel := (List.range 16).map (fun i => g (51 + i))
  { mode := g 1, partition := g 2, indexSelector := g 3, rotation := g 4,
    lo := lo, hi := hi, pbits := pb, selectors := sel, alphaSelectors := asel }

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc7_pack_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut checked := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let outp := fields (sections.getD 1 "")
    let kind := toks.getD 0 ""
    let c := parseCand toks
    if kind == "bc7" then
      let got := bc7PackCandidate c
      let want := (List.range 16).map (fun i => hexByte (outp.getD i ""))
      checked := checked + 1
      if got != want then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} mode {c.mode} part {c.partition} isel {c.indexSelector}: got {got}, want {want}"
    else if kind == "pal" then
      let got := (bc7FillPalette c).flatten.flatten
      let want := outp.map decNat
      checked := checked + 1
      if got != want then
        bad := bad + 1
        if bad <= 6 then
          IO.eprintln s!"line {idx + 1} pal mode {c.mode} part {c.partition}:\n  got  {got.take 40}\n  want {want.take 40}"
    else
      IO.eprintln s!"line {idx + 1}: unknown kind {kind}"
      bad := bad + 1
  IO.println s!"{checked} candidates checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "bc7 pack differential mismatch")
