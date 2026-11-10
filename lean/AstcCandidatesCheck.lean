/-
  TinyEXR - ASTC block-mode candidate list differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_candidates_vectors.c`
  (`C` headers, `K` candidates) and compares
  `Texcomp.astcBuildBlockModeCandidates` /
  `astcBuildDualBlockModeCandidates` (order and ranks) with the C
  `tc_astc_build_*_block_mode_candidates`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcCandidates

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

/-- One expected candidate: `(idx, wx, wy, quant, bits, rank)`. -/
abbrev CandRow := Nat × Nat × Nat × Nat × Nat × Nat

def rowsOf (bx bh dual : Nat) (got : List AstcEncMode) : List Nat × List Nat :=
  let fp := astcFootprintIndex bx bh
  let rows := got.map (fun m =>
    [m.wx, m.wy, m.quant, m.weightBits, astcCandidateRank m fp dual])
  (rows.map (fun r => r.length), rows.flatten)

structure CandAcc where
  hdr : List Nat := []
  want : List CandRow := []
  configs : Nat := 0
  total : Nat := 0
  bad : Nat := 0
  notes : List String := []

def flush (a : CandAcc) : CandAcc :=
  if a.hdr.isEmpty then a
  else
    let bx := a.hdr.getD 0 0
    let bh := a.hdr.getD 1 0
    let q := a.hdr.getD 2 0
    let eb := a.hdr.getD 3 0
    let dual := a.hdr.getD 4 0
    let n := a.hdr.getD 5 0
    let got := if dual != 0 then astcBuildDualBlockModeCandidates bx bh eb q
               else astcBuildBlockModeCandidates bx bh eb q
    let (_, flat) := rowsOf bx bh dual got
    let wantFlat := a.want.foldl (fun acc w =>
      acc ++ [w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2]) []
    let ok := got.length == n && flat == wantFlat
    { a with hdr := [], want := [], configs := a.configs + 1, total := a.total + n,
             bad := a.bad + (if ok then 0 else 1),
             notes := if ok then a.notes
                      else a.notes ++ [s!"{bx}x{bh} q{q} eb{eb} dual{dual}: got {got.length}, want {n}"] }

def step (a : CandAcc) (line : String) : CandAcc :=
  let f := fields line
  if f.getD 0 "" == "C" then
    let a := flush a
    { a with hdr := (List.range 6).map (fun i => natAt f (1 + i)) }
  else if f.getD 0 "" == "K" then
    { a with want := a.want ++ [(natAt f 1, natAt f 2, natAt f 3, natAt f 4,
                                 natAt f 5, natAt f 6)] }
  else a

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_candidates_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let final := flush (lines.foldl step {})
  for note in final.notes.take 6 do
    IO.eprintln note
  IO.println s!"{final.configs} candidate lists ({final.total} entries) checked, {final.bad} mismatches"
  if final.bad != 0 then
    throw (IO.userError "astc candidates mismatch")
