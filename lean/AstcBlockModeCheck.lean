/-
  TinyEXR - ASTC encoder block-mode differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_blockmode_vectors.c`
  (`M <mode> | <ok> <wx> <wy> <quant> <bits> <dual>`) and compares
  `Texcomp.astcEncBlockMode` with `tc_astc_decode_block_mode_2d`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcBlockMode

open Texcomp

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_blockmode_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut okCount := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let t2 := fields (sections.getD 1 "")
    let mode := natAt head 1
    let ok := natAt t2 0 != 0
    let got := astcEncBlockMode mode
    let good :=
      if ok then
        match got with
        | some m =>
          m.wx == natAt t2 1 && m.wy == natAt t2 2 && m.quant == natAt t2 3 &&
            m.weightBits == natAt t2 4 && m.dual == natAt t2 5
        | none => false
      else got.isNone
    if !good then
      bad := bad + 1
      if bad <= 6 then IO.eprintln s!"line {idx + 1} mode {mode}: got {repr got}, want ok {ok}"
    if ok then okCount := okCount + 1
  IO.println s!"{lines.length} block modes ({okCount} admissible) checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc block mode mismatch")
