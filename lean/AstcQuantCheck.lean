/-
  TinyEXR - ASTC colour-quantizer differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_quant_vectors.c`
  (`quant <level> <256 values>` and `edges <v...>`) and compares
  `Texcomp.hdrColorRoundtrip` with `tc_astc_hdr_color_roundtrip` for every
  level 0..20 and every input value.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcColorQuant

open Texcomp

def decInt (s : String) : Int :=
  let neg := s.startsWith "-"
  let digits := if neg then s.drop 1 else s
  let v : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  if neg then -v else v

/-- C clamps `value < 0` to 0 before the level dispatch. -/
def cInput (v : Int) : Nat :=
  let v := if v < 0 then 0 else v
  let v := if v > 255 then 255 else v
  v.toNat

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_quant_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut checked := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let toks := fields line
    let kind := toks.getD 0 ""
    if kind == "quant" then
      let qm := (decInt (toks.getD 1 "")).toNat
      for i in List.range 256 do
        let want := (decInt (toks.getD (2 + i) "")).toNat
        let got := hdrColorRoundtrip qm i
        checked := checked + 1
        if got != want then
          bad := bad + 1
          if bad <= 8 then
            IO.eprintln s!"line {idx + 1} level {qm} value {i}: got {got}, want {want}"
    else if kind == "edges" then
      -- quartets of (level, input) printed as 3 entries per level; the
      -- generator walks levels 0,4,8,..,20 with inputs -7,255,4096.
      let mut j := 1
      for l in List.range 6 do
        let qm := l * 4
        for v in [-7, 255, 4096] do
          let want := (decInt (toks.getD j "")).toNat
          let got := hdrColorRoundtrip qm (cInput v)
          checked := checked + 1
          if got != want then
            bad := bad + 1
            if bad <= 8 then
              IO.eprintln s!"edges level {qm} input {v}: got {got}, want {want}"
          j := j + 1
    else
      IO.eprintln s!"line {idx + 1}: unknown kind {kind}"
      bad := bad + 1
  IO.println s!"{checked} values checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "astc quant differential mismatch")
