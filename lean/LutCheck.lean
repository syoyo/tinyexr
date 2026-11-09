/-
  TinyEXR - LUT-file differential checker (C vs Lean).
  Reads vectors from `test/v3/lutfile_vectors.c`
  (`<kind> lut1d|lut3d <params> <data> <in> | <out>`), applies the Lean
  `applyLut1d` / `applyLut3dTrilinear` kernels, and reports mismatches.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.LutFile

open Tocio

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseBits (s : String) : UInt32 :=
  UInt32.ofNat (s.foldl (fun acc c => acc * 16 + hexVal c) 0)

def f32 (s : String) : Float32 := Float32.ofBits (parseBits s)

def decNum (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) (n : Nat) : IO Bool := do
  let sections := line.splitOn "|"
  let head := sections.getD 0 ""
  let outp := sections.getD 1 ""
  let hp := fields head
  let op_ := fields outp
  let kind := hp.getD 0 ""
  let lutKind := hp.getD 1 ""
  let mut ok := true
  if lutKind == "lut1d" then
    let length := decNum (hp.getD 2 "")
    let channels := decNum (hp.getD 3 "")
    let dmin := f32 (hp.getD 4 "")
    let dmax := f32 (hp.getD 5 "")
    let ndata := length * channels
    let data := (List.range ndata).map (fun i => f32 (hp.getD (i + 7) ""))
    let npix := op_.length / 4
    for k in List.range npix do
      let r := f32 (hp.getD (7 + ndata + (k * 4 + 0)) "")
      let g := f32 (hp.getD (7 + ndata + (k * 4 + 1)) "")
      let b := f32 (hp.getD (7 + ndata + (k * 4 + 2)) "")
      let a := f32 (hp.getD (7 + ndata + (k * 4 + 3)) "")
      let cor := applyLut1d length channels dmin dmax LutInterp.linear data (r, g, b)
      let (cr, cg, cb) := cor
      let er := f32 (op_.getD (k * 4 + 0) "")
      let eg := f32 (op_.getD (k * 4 + 1) "")
      let eb := f32 (op_.getD (k * 4 + 2) "")
      let ea := f32 (op_.getD (k * 4 + 3) "")
      if Float32.toBits cr != Float32.toBits er ||
         Float32.toBits cg != Float32.toBits eg ||
         Float32.toBits cb != Float32.toBits eb ||
         Float32.toBits a != Float32.toBits ea then
        IO.eprintln s!"line {n} lut1d pixel {k}: got {cr} {cg} {cb} {a}, want {er} {eg} {eb} {ea}"
        ok := false
  else if lutKind == "lut3d" then
    let size := decNum (hp.getD 2 "")
    let dmin := f32 (hp.getD 3 "")
    let dmax := f32 (hp.getD 4 "")
    let ndata := size * size * size * 3
    if kind == "cube3dt" then
      -- tetrahedral variant: interp token present, data at offset 6
      let data := (List.range ndata).map (fun i => f32 (hp.getD (i + 6) ""))
      let npix := op_.length / 4
      for k in List.range npix do
        let r := f32 (hp.getD (6 + ndata + (k * 4 + 0)) "")
        let g := f32 (hp.getD (6 + ndata + (k * 4 + 1)) "")
        let b := f32 (hp.getD (6 + ndata + (k * 4 + 2)) "")
        let a := f32 (hp.getD (6 + ndata + (k * 4 + 3)) "")
        let cor := applyLut3dTet size [dmin, dmin, dmin] [dmax, dmax, dmax] data (r, g, b)
        let (cr, cg, cb) := cor
        let er := f32 (op_.getD (k * 4 + 0) "")
        let eg := f32 (op_.getD (k * 4 + 1) "")
        let eb := f32 (op_.getD (k * 4 + 2) "")
        let ea := f32 (op_.getD (k * 4 + 3) "")
        if Float32.toBits cr != Float32.toBits er ||
           Float32.toBits cg != Float32.toBits eg ||
           Float32.toBits cb != Float32.toBits eb ||
           Float32.toBits a != Float32.toBits ea then
          IO.eprintln s!"line {n} lut3dt pixel {k}: got {cr} {cg} {cb} {a}, want {er} {eg} {eb} {ea}"
          ok := false
    else
      let data := (List.range ndata).map (fun i => f32 (hp.getD (i + 6) ""))
      let npix := op_.length / 4
      for k in List.range npix do
        let r := f32 (hp.getD (6 + ndata + (k * 4 + 0)) "")
        let g := f32 (hp.getD (6 + ndata + (k * 4 + 1)) "")
        let b := f32 (hp.getD (6 + ndata + (k * 4 + 2)) "")
        let a := f32 (hp.getD (6 + ndata + (k * 4 + 3)) "")
        let cor := applyLut3dTrilinear size [dmin, dmin, dmin] [dmax, dmax, dmax] data (r, g, b)
        let (cr, cg, cb) := cor
        let er := f32 (op_.getD (k * 4 + 0) "")
        let eg := f32 (op_.getD (k * 4 + 1) "")
        let eb := f32 (op_.getD (k * 4 + 2) "")
        let ea := f32 (op_.getD (k * 4 + 3) "")
        if Float32.toBits cr != Float32.toBits er ||
           Float32.toBits cg != Float32.toBits eg ||
           Float32.toBits cb != Float32.toBits eb ||
           Float32.toBits a != Float32.toBits ea then
          IO.eprintln s!"line {n} lut3d pixel {k}: got {cr} {cg} {cb} {a}, want {er} {eg} {eb} {ea}"
          ok := false
  return ok

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/lutfile_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let ok ← checkLine line (idx + 1)
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} lines checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "lutfile differential mismatch")
