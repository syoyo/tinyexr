/-
  TinyEXR - Tocio op differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/tocio_vectors.c` (op parameters and
  Float32 pixel buffers as hex bit patterns), applies the Lean op
  kernels (`Tocio.Ops` + `Tocio.FixedFunc`), and reports mismatches
  bit-by-bit.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Ops
import Tocio.FixedFunc
import Tocio.Op

open Tocio

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

/-- Compare six Float32 triples and report. -/
def cmp4 (cor : Float32 × Float32 × Float32 × Float32)
    (op_ : List String) (kind : String) (n : Nat) (k : Nat) : IO Bool := do
  let er := f32 (op_.getD (k * 4 + 0) "")
  let eg := f32 (op_.getD (k * 4 + 1) "")
  let eb := f32 (op_.getD (k * 4 + 2) "")
  let ea := f32 (op_.getD (k * 4 + 3) "")
  if Float32.toBits cor.1 != Float32.toBits er ||
     Float32.toBits cor.2.1 != Float32.toBits eg ||
     Float32.toBits cor.2.2.1 != Float32.toBits eb ||
     Float32.toBits cor.2.2.2 != Float32.toBits ea then
    IO.eprintln s!"line {n} {kind} pixel {k}: got {cor.1} {cor.2.1} {cor.2.2.1} {cor.2.2.2}, want {er} {eg} {eb} {ea}"
    return false
  return true

def checkLine (line : String) (n : Nat) : IO Bool := do
  let sections := line.splitOn "|"
  let head := sections.getD 0 ""
  let inp := sections.getD 1 ""
  let outp := sections.getD 2 ""
  let hp := fields head
  let ip := fields inp
  let op_ := fields outp
  let kind := hp.getD 0 ""
  let mut ok := true
  if kind == "matrix" then
    let m := (List.range 16).map (fun i => f32 (hp.getD (i + 1) ""))
    let off := (List.range 4).map (fun i => f32 (hp.getD (i + 17) ""))
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyMatrix m off px) op_ "matrix" n k) then ok := false
  else if kind == "range" then
    let scale := (List.range 4).map (fun i => f32 (hp.getD (i + 1) ""))
    let off := (List.range 4).map (fun i => f32 (hp.getD (i + 5) ""))
    let vmin := (List.range 4).map (fun i => f32 (hp.getD (i + 9) ""))
    let vmax := (List.range 4).map (fun i => f32 (hp.getD (i + 13) ""))
    let clo := (hp.getD 17 "") == "1"
    let chi := (hp.getD 18 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyRange scale off vmin vmax clo chi px) op_ "range" n k) then ok := false
  else if kind == "exponent" then
    let e := (List.range 4).map (fun i => f32 (hp.getD (i + 1) ""))
    let mirror := (hp.getD 5 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyExponent e mirror 4 px) op_ "exponent" n k) then ok := false
  else if kind == "log" then
    let base := f32 (hp.getD 1 "")
    let logS := (List.range 3).map (fun i => f32 (hp.getD (i + 2) ""))
    let logO := (List.range 3).map (fun i => f32 (hp.getD (i + 5) ""))
    let linS := (List.range 3).map (fun i => f32 (hp.getD (i + 8) ""))
    let linO := (List.range 3).map (fun i => f32 (hp.getD (i + 11) ""))
    let inv := (hp.getD 14 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyLog base logS logO linS linO inv 4 px) op_ "log" n k) then ok := false
  else if kind == "logcam" then
    let base := f32 (hp.getD 1 "")
    let logS := (List.range 3).map (fun i => f32 (hp.getD (i + 2) ""))
    let logO := (List.range 3).map (fun i => f32 (hp.getD (i + 5) ""))
    let linS := (List.range 3).map (fun i => f32 (hp.getD (i + 8) ""))
    let linO := (List.range 3).map (fun i => f32 (hp.getD (i + 11) ""))
    let linBrk := (List.range 3).map (fun i => f32 (hp.getD (i + 14) ""))
    let linSl := (List.range 3).map (fun i => f32 (hp.getD (i + 17) ""))
    let linOff := (List.range 3).map (fun i => f32 (hp.getD (i + 20) ""))
    let inv := (hp.getD 23 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyLogCam base logS logO linS linO linBrk linSl linOff inv 4 px) op_ "logcam" n k) then ok := false
  else if kind == "explin" then
    let sc := (List.range 4).map (fun i => f32 (hp.getD (i + 1) ""))
    let off := (List.range 4).map (fun i => f32 (hp.getD (i + 5) ""))
    let gam := (List.range 4).map (fun i => f32 (hp.getD (i + 9) ""))
    let brk := (List.range 4).map (fun i => f32 (hp.getD (i + 13) ""))
    let slo := (List.range 4).map (fun i => f32 (hp.getD (i + 17) ""))
    let inv := (hp.getD 21 "") == "1"
    let mir := (hp.getD 22 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyExpLinear sc off gam brk slo inv mir 4 px) op_ "explin" n k) then ok := false
  else if kind == "cdl" then
    let slope := (List.range 3).map (fun i => f32 (hp.getD (i + 1) ""))
    let off := (List.range 3).map (fun i => f32 (hp.getD (i + 4) ""))
    let pow := (List.range 3).map (fun i => f32 (hp.getD (i + 7) ""))
    let sat := f32 (hp.getD 10 "")
    let luma := (List.range 3).map (fun i => f32 (hp.getD (i + 11) ""))
    let clamp := (hp.getD 14 "") == "1"
    let inv := (hp.getD 15 "") == "1"
    for k in List.range 4 do
      let px := (f32 (ip.getD (k * 4 + 0) ""), f32 (ip.getD (k * 4 + 1) ""),
                 f32 (ip.getD (k * 4 + 2) ""), f32 (ip.getD (k * 4 + 3) ""))
      if !(← cmp4 (applyCdl slope off pow sat luma clamp inv px) op_ "cdl" n k) then ok := false
  else if kind == "ff" then
    let styleIdx : Nat := (hp.getD 1 "").foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    let params := (List.range 8).map (fun i => f32 (hp.getD (i + 3) ""))
    let style : FfStyle := match styleIdx with
      | 0 => .acesGlow10 | 1 => .acesGlow10Inv | 2 => .acesDarkToDim10
      | 3 => .acesDarkToDim10Inv | 4 => .acesGamutComp13
      | 5 => .acesGamutComp13Inv | 6 => .rec2100Surround | 7 => .rec2100SurroundInv
      | 8 => .acesGlow03 | 9 => .acesGlow03Inv | 10 => .acesRedMod03
      | 11 => .acesRedMod03Inv | 12 => .acesRedMod10 | 13 => .acesRedMod10Inv
      | 14 => .rgbToHsv | 15 => .hsvToRgb | 16 => .xyzToXyY | 17 => .xyYToXyz
      | 18 => .xyzToUvY | 19 => .uvYToXyz | 20 => .xyzToLuv | 21 => .luvToXyz
      | 22 => .linToPq | 23 => .pqToLin | 24 => .linToHlg | 25 => .hlgToLin
      | _ => .acesGlow10
    for k in List.range 1 do
      let r := f32 (ip.getD 0 "")
      let g := f32 (ip.getD 1 "")
      let b := f32 (ip.getD 2 "")
      let a := f32 (ip.getD 3 "")
      let cor := applyFixedFunc style params (r, g, b)
      let (cr, cg, cb) := cor
      let cor4 := (cr, cg, cb, a)
      if !(← cmp4 cor4 op_ "ff" n k) then ok := false
  return ok

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tocio_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let ok ← checkLine line (idx + 1)
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} blocks checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "tocio differential mismatch")
