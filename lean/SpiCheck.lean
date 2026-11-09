/-
  TinyEXR - SPI file differential checker (C vs Lean).
  Reads vectors from `test/v3/spi_vectors.c` (C `load_spi1d`/`load_spi3d`
  parse results plus applied pixels, and the hex-encoded source), then
  re-parses with Lean `loadSpi1d`/`loadSpi3d` and compares op contents
  and kernel outputs bit-for-bit.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.SpiFile

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

/-- Hex bytes → string by characters. -/
def fromHex (s : String) : String :=
  let cs := s.toList
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | a :: b :: rest => go rest (acc ++ [Char.ofNat (hexVal a * 16 + hexVal b)])
    | _ => acc
  String.ofList (go cs [])

def checkHead (n : Nat) (hp : List String) (outp : List String) (srcs : String)
    : IO Bool := do
  let kind := hp.getD 0 ""
  let status := hp.getD 1 ""
  let lutKind := hp.getD 2 ""
  let src := fromHex (String.ofList ((srcs.toList).dropWhile (· == ' ')))
  if status == "fail" then
    match kind with
    | "spi1d" =>
      match loadSpi1d src with
      | none => return true
      | some _ =>
        IO.eprintln s!"line {n} spi1d: expected parse failure, Lean succeeded"
        return false
    | "spi3d" =>
      match loadSpi3d src with
      | none => return true
      | some _ =>
        IO.eprintln s!"line {n} spi3d: expected parse failure, Lean succeeded"
        return false
    | _ =>
      IO.eprintln s!"line {n}: unknown kind {kind}"
      return false
  if lutKind == "lut1d" then
    let length := decNum (hp.getD 3 "")
    let channels := decNum (hp.getD 4 "")
    let dmin := f32 (hp.getD 5 "")
    let dmax := f32 (hp.getD 6 "")
    let ndata := length * channels
    let data := (List.range ndata).map (fun i => f32 (hp.getD (i + 8) ""))
    let npix := outp.length / 4
    match loadSpi1d src with
    | none =>
      IO.eprintln s!"line {n} spi1d: C ok, Lean failed"
      return false
    | some c =>
      let mut ok := true
      if c.length != length || c.channels != channels ||
         Float32.toBits c.domainMin != Float32.toBits dmin ||
         Float32.toBits c.domainMax != Float32.toBits dmax then
        IO.eprintln s!"line {n} spi1d: header mismatch: got len {c.length} ch {c.channels} dom {c.domainMin} {c.domainMax}"
        ok := false
      for (i, v) in List.zip (List.range ndata) data do
        if Float32.toBits (c.data.getD i 0.0) != Float32.toBits v then
          IO.eprintln s!"line {n} spi1d: data[{i}] got {c.data.getD i 0.0}, want {v}"
          ok := false
      for k in List.range npix do
        let r := f32 (hp.getD (8 + ndata + (k * 4 + 0)) "")
        let g := f32 (hp.getD (8 + ndata + (k * 4 + 1)) "")
        let b := f32 (hp.getD (8 + ndata + (k * 4 + 2)) "")
        let a := f32 (hp.getD (8 + ndata + (k * 4 + 3)) "")
        let (cr, cg, cb) := applyLut1d c.length c.channels c.domainMin c.domainMax
          LutInterp.linear c.data (r, g, b)
        let er := f32 (outp.getD (k * 4 + 0) "")
        let eg := f32 (outp.getD (k * 4 + 1) "")
        let eb := f32 (outp.getD (k * 4 + 2) "")
        let ea := f32 (outp.getD (k * 4 + 3) "")
        if Float32.toBits cr != Float32.toBits er ||
           Float32.toBits cg != Float32.toBits eg ||
           Float32.toBits cb != Float32.toBits eb ||
           Float32.toBits a != Float32.toBits ea then
          IO.eprintln s!"line {n} spi1d pixel {k}: got {cr} {cg} {cb} {a}, want {er} {eg} {eb} {ea}"
          ok := false
      return ok
  else if lutKind == "lut3d" then
    let size := decNum (hp.getD 3 "")
    let ndata := size * size * size * 3
    let data := (List.range ndata).map (fun i => f32 (hp.getD (i + 7) ""))
    let npix := outp.length / 4
    match loadSpi3d src with
    | none =>
      IO.eprintln s!"line {n} spi3d: C ok, Lean failed"
      return false
    | some c =>
      let mut ok := true
      if c.size != size then
        IO.eprintln s!"line {n} spi3d: size got {c.size}, want {size}"
        ok := false
      for (i, v) in List.zip (List.range ndata) data do
        if Float32.toBits (c.data.getD i 0.0) != Float32.toBits v then
          IO.eprintln s!"line {n} spi3d: data[{i}] got {c.data.getD i 0.0}, want {v}"
          ok := false
      for k in List.range npix do
        let r := f32 (hp.getD (7 + ndata + (k * 4 + 0)) "")
        let g := f32 (hp.getD (7 + ndata + (k * 4 + 1)) "")
        let b := f32 (hp.getD (7 + ndata + (k * 4 + 2)) "")
        let a := f32 (hp.getD (7 + ndata + (k * 4 + 3)) "")
        let (cr, cg, cb) := applyLut3dTrilinear c.size [0.0, 0.0, 0.0] [1.0, 1.0, 1.0]
          c.data (r, g, b)
        let er := f32 (outp.getD (k * 4 + 0) "")
        let eg := f32 (outp.getD (k * 4 + 1) "")
        let eb := f32 (outp.getD (k * 4 + 2) "")
        let ea := f32 (outp.getD (k * 4 + 3) "")
        if Float32.toBits cr != Float32.toBits er ||
           Float32.toBits cg != Float32.toBits eg ||
           Float32.toBits cb != Float32.toBits eb ||
           Float32.toBits a != Float32.toBits ea then
          IO.eprintln s!"line {n} spi3d pixel {k}: got {cr} {cg} {cb} {a}, want {er} {eg} {eb} {ea}"
          ok := false
      return ok
  else
    IO.eprintln s!"line {n}: unknown lut kind {lutKind}"
    return false

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/spi_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let head := sections.getD 0 ""
    let outp := sections.getD 1 ""
    let srcs := sections.getD (sections.length - 1) ""
    let ok ← checkHead (idx + 1) (fields head) (fields outp) srcs
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} lines checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "spi differential mismatch")
