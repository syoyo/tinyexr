/-
  TinyEXR - tocio matrix/LUT algebraic-model differential checker.

  The algebraic laws live in `Tocio.MatrixModel` / `Tocio.LutModel`; this
  gate pins the corresponding Float32 kernels against C.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Ops
import Tocio.Lut
import Tocio.MatrixModel
import Tocio.LutModel

noncomputable section

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def f32 (s : String) : Float32 := Float32.ofBits (UInt32.ofNat (parseNat s))
def f32s (xs : List String) : List Float32 := xs.map f32
def bitsEq (a b : Float32) : Bool := Float32.toBits a == Float32.toBits b
def eqs (a b : List Float32) : Bool :=
  a.length == b.length && (List.zip a b).all (fun p => bitsEq p.1 p.2)

def checkMat (f : List String) : Bool :=
  let xs := f32s (f.drop 1)
  let m := xs.take 16
  let off := (xs.drop 16).take 4
  let px := (xs.drop 20).take 4
  let want := (xs.drop 24).take 4
  let (r, g, b, a) := Tocio.applyMatrix m off (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  eqs [r, g, b, a] want

/-- Float32 byte-exact replay of the C `toc_lut1d_apply_pixel` path. -/
def lut1dF32 (data : Nat → Float32) (n : Nat) (dmin dmax x : Float32) : Float32 :=
  let den := dmax - dmin
  let u0 : Float32 := if den != 0 then (x - dmin) / den else 0
  let u : Float32 := if !(u0 > 0) then 0 else if u0 > 1 then 1 else u0
  let g : Float32 := u * Float32.ofNat (n - 1)
  let i : Nat := g.toUInt64.toNat
  let i0 : Nat := if i >= n - 1 then n - 2 else i
  let f : Float32 := g - Float32.ofNat i0
  let a := data i0
  let b := data (i0 + 1)
  a + (b - a) * f

def checkLut (f : List String) : Bool :=
  let n := (f.getD 1 "0").toNat!
  let chans := (f.getD 2 "0").toNat!
  let dmin := f32 (f.getD 3 "0")
  let dmax := f32 (f.getD 4 "0")
  let all := f32s (f.drop 5)
  let data := all.take (n * chans)
  let px := (all.drop (n * chans)).take 3
  let want := (all.drop (n * chans + 3)).take 3
  let out := (List.range 3).map (fun c =>
    lut1dF32 (fun i => if chans == 1 then data.getD i 0 else data.getD (i * 3 + c) 0)
      n dmin dmax (px.getD c 0))
  eqs out want

def pxList (p : Tocio.Pixel) : List Float32 := [p.1, p.2.1, p.2.2.1, p.2.2.2]

def checkRange (f : List String) : Bool :=
  let xs := f32s (f.drop 1)
  let sc := xs.take 4
  let of := (xs.drop 4).take 4
  let lo := (xs.drop 8).take 4
  let hi := (xs.drop 12).take 4
  let cl := (f.getD 17 "0") == "1"
  let ch := (f.getD 18 "0") == "1"
  let px := (xs.drop 18).take 4
  let want := (xs.drop 22).take 4
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  eqs (pxList (Tocio.applyRange sc of lo hi cl ch p)) want

def checkExp (f : List String) : Bool :=
  let mirror := (f.getD 1 "0") == "1"
  let ch := (f.getD 2 "0").toNat!
  let xs := f32s (f.drop 3)
  let e := xs.take 4
  let px := (xs.drop 4).take 4
  let want := (xs.drop 8).take 4
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  eqs (pxList (Tocio.applyExponent e mirror ch p)) want

def checkLine (line : String) : Bool :=
  let f := fields line
  match f with
  | "mat" :: _ => checkMat f
  | "range" :: _ => checkRange f
  | "exp" :: _ => checkExp f
  | "lut" :: _ => checkLut f
  | _ => true

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tocio_model_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 8 then IO.println s!"mismatch at line {idx + 1}: {line.take 160}"
  IO.println s!"{ls.length} tocio model vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "tocio model differential mismatch")
