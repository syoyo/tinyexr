/-
  TinyEXR - codegen-semantics differential checker.

  Replays `test/v3/tocio_model_vectors.c` matrix vectors through the
  statement AST of `Tocio.CodegenSemantics` (the AST whose emitted text is
  byte-identical to the C emitter per `tocio-codegen-diff`) and compares
  the result with the C kernel output.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.CodegenSemantics

noncomputable section

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def hv (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def pn (s : String) : Nat := s.foldl (fun a c => a * 16 + hv c) 0
def f32 (s : String) : Float32 := Float32.ofBits (UInt32.ofNat (pn s))
def f32s (xs : List String) : List Float32 := xs.map f32
def eqs (a b : List Float32) : Bool :=
  a.length == b.length && (List.zip a b).all (fun q => Float32.toBits q.1 == Float32.toBits q.2)

def checkMat (f : List String) : Bool :=
  let xs := (f.drop 1).map f32
  let m := xs.take 16
  let off := (xs.drop 16).take 4
  let px := (xs.drop 20).take 4
  let want := (xs.drop 24).take 4
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  let out := Tocio.evalStmts
    (Tocio.compileMatrix (m.map Float32.toBits) (off.map Float32.toBits))
    (Tocio.pxList p)
  (List.zip out want).all (fun q => Float32.toBits q.1 == Float32.toBits q.2) &&
    out.length == want.length &&
    Tocio.listPx out == Tocio.applyMatrix m off p

def checkRange (f : List String) : Bool :=
  let xs := (f.drop 1).map f32
  let sc := xs.take 4
  let of := (xs.drop 4).take 4
  let lo := (xs.drop 8).take 4
  let hi := (xs.drop 12).take 4
  let cl := (f.getD 17 "0") == "1"
  let ch := (f.getD 18 "0") == "1"
  let px := (xs.drop 18).take 4
  let want := (xs.drop 22).take 4
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  let out := Tocio.evalStmts
    (Tocio.compileRange (sc.map Float32.toBits) (of.map Float32.toBits)
      (lo.map Float32.toBits) (hi.map Float32.toBits) cl ch) (Tocio.pxList p)
  (List.zip out want).all (fun q => Float32.toBits q.1 == Float32.toBits q.2) &&
    out.length == want.length &&
    Tocio.listPx out == Tocio.applyRange sc of lo hi cl ch p

def checkLutAst (f : List String) : Bool :=
  let n := (f.getD 1 "0").toNat!
  let ch := (f.getD 2 "0").toNat!
  let dmin := f32 (f.getD 3 "0")
  let dmax := f32 (f.getD 4 "0")
  let all := (f.drop 5).map f32
  let data := (all.take (n * ch)).map Float32.toBits
  let px := (all.drop (n * ch)).take 3
  let want := (all.drop (n * ch + 3)).take 3
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, 0)
  let out := Tocio.evalStmts
    (Tocio.compileLut1d n ch (Float32.toBits dmin) (Float32.toBits dmax) data)
    (Tocio.pxList p)
  (List.zip (out.take 3) want).all (fun q => Float32.toBits q.1 == Float32.toBits q.2) &&
    out.length >= 3

def checkExp (f : List String) : Bool :=
  let mirror := (f.getD 1 "0") == "1"
  let ch := (f.getD 2 "0").toNat!
  let xs := f32s (f.drop 3)
  let e := xs.take 4
  let px := (xs.drop 4).take 4
  let want := (xs.drop 8).take 4
  let p : Tocio.Pixel := (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
  let out := Tocio.evalStmts
    (Tocio.compileExponent (e.map Float32.toBits) mirror ch) (Tocio.pxList p)
  eqs out want &&
  Tocio.listPx out == Tocio.applyExponent e mirror ch p

def checkLine (line : String) : Bool :=
  let f := fields line
  match f with
  | "mat" :: _ => checkMat f
  | "range" :: _ => checkRange f
  | "exp" :: _ => checkExp f
  | "lut" :: _ => checkLutAst f
  | _ => true

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tocio_model_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 5 then IO.println s!"mismatch at line {idx + 1}"
  IO.println s!"{ls.length} codegen-semantics vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "codegen semantics differential mismatch")
