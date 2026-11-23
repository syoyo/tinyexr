/-
  TinyEXR - tir scalar-kernel differential checker (C vectors vs Lean model).

  Reads bit-exact vectors emitted by `test/v3/tir_kernel_vectors.c` and
  replays the corresponding `Tir.Kernels` definition, comparing output
  Float32 bits (or integer/half values) exactly.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tir.Kernels

open Tir

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def f32 (s : String) : Float32 := Float32.ofBits (UInt32.ofNat (parseNat s))
def u16v (s : String) : UInt16 := UInt16.ofNat (parseNat s)
def decNat (s : String) : Nat := s.toNat!

def takeDrop (n : Nat) (xs : List String) : List String × List String :=
  (xs.take n, xs.drop n)

def f32s (xs : List String) : List Float32 := xs.map f32

def bitsEq (a b : Float32) : Bool := Float32.toBits a == Float32.toBits b

def listBitsEq (a b : List Float32) : Bool :=
  a.length == b.length && (List.zip a b).all (fun p => bitsEq p.1 p.2)

def checkLine (line : String) : Bool :=
  let f := fields line
  match f with
  | [] => true
  | kind :: rest =>
    match kind with
    | "hdot" =>
        let wc := (rest.getD 0 "0").toNat!
        let start := (rest.getD 1 "0").toNat!
        let count := (rest.getD 2 "0").toNat!
        let nblk := ((count + 3) / 4) * 4
        let srcn := (start + nblk + 2) * wc
        let src := f32s ((rest.drop 3).take srcn)
        let w := f32s ((rest.drop (3 + srcn)).take 8)
        let want := f32s ((rest.drop (3 + srcn + 8)).take wc)
        listBitsEq (hDot wc start count src w) want
    | "vweighted" =>
        let n := (rest.getD 0 "0").toNat!
        let c := (rest.getD 1 "0").toNat!
        let w := f32s ((rest.drop 2).take n)
        let rows := f32s ((rest.drop (2 + n)).take (n + c + 2))
        let want := f32 ((rest.drop (2 + n + n + c + 2)).getD 0 "0")
        bitsEq (vWeighted n w rows c) want
    | "minmax" =>
        let start := (rest.getD 0 "0").toNat!
        let count := (rest.getD 1 "0").toNat!
        let src := f32s ((rest.drop 2).take (count + 2))
        let wantMn := f32 (rest.getD (2 + count + 2) "0")
        let wantMx := f32 (rest.getD (3 + count + 2) "0")
        let (mn, mx) := hMinMax start count src 0
        bitsEq mn wantMn && bitsEq mx wantMx
    | "anti" =>
        let v := f32 (rest.getD 0 "0"); let mn := f32 (rest.getD 1 "0")
        let mx := f32 (rest.getD 2 "0"); let s := f32 (rest.getD 3 "0")
        let want := f32 (rest.getD 4 "0")
        bitsEq (antiringApply v mn mx s) want
    | "clamp" =>
        let v := f32 (rest.getD 0 "0"); let lo := f32 (rest.getD 1 "0")
        let hi := f32 (rest.getD 2 "0"); let want := f32 (rest.getD 3 "0")
        bitsEq (clampOne v lo hi) want
    | "norm3" =>
        let x := f32 (rest.getD 0 "0"); let y := f32 (rest.getD 1 "0")
        let z := f32 (rest.getD 2 "0")
        let want := rest.drop 3 |>.take 3 |>.map f32
        let (a, b, c) := normalize3 x y z
        listBitsEq [a, b, c] want
    | "premul" =>
        let v := (rest.take 4).map f32
        let want := (rest.drop 4).take 4 |>.map f32
        let (a, b, c, d) := premult4 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0) (v.getD 3 0)
        listBitsEq [a, b, c, d] want
    | "unpremul" =>
        let v := (rest.take 4).map f32
        let want := (rest.drop 4).take 4 |>.map f32
        let (a, b, c, d) := unpremult4 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0) (v.getD 3 0)
        listBitsEq [a, b, c, d] want
    | "rc" =>
        bitsEq (rangeCompress (f32 (rest.getD 0 "0"))) (f32 (rest.getD 1 "0"))
    | "re" =>
        bitsEq (rangeExpand (f32 (rest.getD 0 "0"))) (f32 (rest.getD 1 "0"))
    | "f16to32" =>
        bitsEq (f16ToF32 (u16v (rest.getD 0 "0"))) (f32 (rest.getD 1 "0"))
    | "f32to16" =>
        f32ToF16 (f32 (rest.getD 0 "0")) == u16v (rest.getD 1 "0")
    | "u8to32" =>
        bitsEq (u8ToF32 (UInt8.ofNat (decNat (rest.getD 0 "0")))) (f32 (rest.getD 1 "0"))
    | "u16to32" =>
        bitsEq (u16ToF32 (UInt16.ofNat (decNat (rest.getD 0 "0")))) (f32 (rest.getD 1 "0"))
    | "f32tou8" =>
        f32ToU8 (f32 (rest.getD 0 "0")) == UInt8.ofNat ((rest.getD 1 "0").toNat!)
    | "f32tou16" =>
        f32ToU16 (f32 (rest.getD 0 "0")) == u16v (rest.getD 1 "0")
    | _ => true

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tir_kernel_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} tir kernel vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "tir kernel differential mismatch")
