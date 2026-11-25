/-
  TinyEXR - bit-exact differential checker for the shared math model.

  Reads vectors emitted by `test/v3/math_vectors.c` and compares the output
  bit pattern of each `ExrMath` definition against the C implementation.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Math.F32

open ExrMath

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseHex (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0

def bits (s : String) : UInt32 := UInt32.ofNat (parseHex s)
def f32 (s : String) : Float32 := Float32.ofBits (bits s)

def checkLine (fs : List String) : Bool :=
  match fs with
  | [op, a, r] =>
      let x := f32 a
      let want := bits r
      let got :=
        match op with
        | "log2f" => log2f x
        | "exp2f" => exp2f x
        | "logf" => logf x
        | "expf" => expf x
        | "sqrtf" => sqrtf x
        | "sqrtfExact" => sqrtfExact x
        | "log2fFast" => log2fFast x
        | "exp2fFast" => exp2fFast x
        | "sqrtfFast" => sqrtfFast x
        | _ => Float32.ofBits 0xdeadbeef
      Float32.toBits got == want
  | [op, a, b, r] =>
      let x := f32 a
      let y := f32 b
      let want := bits r
      let got :=
        match op with
        | "powf" => powf x y
        | "powfFast" => powfFast x y
        | _ => Float32.ofBits 0xdeadbeef
      Float32.toBits got == want
  | _ => false

def checkLines : List String → Nat × Nat × List String
  | [] => (0, 0, [])
  | l :: ls =>
      let (ok, bad, ex) := checkLines ls
      if checkLine (fields l) then (ok + 1, bad, ex) else (ok, bad + 1, l :: ex)

def main (args : List String) : IO UInt32 := do
  let path := args.getD 0 "/tmp/opencode/math_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := (content.splitOn "\n").filter (fun s => s != "")
  let (ok, bad, ex) := checkLines ls
  IO.println s!"math vectors checked: {ok + bad}, mismatches: {bad}"
  for l in ex.take 10 do IO.println s!"  MISMATCH {l}"
  return if bad == 0 then 0 else 1
