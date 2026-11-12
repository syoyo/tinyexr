/-
  TinyEXR - tocio AOT-C codegen differential checker (C vs Lean).

  Reads vectors from `test/v3/codegen_vectors.c`:

      cgop <id> <kind> <params...>      (floats as 8-hex-digit bit patterns)
      cgdoc <id> | <hex of the emitted C source>

  rebuilds each op list with the Lean model (`Tocio.CodegenC`), emits the
  source with `emitC`, and compares it hex-encoded against the C's output
  byte-for-byte.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.CodegenC

open Tocio

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseBits (s : String) : UInt32 :=
  UInt32.ofNat (s.foldl (fun acc c => acc * 16 + hexVal c) 0)

def decNum (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

/-- Hex-encode a string (ASCII bytes). -/
def toHex (s : String) : String :=
  String.join (s.toList.map (fun c =>
    let v := c.toNat
    let hi := hexDigChar (v / 16)
    let lo := hexDigChar (v % 16)
    String.ofList [hi, lo]))

def bitsAt (ts : List String) (start n : Nat) : List UInt32 :=
  (List.range n).map (fun i => parseBits (ts.getD (start + i) "0"))

def natAt (ts : List String) (i : Nat) : Nat :=
  decNum (ts.getD i "0")

/-- Parse one `cgop` record into an op (fields after `cgop <id>`). -/
def parseOp (ts : List String) : Option COp :=
  match ts.getD 0 "", ts.getD 1 "" with
  | "matrix", _ => some (.matrix (bitsAt ts 1 16) (bitsAt ts 17 4))
  | "range", _ =>
    some (.range (bitsAt ts 1 4) (bitsAt ts 5 4) (bitsAt ts 9 4) (bitsAt ts 13 4)
      (natAt ts 17 != 0) (natAt ts 18 != 0))
  | "exponent", _ => some (.exponent (bitsAt ts 1 4) (natAt ts 5 != 0))
  | "explinear", _ =>
    some (.expLinear (bitsAt ts 1 4) (bitsAt ts 5 4) (bitsAt ts 9 4)
      (bitsAt ts 13 4) (bitsAt ts 17 4) (natAt ts 21 != 0) (natAt ts 22 != 0))
  | "log", _ =>
    some (.log (bitsAt ts 1 3) (bitsAt ts 4 3) (bitsAt ts 7 3) (bitsAt ts 10 3)
      (parseBits (ts.getD 13 "0")) (natAt ts 14 != 0))
  | "logcam", _ => some .logCamera
  | "cdl", _ =>
    some (.cdl (bitsAt ts 1 3) (bitsAt ts 4 3) (bitsAt ts 7 3)
      (parseBits (ts.getD 10 "0")) (bitsAt ts 11 3)
      (natAt ts 14 != 0) (natAt ts 15 != 0))
  | "lut1d", _ =>
    let len := natAt ts 1
    let ch := natAt ts 2
    let n := len * (if ch == 1 then 1 else 3)
    some (.lut1d len ch (parseBits (ts.getD 3 "0")) (parseBits (ts.getD 4 "0"))
      (bitsAt ts 5 n))
  | "lut3d", _ =>
    let size := natAt ts 1
    let tet := natAt ts 2 != 0
    let n := size * size * size * 3
    some (.lut3d size (bitsAt ts 3 3) (bitsAt ts 6 3) tet (bitsAt ts 9 n))
  | "fixed", _ =>
    some (.fixed (natAt ts 1) (natAt ts 2) (bitsAt ts 3 8))
  | _, _ => none

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/codegen_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (fun l => l != "")

  -- collect custom function names per doc id
  let mut names : List (Nat × String) := []
  for line in lines do
    let ts := fields line
    if ts.getD 0 "" == "cgname" then
      names := names ++ [(natAt ts 1, ts.getD 2 "tocio_apply")]

  -- collect ops per doc id
  let mut opsByDoc : List (Nat × List COp) := []
  for line in lines do
    let ts := fields line
    if ts.getD 0 "" == "cgop" then
      let id := natAt ts 1
      match parseOp (ts.drop 2) with
      | some op =>
        opsByDoc := opsByDoc.map (fun p =>
          if p.1 == id then (p.1, p.2 ++ [op]) else p)
        if !opsByDoc.any (fun p => p.1 == id) then
          opsByDoc := opsByDoc ++ [(id, [op])]
      | none => IO.eprintln s!"bad cgop: {line}"

  let mut bad := 0
  let mut n := 0
  for line in lines do
    let sections := line.splitOn "|"
    let ts := fields (sections.getD 0 "")
    if ts.getD 0 "" != "cgdoc" then continue
    n := n + 1
    let id := decNum (ts.getD 1 "")
    let raw := sections.getD 1 ""
    let want := if raw.startsWith " " then String.ofList (raw.toList.drop 1) else raw
    let ops := match opsByDoc.find? (fun p => p.1 == id) with
      | some (_, os) => os
      | none => []
    let fname := match names.find? (fun p => p.1 == id) with
      | some (_, n) => n
      | none => "tocio_apply"
    let got :=
      match emitC fname ops with
      | .ok src => toHex src
      | .error _ => "ERR"
    if got != want then
      IO.eprintln s!"codegen doc {id}: mismatch ({got.length} vs {want.length} hex chars)"
      -- locate the first differing position for debugging
      let g := got.toList
      let w := want.toList
      let firstDiff :=
        (List.range (min g.length w.length)).find? (fun i => g[i]? != w[i]?)
      match firstDiff with
      | some i =>
        IO.eprintln s!"  first diff at hex char {i}: got {String.ofList (g.drop i |>.take 24)} want {String.ofList (w.drop i |>.take 24)}"
      | none => IO.eprintln "  (prefix equal; length differs)"
      bad := bad + 1

  IO.println s!"{n} codegen docs checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "codegen differential mismatch")
