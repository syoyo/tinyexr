/-
  TinyEXR - shared vector-parsing helpers for the tocio codegen gates.

  The `cgop`/`ggop` recipe format (op kind plus float parameters as
  8-hex-digit IEEE-754 bit patterns) and hex helpers used by
  `CodegenCheck` (AOT-C) and `GLSLCheck` (GLSL).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.CodegenC

namespace Tocio

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


end Tocio
