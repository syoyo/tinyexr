/-
  TinyEXR - differential checker for the float-output texcomp wrappers.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.FloatOutput

open Texcomp

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0

def parseNat (s : String) : Nat := s.foldl (fun a c => a * 16 + hexVal c) 0

def bytesOf (s : String) : List UInt8 :=
  let cs := s.toList
  (List.range (cs.length / 2)).map (fun i => UInt8.ofNat (parseNat (String.ofList ((cs.drop (i * 2)).take 2))))

def u16Of (s : String) : UInt16 := UInt16.ofNat (parseNat s)
def f32Of (s : String) : Float32 := Float32.ofBits (UInt32.ofNat (parseNat s))

def chunks (n : Nat) (s : String) : List String :=
  let cs := s.toList
  (List.range (cs.length / n)).map (fun i => String.ofList ((cs.drop (i * n)).take n))

def u16List (s : String) : List UInt16 :=
  (chunks 4 s).map (fun q =>
    let lo := parseNat (String.ofList (q.toList.take 2))
    let hi := parseNat (String.ofList (q.toList.drop 2))
    UInt16.ofNat (lo + hi * 256))
def f32List (s : String) : List Float32 := (chunks 8 s).map f32Of

def halvesEqual (got : List UInt16) (want : String) : Bool :=
  let ws := u16List want
  got.length == ws.length && (List.zip got ws).all (fun q => q.1 == q.2)

def floatsEqual (got : List Float32) (want : String) : Bool :=
  let ws := f32List want
  got.length == ws.length &&
    (List.zip got ws).all (fun q => Float32.toBits q.1 == Float32.toBits q.2)

def checkLine (line : String) : Bool :=
  let f := fields line
  match f with
  | "bc6h16" :: sg :: w :: h :: rest =>
      let data := bytesOf (rest.getD 0 "")
      let want := rest.getD 1 ""
      match bc6hDecodeRgb16f data (w.toNat!) (h.toNat!) (sg == "1") with
      | some out => halvesEqual out want
      | none => false
  | "bc6hf" :: sg :: w :: h :: rest =>
      let data := bytesOf (rest.getD 0 "")
      let want := rest.getD 1 ""
      match bc6hDecodeRgbaf data (w.toNat!) (h.toNat!) (sg == "1") with
      | some out => floatsEqual out want
      | none => false
  | "bc7f" :: w :: h :: rest =>
      let data := bytesOf (rest.getD 0 "")
      let want := rest.getD 1 ""
      match bc7DecodeRgbaf data (w.toNat!) (h.toNat!) with
      | some out => floatsEqual out want
      | none => false
  | "astcf" :: w :: h :: bx :: bh :: rest =>
      let data := bytesOf (rest.getD 0 "")
      let want := rest.getD 1 ""
      match astcHdrDecodeRgbaf data (w.toNat!) (h.toNat!) (bx.toNat!) (bh.toNat!) with
      | some out => floatsEqual out want
      | none => false
  | _ => false

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tc_float_dec_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := (content.splitOn "\n").filter (fun s => s != "")
  let mut bad := 0
  for (i, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 8 then IO.println s!"mismatch at line {i + 1}"
  IO.println s!"{ls.length} float-output vectors checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "float-output differential mismatch")
