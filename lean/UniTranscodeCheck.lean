/-
  TinyEXR - uni BC1/BC7 transcode differential checker (C vs Lean model).

  Line (test/v3/astc_uni_transcode_vectors.c):
    T <w> <h> <ok> | <uni blocks> | <bc1 bytes> | <bc7 bytes>
  ok = 0 (corrupt uni): the model must also fail and the C produced no output.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.UniTranscode

open Texcomp

def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/astc_uni_transcode_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sec := line.splitOn "|"
    let head := fields (sec.getD 0 "")
    let w := decNat (head.getD 1 "0")
    let h := decNat (head.getD 2 "0")
    let wantOk := decNat (head.getD 3 "0") != 0
    let uni := (fields (sec.getD 1 "")).map hexNat
    let bc1 := (fields (sec.getD 2 "")).map hexNat
    let bc7 := (fields (sec.getD 3 "")).map hexNat
    let ok :=
      match uniTranscodeBc1 uni w h, uniTranscodeBc7 uni w h with
      | some a, some b => wantOk && a == bc1 && b == bc7
      | none, none => !wantOk
      | _, _ => false
    if !ok then
      bad := bad + 1
      if bad <= 4 then IO.eprintln s!"line {idx + 1} {w}x{h} wantOk={wantOk}: mismatch"
  IO.println s!"{lines.length} uni transcodes checked, {bad} mismatches"
  if bad != 0 then throw (IO.userError "uni transcode mismatch")
