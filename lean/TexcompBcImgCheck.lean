/-
  TinyEXR - BC4/BC5 full-image differential checker (C vs Lean).

  Reads `test/v3/tc_bc_img_vectors.c` output and compares the complete
  decoded image byte-for-byte with `Texcomp.bc4DecodeImage` /
  `Texcomp.bc5DecodeImage`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc4Image
import Texcomp.Bc5Image
import Texcomp.Etc2Image
import Texcomp.EacImage
import Texcomp.Bc7DecodeImage

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0

def parseBytes (s : String) : List UInt8 :=
  let cs := s.toList
  (List.range (cs.length / 2)).map (fun i =>
    UInt8.ofNat (parseNat (String.ofList ((cs.drop (i * 2)).take 2))))

def decBytes (xs : List String) : List UInt8 :=
  xs.map (fun s => UInt8.ofNat s.toNat!)

def checkLine (line : String) : Bool :=
  let f := fields line
  match f with
  | kind :: w :: h :: data :: rest =>
      let wi := w.toNat!
      let hi := h.toNat!
      let bs := parseBytes data
      let want := decBytes rest
      match kind with
      | "bc4" =>
          match Texcomp.bc4DecodeImage bs wi hi with
          | some out => out == want
          | none => false
      | "bc5" =>
          match Texcomp.bc5DecodeImage bs wi hi with
          | some out => out == want
          | none => false
      | "etc2rgb" =>
          match Texcomp.etc2DecodeImage bs wi hi false with
          | some out => out == want
          | none => false
      | "etc2rgba" =>
          match Texcomp.etc2DecodeImage bs wi hi true with
          | some out => out == want
          | none => false
      | "eacr11" =>
          match Texcomp.eacDecodeImage bs wi hi false with
          | some out => out == want
          | none => false
      | "eacrg11" =>
          match Texcomp.eacDecodeImage bs wi hi true with
          | some out => out == want
          | none => false
      | "bc7" =>
          match Texcomp.bc7DecodeImage2 bs wi hi with
          | some out => out == want
          | none => false
      | _ => true
  | _ => true

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tc_bc_img_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line.take 160}"
  IO.println s!"{ls.length} BC image vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "BC image differential mismatch")
