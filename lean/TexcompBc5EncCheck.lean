/-
  TinyEXR - BC5 image-compressor differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc5EncodeImage
import Texcomp.Bc3EncodeImage
import Texcomp.EacEncodeImage
import Texcomp.Bc7EncodeImage
import Texcomp.Bc6hEncodeImage

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0

def parseNats (s : String) : List Nat :=
  let cs := s.toList
  (List.range (cs.length / 2)).map (fun i => parseNat (String.ofList ((cs.drop (i * 2)).take 2)))

def checkBc3 (f : List String) : Bool :=
  match f with
  | "bc3enc" :: w :: h :: _ :: _ :: src :: want :: _ =>
      match Texcomp.bc3CompressImage (parseNats src) w.toNat! h.toNat! with
      | some out => out == parseNats want
      | none => false
  | _ => true

def checkEac (f : List String) : Bool :=
  match f with
  | "eacenc" :: w :: h :: rg :: _ :: src :: want :: _ =>
      match Texcomp.eacCompressImage (parseNats src) w.toNat! h.toNat! (rg == "1") with
      | some out => out == parseNats want
      | none => false
  | _ => true

def checkBc7Img (f : List String) : Bool :=
  match f with
  | "bc7enc" :: w :: h :: _ :: _ :: src :: want :: _ =>
      match Texcomp.bc7CompressImage (parseNats src) w.toNat! h.toNat! with
      | some out => out == parseNats want
      | none => false
  | _ => true

def parseWords (s : String) : List UInt32 :=
  let cs := s.toList
  (List.range (cs.length / 8)).map (fun i => UInt32.ofNat (parseNat (String.ofList ((cs.drop (i * 8)).take 8))))

def checkBc6hImg (f : List String) : Bool :=
  match f with
  | "bc6henc" :: w :: h :: sf :: src :: want :: _ =>
      match Texcomp.bc6hCompressImage (parseWords src) w.toNat! h.toNat! (sf == "1") with
      | some out => out == parseNats want
      | none => false
  | _ => true

def checkLine (line : String) : Bool :=
  if line.startsWith "bc6henc" then checkBc6hImg (fields line) else
  if line.startsWith "bc3enc" then checkBc3 (fields line)
  else if line.startsWith "eacenc" then checkEac (fields line)
  else if line.startsWith "bc7enc" then checkBc7Img (fields line) else
  let f := fields line
  match f with
  | "bc5enc" :: w :: h :: rgba :: snorm :: src :: want :: _ =>
      let wi := w.toNat!
      let hi := h.toNat!
      let r := rgba == "1"
      let s := snorm == "1"
      match Texcomp.bc5CompressImage (parseNats src) wi hi r s with
      | some out => out == parseNats want
      | none => false
  | _ => true

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tc_bc5_enc_img_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line.take 160}"
  IO.println s!"{ls.length} BC5 image-encoder vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "BC5 image encoder differential mismatch")
