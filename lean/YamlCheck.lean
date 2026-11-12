/-
  TinyEXR - Tocio YAML parser differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/yaml_vectors.c`:

      ydoc <id> | <hex of the document text>
      y <id> <v> | <tree dump>

  where `v = 0` means the C parser accepted the document (dump is the
  canonical node tree) and `v = 1` means `TOC_ERROR_PARSE` (empty
  dump). The checker decodes the hex, parses the document with the
  Lean model parser (`Tocio.YamlEngine`), pretty-prints its tree with
  the same discipline (`dumpTree`, including `<tag>` prefixes), and requires a
  byte-for-byte match
  with the C dump (an empty dump on both sides for rejects).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.YamlEngine

open Tocio

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode the hex payload (ASCII documents only): byte pairs to chars. -/
def hexToChars (s : String) : List Char :=
  go s.toList
where
  go : List Char → List Char
    | a :: b :: rest => Char.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | [a] => [Char.ofNat (hexVal a)]
    | [] => []

def decNum (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

/-- Trim spaces/tabs on both ends (no `String.trim` in this toolchain). -/
def trimWS (s : String) : String :=
  let a := s.toList.dropWhile (fun c => c == ' ' || c == '\t')
  let b := a.reverse.dropWhile (fun c => c == ' ' || c == '\t')
  String.ofList b.reverse

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/yaml_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (fun l => l != "")

  -- Pass 1: collect `ydoc` records.
  let mut docs : List (Nat × String) := []
  for line in lines do
    let sections := line.splitOn "|"
    if (fields (sections.getD 0 "")).getD 0 "" == "ydoc" then
      let id := decNum ((fields (sections.getD 0 "")).getD 1 "")
      let hex := trimWS (sections.getD 1 "")
      docs := docs ++ [(id, hex)]

  -- Pass 2: check each `y` record.
  let mut bad := 0
  let mut n := 0
  for line in lines do
    let sections := line.splitOn "|"
    let hp := fields (sections.getD 0 "")
    if hp.getD 0 "" != "y" then continue
    n := n + 1
    let id := decNum (hp.getD 1 "")
    let v := decNum (hp.getD 2 "")
    let want := trimWS (sections.getD 1 "")
    let hex := match docs.find? (fun p => p.1 == id) with
      | some (_, h) => h
      | none => ""
    let got :=
      match yamlParse (String.ofList (hexToChars hex)) with
      | none => ""
      | some tree => dumpTree tree
    let want' := want
    if got != want' then
      IO.eprintln s!"doc {id} (v={v}):\n  C   : {want'}\n  Lean: {got}"
      bad := bad + 1

  IO.println s!"{n} docs checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "yaml differential mismatch")
