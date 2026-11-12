/-
  TinyEXR - tocio processor-build differential checker (C vs Lean).

  Reads vectors from `test/v3/processor_vectors.c`:

      cdoc <id> | <hex of the config YAML>
      pcfg <id> | <0|1>                     (1 = config parse error)
      pq <id> cs <hex src> <hex dst> | <result>
      pq <id> dv <hex src> <hex display> <hex view> | <result>

  re-parses the config with the Lean YAML model, rebuilds each pipeline
  with `Tocio.ProcessorModel`, and compares the rendered result
  (`ok:K1,K2,...` / `err:CODE`) byte-for-byte.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.ProcessorModel

open Tocio

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode the hex payload (ASCII): byte pairs to chars. -/
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
  let path := args.getD 0 "build/lean-gen/processor_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (fun l => l != "")

  -- Pass 1: collect config documents.
  let mut docs : List (Nat × String) := []
  for line in lines do
    let sections := line.splitOn "|"
    let hp := fields (sections.getD 0 "")
    if hp.getD 0 "" == "cdoc" then
      let id := decNum (hp.getD 1 "")
      let hex := trimWS (sections.getD 1 "")
      docs := docs ++ [(id, hex)]

  let mut bad := 0
  let mut npq := 0
  let mut npcfg := 0
  for line in lines do
    let sections := line.splitOn "|"
    let hp := fields (sections.getD 0 "")
    let resRaw := sections.getD 1 ""
    let res := if resRaw.startsWith " " then String.ofList (resRaw.toList.drop 1) else resRaw
    let id := decNum (hp.getD 1 "")
    let tree : Option YTree :=
      match docs.find? (fun p => p.1 == id) with
      | some (_, h) => yamlParse (String.ofList (hexToChars h))
      | none => none
    if hp.getD 0 "" == "pcfg" then
      npcfg := npcfg + 1
      let wantErr := decNum (hp.getD 2 "")
      let got := match tree with | none => "1" | some _ => "0"
      if got != (if wantErr == 1 then "1" else "0") then
        IO.eprintln s!"pcfg {id}: C {wantErr}, Lean {got}"
        bad := bad + 1
    else if hp.getD 0 "" == "pq" then
      npq := npq + 1
      let kind := hp.getD 2 ""
      let a := String.ofList (hexToChars (hp.getD 3 ""))
      let b := String.ofList (hexToChars (hp.getD 4 ""))
      let c := String.ofList (hexToChars (hp.getD 5 ""))
      let got :=
        match tree with
        | none => "err:PARSE"
        | some root =>
          if kind == "dv" then renderProcResult (pFromDisplayView root a b c)
          else renderProcResult (pFromColorspaces root a b)
      if got != res then
        IO.eprintln s!"pq {id} {kind} [{a}] [{b}] [{c}]:\n  C   : {res}\n  Lean: {got}"
        bad := bad + 1

  IO.println s!"{npq} processor queries + {npcfg} config verdicts checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "processor differential mismatch")
