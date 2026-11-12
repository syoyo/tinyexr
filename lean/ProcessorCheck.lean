/-
  TinyEXR - tocio processor-build differential checker (C vs Lean).

  Reads vectors from `test/v3/processor_vectors.c`:

      cdoc <id> | <hex of the config YAML>
      pcfg <id> | <0|1>                     (1 = config parse error)
      pq <id> cs <hex src> <hex dst> | <result>
      pq <id> dv <hex src> <hex display> <hex view> | <result>
      pop <id> | <qi> <k> <kind> <parameter bits...>

  re-parses the config with the Lean YAML model, rebuilds each pipeline
  with `Tocio.ProcessorModel`, and compares the rendered result
  (`ok:K1,K2,...` / `err:CODE`) and every op's numeric parameter recipe
  byte-for-byte.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.ProcessorModel
import Tocio.CodegenRecipe

open Tocio

structure Q where
  doc : Nat
  kind : String
  a : String
  b : String
  c : String
  want : String

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/processor_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (fun l => l != "")

  -- Pass 1: collect config documents, queries and parameter recipes.
  let mut docs : List (Nat × String) := []
  let mut qs : List Q := []
  let mut pops : List (Nat × String) := []
  let mut files : FileMap := []
  let mut cfgs : List (Nat × Nat) := []
  for line in lines do
    let sections := line.splitOn "|"
    let hp := fields (sections.getD 0 "")
    let head := hp.getD 0 ""
    let raw := sections.getD 1 ""
    let sec := if raw.startsWith " " then String.ofList (raw.toList.drop 1) else raw
    let id := decNum (hp.getD 1 "")
    if head == "cdoc" then
      docs := docs ++ [(id, String.ofList (hexToChars (trimWS sec)))]
    else if head == "pcfg" then
      cfgs := cfgs ++ [(id, decNum (hp.getD 2 ""))]
    else if head == "pq" then
      let kind := hp.getD 2 ""
      let a := String.ofList (hexToChars (hp.getD 3 ""))
      let b := String.ofList (hexToChars (hp.getD 4 ""))
      let c := String.ofList (hexToChars (hp.getD 5 ""))
      qs := qs ++ [{ doc := id, kind := kind, a := a, b := b, c := c, want := sec }]
    else if head == "pop" then
      pops := pops ++ [(id, sec)]
    else if head == "pfile" then
      let nm := String.ofList (hexToChars (hp.getD 1 ""))
      let dt := String.ofList (hexToChars (hp.getD 2 ""))
      files := files ++ [(nm, dt)]

  let mut bad := 0
  -- config verdicts
  for (id, wantErr) in cfgs do
    let tree : Option YTree :=
      match docs.find? (fun p => p.1 == id) with
      | some (_, h) => yamlParse h
      | none => none
    let got := match tree with | none => 1 | some _ => 0
    if got != wantErr then
      IO.eprintln s!"pcfg {id}: C {wantErr}, Lean {got}"
      bad := bad + 1

  -- queries and recipes, per doc in file order
  for (id, _) in docs do
    let docQs := qs.filter (fun q => q.doc == id)
    if docQs.isEmpty then continue
    let tree : Option YTree :=
      match docs.find? (fun p => p.1 == id) with
      | some (_, h) => yamlParse h
      | none => none
    let mut expectedPops : List String := []
    for (q, qi) in docQs.zipIdx do
      let res : Except String (List COp) :=
        match tree with
        | none => .error "PARSE"
        | some root =>
          if q.kind == "dv" then pFromDisplayView files root q.a q.b q.c
          else pFromColorspaces files root q.a q.b
      let got := renderProcResult res
      if got != q.want then
        IO.eprintln s!"pq {id} {q.kind} [{q.a}] [{q.b}] [{q.c}]:\n  C   : {q.want}\n  Lean: {got}"
        bad := bad + 1
      match res with
      | .ok ops =>
        for (op, k) in ops.zipIdx do
          expectedPops := expectedPops ++ [s!"{qi} {k} {copRecipe op}"]
      | .error _ => pure ()
    let gotPops := (pops.filter (fun p => p.1 == id)).map (·.2)
    if gotPops != expectedPops then
      IO.eprintln s!"pop {id}: {gotPops.length} C recipes vs {expectedPops.length} Lean"
      for ((g, e), i) in (List.zip gotPops expectedPops).zipIdx do
        if g != e then
          IO.eprintln s!"  recipe {i}:\n    C   : {g}\n    Lean: {e}"
      if gotPops.length != expectedPops.length then
        IO.eprintln s!"  C   : {gotPops}\n  Lean: {expectedPops}"
      bad := bad + 1

  IO.println s!"{qs.length} processor queries ({pops.length} op recipes) + {cfgs.length} config verdicts checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "processor differential mismatch")
