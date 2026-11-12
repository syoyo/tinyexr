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
import Tocio.CodegenRecipe

open Tocio

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
