/-
  TinyEXR - tocio GLSL codegen differential checker (C vs Lean).

  Reads vectors from `test/v3/glsl_vectors.c`:

      ggtarget <id> <es30|330|vulkan>
      ggop <id> <kind> <params...>
      ggtex <id> <name> <dim> <w> <h> <d> <ch> <interp>
      ggdoc <id> | <hex of the emitted shader source>

  rebuilds each op list, emits the shader with `Tocio.emitGLSL`, and
  compares the source and the LUT texture descriptors against the C.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.CodegenGLSL
import Tocio.CodegenMetal
import Tocio.CodegenRecipe

open Tocio

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/glsl_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := (content.splitOn "\n").filter (fun l => l != "")

  let mut targets : List (Nat × String) := []
  let mut opsByDoc : List (Nat × List COp) := []
  let mut texLines : List (Nat × String) := []
  for line in lines do
    let ts := fields line
    if ts.getD 0 "" == "ggtarget" then
      targets := targets ++ [(natAt ts 1, ts.getD 2 "es30")]
    else if ts.getD 0 "" == "ggop" then
      let id := natAt ts 1
      match parseOp (ts.drop 2) with
      | some op =>
        if opsByDoc.any (fun p => p.1 == id) then
          opsByDoc := opsByDoc.map (fun p =>
            if p.1 == id then (p.1, p.2 ++ [op]) else p)
        else
          opsByDoc := opsByDoc ++ [(id, [op])]
      | none => IO.eprintln s!"bad ggop: {line}"
    else if ts.getD 0 "" == "ggtex" || ts.getD 0 "" == "msltex" then
      -- compare argument vector textually (tagged by backend)
      let rest := String.intercalate " " (ts.drop 2)
      texLines := texLines ++ [(natAt ts 1, (if ts.getD 0 "" == "ggtex" then "G " else "M ") ++ rest)]

  let mut bad := 0
  let mut n := 0
  let mut ntex := 0
  for line in lines do
    let sections := line.splitOn "|"
    let ts := fields (sections.getD 0 "")
    let isMsl := ts.getD 0 "" == "msldoc"
    if ts.getD 0 "" != "ggdoc" && !isMsl then continue
    n := n + 1
    let id := decNum (ts.getD 1 "")
    let raw := sections.getD 1 ""
    let want := if raw.startsWith " " then String.ofList (raw.toList.drop 1) else raw
    let target := match targets.find? (fun p => p.1 == id) with
      | some (_, t) => t
      | none => "es30"
    let ops := match opsByDoc.find? (fun p => p.1 == id) with
      | some (_, os) => os
      | none => []
    match (if isMsl then emitMetal ops else emitGLSL target ops) with
    | .error e =>
      IO.eprintln s!"glsl doc {id}: Lean error {e}"
      bad := bad + 1
    | .ok out =>
      let got := toHex out.source
      if got != want then
        IO.eprintln s!"glsl doc {id}: source mismatch ({got.length} vs {want.length} hex chars)"
        let g := got.toList
        let w := want.toList
        match (List.range (min g.length w.length)).find? (fun i => g[i]? != w[i]?) with
        | some i =>
          IO.eprintln s!"  first diff at hex char {i}: got {String.ofList (g.drop i |>.take 24)} want {String.ofList (w.drop i |>.take 24)}"
        | none => IO.eprintln "  (prefix equal; length differs)"
        bad := bad + 1
      -- texture descriptors
      let tag := if isMsl then "M " else "G "
      let wantTex := (texLines.filter (fun p => p.1 == id && p.2.startsWith tag)).map
        (fun p => String.ofList (p.2.toList.drop 2))
      let gotTex := out.textures.map (fun t =>
        s!"{t.name} {t.dim} {t.width} {t.height} {t.depth} {t.channels} {if t.interp then 1 else 0}")
      ntex := ntex + 1
      if gotTex != wantTex then
        IO.eprintln s!"glsl doc {id}: texture mismatch\n  C   : {wantTex}\n  Lean: {gotTex}"
        bad := bad + 1

  IO.println s!"{n} GPU shaders ({ntex} docs) checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "GLSL codegen differential mismatch")
