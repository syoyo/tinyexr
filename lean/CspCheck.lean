/-
  TinyEXR - CSP differential checker (C vs Lean).
  Reads vectors from `test/v3/csp_vectors.c` (C `toc_load_csp` results
  plus applied pixels and the hex-encoded source), re-parses with Lean
  `loadCsp`, compares op contents bit-for-bit and applies the ops
  through the Lean kernels.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Csp
import Tocio.Ops

open Tocio

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseBits (s : String) : UInt32 :=
  UInt32.ofNat (s.foldl (fun acc c => acc * 16 + hexVal c) 0)

def f32 (s : String) : Float32 := Float32.ofBits (parseBits s)

def decNum (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def fromHex (s : String) : String :=
  let cs := (s.toList).filter (fun c => c != ' ' && c != '\n')
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | a :: b :: rest => go rest (acc ++ [Char.ofNat (hexVal a * 16 + hexVal b)])
    | _ => acc
  String.ofList (go cs [])

def readF32s (toks : List String) (i n : Nat) : List Float32 × Nat :=
  let vals := (List.range n).map (fun k => f32 (toks.getD (i + k) ""))
  (vals, i + n)

def applyOp (op : ClfOp) (px : Pixel) : Pixel :=
  match op with
  | .matrix m off => applyMatrix m off px
  | .lut1d ln d =>
    let (o0, o1, o2) := applyLut1d ln 3 0.0 1.0 LutInterp.linear d (px.1, px.2.1, px.2.2.1)
    (o0, o1, o2, px.2.2.2)
  | .lut3d sz d tetra =>
    let px3 := (px.1, px.2.1, px.2.2.1)
    let (o0, o1, o2) := if tetra then
      applyLut3dTet sz [0.0, 0.0, 0.0] [1.0, 1.0, 1.0] d px3
    else
      applyLut3dTrilinear sz [0.0, 0.0, 0.0] [1.0, 1.0, 1.0] d px3
    (o0, o1, o2, px.2.2.2)
  | _ => px

def checkLine (line : String) (n : Nat) : IO Bool := do
  let sections := line.splitOn "|"
  let head := sections.getD 0 ""
  let outp := sections.getD 1 ""
  let srcs := sections.getD (sections.length - 1) ""
  let hp := fields head
  let src := fromHex srcs
  if (hp.getD 1 "") == "fail" then
    let want := hp.getD 2 ""
    match loadCsp src with
    | Except.error .parse =>
      if want == "parse" then return true
      else
        IO.eprintln s!"line {n}: C {want}, Lean parse"
        return false
    | Except.error .unsupported =>
      if want == "unsupported" then return true
      else
        IO.eprintln s!"line {n}: C {want}, Lean unsupported"
        return false
    | Except.ok ops =>
      IO.eprintln s!"line {n}: C {want}, Lean ok with {ops.length} ops"
      return false
  let nops := decNum (hp.getD 3 "")
  let mut idx := 4
  let mut ok := true
  let mut wantOps : List (String × List Float32 × Nat × Bool) := []
  for _ in List.range nops do
    let kind := hp.getD idx ""
    idx := idx + 1
    if kind == "matrix" then
      let (m, i1) := readF32s hp idx 16
      let (off, i2) := readF32s hp i1 4
      wantOps := wantOps ++ [("matrix", m ++ off, 0, false)]
      idx := i2
    else if kind == "lut1d" then
      let ln := decNum (hp.getD idx "")
      let (data, i1) := readF32s hp (idx + 1) (ln * 3)
      wantOps := wantOps ++ [("lut1d", data, ln, false)]
      idx := i1
    else if kind == "lut3d" then
      let sz := decNum (hp.getD idx "")
      let tetra := decNum (hp.getD (idx + 1) "")
      let (data, i2) := readF32s hp (idx + 2) (sz * sz * sz * 3)
      wantOps := wantOps ++ [("lut3d", data, sz, tetra == 2)]
      idx := i2
    else
      IO.eprintln s!"line {n}: unknown op kind {kind}"
      ok := false
  let npix := (fields outp).length / 4
  match loadCsp src with
  | Except.error e =>
    IO.eprintln s!"line {n}: C ok, Lean {e}"
    return false
  | Except.ok ops =>
    if ops.length != nops then
      IO.eprintln s!"line {n}: op count got {ops.length}, want {nops}"
      ok := false
    for (i, w) in List.zip (List.range nops) wantOps do
      let (kind, data, nn, tetra) := w
      match ops[i]? with
      | none => pure ()
      | some op =>
        match kind with
        | "matrix" =>
          match op with
          | .matrix m off =>
            let got := m ++ off
            for (k, v) in List.zip (List.range 20) data do
              if Float32.toBits (got.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} matrix field[{k}]"
                ok := false
          | _ => pure ()
        | "lut1d" =>
          match op with
          | .lut1d ln d =>
            if ln != nn then
              IO.eprintln s!"line {n} op {i} lut1d length got {ln}, want {nn}"
              ok := false
            for (k, v) in List.zip (List.range data.length) data do
              if Float32.toBits (d.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} lut1d data[{k}] got {d.getD k 0.0}, want {v}"
                ok := false
          | _ => pure ()
        | "lut3d" =>
          match op with
          | .lut3d sz d tetra' =>
            if sz != nn || tetra' != tetra then
              IO.eprintln s!"line {n} op {i} lut3d header"
              ok := false
            for (k, v) in List.zip (List.range data.length) data do
              if Float32.toBits (d.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} lut3d data[{k}] got {d.getD k 0.0}, want {v}"
                ok := false
          | _ => pure ()
        | _ => pure ()
    for k in List.range npix do
      let r := f32 (hp.getD (idx + (k * 4 + 0)) "")
      let g := f32 (hp.getD (idx + (k * 4 + 1)) "")
      let b := f32 (hp.getD (idx + (k * 4 + 2)) "")
      let a := f32 (hp.getD (idx + (k * 4 + 3)) "")
      let px0 : Pixel := (r, g, b, a)
      let out0 := ops.foldl (fun p op => applyOp op p) px0
      let (cr, cg, cb, ca) := out0
      let er := f32 ((fields outp).getD (k * 4 + 0) "")
      let eg := f32 ((fields outp).getD (k * 4 + 1) "")
      let eb := f32 ((fields outp).getD (k * 4 + 2) "")
      let ea := f32 ((fields outp).getD (k * 4 + 3) "")
      if Float32.toBits cr != Float32.toBits er ||
         Float32.toBits cg != Float32.toBits eg ||
         Float32.toBits cb != Float32.toBits eb ||
         Float32.toBits ca != Float32.toBits ea then
        IO.eprintln s!"line {n} pixel {k}: got {cr} {cg} {cb} {ca}, want {er} {eg} {eb} {ea}"
        ok := false
    return ok

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/csp_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let ok ← checkLine line (idx + 1)
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} lines checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "csp differential mismatch")
