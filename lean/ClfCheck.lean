/-
  TinyEXR - CLF differential checker (C vs Lean).
  Reads vectors from `test/v3/clf_vectors.c` (C `toc_load_clf` results
  plus applied pixels and the hex-encoded source), re-parses with Lean
  `loadClf`, compares op contents bit-for-bit and applies the ops
  through the Lean kernels.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Clf
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

/-- Read the next n hex floats from the token list at position i. -/
def readF32s (toks : List String) (i n : Nat) : List Float32 × Nat :=
  let vals := (List.range n).map (fun k => f32 (toks.getD (i + k) ""))
  (vals, i + n)

/-- Apply one parsed op (Lean content) to a pixel, for output parity. -/
def applyOp (op : ClfOp) (px : Pixel) : Pixel :=
  match op with
  | .matrix m off => applyMatrix m off px
  | .range scale off mn mx clLo clHi => applyRange scale off mn mx clLo clHi px
  | .exponent e mirror => applyExponent e mirror 4 px
  | .expLinear sc off g br sl inv mir => applyExpLinear sc off g br sl inv mir 4 px
  | .log base inv ls lo ns no => applyLog base ls lo ns no inv 4 px
  | .logCam base inv ls lo ns no br ls2 lo2 =>
    applyLogCam base ls lo ns no br ls2 lo2 inv 4 px
  | .cdl sl of pw sat cl => applyCdl sl of pw sat [0.0, 0.0, 0.0] cl false px
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

def checkLine (line : String) (n : Nat) : IO Bool := do
  let sections := line.splitOn "|"
  let head := sections.getD 0 ""
  let outp := sections.getD 1 ""
  let srcs := sections.getD (sections.length - 1) ""
  let hp := fields head
  let src := fromHex srcs
  if (hp.getD 1 "") == "fail" then
    let want := hp.getD 2 ""
    match loadClf src with
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
  let mut wantOps : List (String × List Float32 × List Float32 × List Float32 × List Float32 ×
      List Float32 × List Float32 × List Float32 × List Float32 × Nat × Nat) := []
  for _ in List.range nops do
    let kind := hp.getD idx ""
    idx := idx + 1
    if kind == "matrix" then
      let (m, i1) := readF32s hp idx 16
      let (off, i2) := readF32s hp i1 4
      wantOps := wantOps ++ [("matrix", m, off, [], [], [], [], [], [], 0, 0)]
      idx := i2
    else if kind == "range" then
      let (scale, i1) := readF32s hp idx 4
      let (off, i2) := readF32s hp i1 4
      let (mn, i3) := readF32s hp i2 4
      let (mx, i4) := readF32s hp i3 4
      let cl := decNum (hp.getD i4 "")
      let ch := decNum (hp.getD (i4 + 1) "")
      wantOps := wantOps ++ [("range", scale, off, mn, mx, [], [], [], [], cl, ch)]
      idx := i4 + 2
    else if kind == "exponent" then
      let (e, i1) := readF32s hp idx 4
      let mir := decNum (hp.getD i1 "")
      wantOps := wantOps ++ [("exponent", e, [], [], [], [], [], [], [], mir, 0)]
      idx := i1 + 1
    else if kind == "lut1d" then
      let ln := decNum (hp.getD idx "")
      let (data, i1) := readF32s hp (idx + 1) (ln * 3)
      wantOps := wantOps ++ [("lut1d", data, [], [], [], [], [], [], [], ln, 0)]
      idx := i1
    else if kind == "lut3d" then
      let sz := decNum (hp.getD idx "")
      let tetra := decNum (hp.getD (idx + 1) "")
      let (data, i2) := readF32s hp (idx + 2) (sz * sz * sz * 3)
      wantOps := wantOps ++ [("lut3d", data, [], [], [], [], [], [], [], sz, tetra)]
      idx := i2
    else if kind == "explin" then
      let (sc, i1) := readF32s hp idx 4
      let (off, i2) := readF32s hp i1 4
      let (g, i3) := readF32s hp i2 4
      let (br, i4) := readF32s hp i3 4
      let (sl, i5) := readF32s hp i4 4
      let inv := decNum (hp.getD i5 "")
      let mir := decNum (hp.getD (i5 + 1) "")
      wantOps := wantOps ++ [("explin", sc, off, g, br, sl, [], [], [], inv, mir)]
      idx := i5 + 2
    else if kind == "log" then
      let (base, i1) := readF32s hp idx 1
      let inv := decNum (hp.getD i1 "")
      let (ls, i2) := readF32s hp (i1 + 1) 3
      let (lo, i3) := readF32s hp i2 3
      let (ns, i4) := readF32s hp i3 3
      let (no, i5) := readF32s hp i4 3
      wantOps := wantOps ++ [("log", base, ls, lo, ns, no, [], [], [], inv, 0)]
      idx := i5
    else if kind == "logcam" then
      let (base, i1) := readF32s hp idx 1
      let inv := decNum (hp.getD i1 "")
      let (ls, i2) := readF32s hp (i1 + 1) 3
      let (lo, i3) := readF32s hp i2 3
      let (ns, i4) := readF32s hp i3 3
      let (no, i5) := readF32s hp i4 3
      let (br, i6) := readF32s hp i5 3
      let (ls2, i7) := readF32s hp i6 3
      let (lo2, i8) := readF32s hp i7 3
      wantOps := wantOps ++ [("logcam", base, ls, lo, ns, no, br, ls2, lo2, inv, 0)]
      idx := i8
    else if kind == "cdl" then
      let (sl, i1) := readF32s hp idx 3
      let (of, i2) := readF32s hp i1 3
      let (pw, i3) := readF32s hp i2 3
      let (sat, i4) := readF32s hp i3 1
      let cl := decNum (hp.getD i4 "")
      wantOps := wantOps ++ [("cdl", sl, of, pw, sat, [], [], [], [], cl, 0)]
      idx := i4 + 1
    else
      IO.eprintln s!"line {n}: unknown op kind {kind}"
      ok := false
  let npix := (fields outp).length / 4
  match loadClf src with
  | Except.error e =>
    IO.eprintln s!"line {n}: C ok, Lean {e}"
    return false
  | Except.ok ops =>
    if ops.length != nops then
      IO.eprintln s!"line {n}: op count got {ops.length}, want {nops}"
      ok := false
    for (i, w) in List.zip (List.range nops) wantOps do
      let (kind, a, b, c, d, e, f, g, h, fl1, fl2) := w
      match ops[i]? with
      | none => pure ()
      | some op =>
        match kind with
        | "matrix" =>
          match op with
          | .matrix m off =>
            for (k, v) in List.zip (List.range 16) a do
              if Float32.toBits (m.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} matrix m[{k}]"
                ok := false
            for (k, v) in List.zip (List.range 4) b do
              if Float32.toBits (off.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} matrix off[{k}]"
                ok := false
          | _ => pure ()
        | "range" =>
          match op with
          | .range scale off mn mx clLo clHi =>
            for (k, v) in List.zip (List.range 4) a do
              if Float32.toBits (scale.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} range scale[{k}]"
                ok := false
            for (k, v) in List.zip (List.range 4) b do
              if Float32.toBits (off.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} range offset[{k}]"
                ok := false
            for (k, v) in List.zip (List.range 4) c do
              if Float32.toBits (mn.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} range min[{k}]"
                ok := false
            for (k, v) in List.zip (List.range 4) d do
              if Float32.toBits (mx.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} range max[{k}]"
                ok := false
            if clLo != (fl1 == 1) || clHi != (fl2 == 1) then
              IO.eprintln s!"line {n} op {i} range clamps"
              ok := false
          | _ => pure ()
        | "exponent" =>
          match op with
          | .exponent en mir =>
            for (k, v) in List.zip (List.range 4) a do
              if Float32.toBits (en.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} exponent e[{k}] got {en.getD k 0.0}, want {v}"
                ok := false
            if mir != (fl1 == 1) then
              IO.eprintln s!"line {n} op {i} exponent mirror"
              ok := false
          | _ => pure ()
        | "lut1d" =>
          match op with
          | .lut1d ln d =>
            if ln != fl1 then
              IO.eprintln s!"line {n} op {i} lut1d length got {ln}, want {fl1}"
              ok := false
            for (k, v) in List.zip (List.range a.length) a do
              if Float32.toBits (d.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} lut1d data[{k}]"
                ok := false
          | _ => pure ()
        | "lut3d" =>
          match op with
          | .lut3d sz d tetra =>
            if sz != fl1 then
              IO.eprintln s!"line {n} op {i} lut3d size got {sz}, want {fl1}"
              ok := false
            if tetra != (fl2 == 2) then
              IO.eprintln s!"line {n} op {i} lut3d tetra"
              ok := false
            for (k, v) in List.zip (List.range a.length) a do
              if Float32.toBits (d.getD k 0.0) != Float32.toBits v then
                IO.eprintln s!"line {n} op {i} lut3d data[{k}] got {d.getD k 0.0}, want {v}"
                ok := false
          | _ => pure ()
        | "explin" =>
          match op with
          | .expLinear sc off g br sl inv mir =>
            let groups := [("scale", sc, 4, a), ("offset", off, 4, b), ("gamma", g, 4, c),
              ("breakpoint", br, 4, d), ("slope", sl, 4, e)]
            for (nm, arr, cnt, wv) in groups do
              for (k, v) in List.zip (List.range cnt) wv do
                if Float32.toBits (arr.getD k 0.0) != Float32.toBits v then
                  IO.eprintln s!"line {n} op {i} explin {nm}[{k}] got {arr.getD k 0.0}, want {v}"
                  ok := false
            if inv != (fl1 == 1) || mir != (fl2 == 1) then
              IO.eprintln s!"line {n} op {i} explin flags"
              ok := false
          | _ => pure ()
        | "log" =>
          match op with
          | .log base inv ls lo ns no =>
            if Float32.toBits base != Float32.toBits (a.getD 0 0.0) ||
               inv != (fl1 == 1) then
              IO.eprintln s!"line {n} op {i} log base/flags"
              ok := false
            let groups := [("ls", ls, 3, b), ("lo", lo, 3, c), ("ns", ns, 3, d), ("no", no, 3, e)]
            for (nm, arr, cnt, wv) in groups do
              for (k, v) in List.zip (List.range cnt) wv do
                if Float32.toBits (arr.getD k 0.0) != Float32.toBits v then
                  IO.eprintln s!"line {n} op {i} log {nm}[{k}]"
                  ok := false
          | _ => pure ()
        | "logcam" =>
          match op with
          | .logCam base inv ls lo ns no br ls2 lo2 =>
            if Float32.toBits base != Float32.toBits (a.getD 0 0.0) ||
               inv != (fl1 == 1) then
              IO.eprintln s!"line {n} op {i} logcam base/flags"
              ok := false
            let groups := [("ls", ls, 3, b), ("lo", lo, 3, c), ("ns", ns, 3, d),
              ("no", no, 3, e), ("br", br, 3, f), ("ls2", ls2, 3, g),
              ("lo2", lo2, 3, h)]
            for (nm, arr, cnt, wv) in groups do
              for (k, v) in List.zip (List.range cnt) wv do
                if Float32.toBits (arr.getD k 0.0) != Float32.toBits v then
                  IO.eprintln s!"line {n} op {i} logcam {nm}[{k}] got {arr.getD k 0.0}, want {v}"
                  ok := false
          | _ => pure ()
        | "cdl" =>
          match op with
          | .cdl sl of pw sat cl =>
            let groups := [("slope", sl, 3, a), ("offset", of, 3, b), ("power", pw, 3, c),
              ("saturation", [sat], 1, d)]
            for (nm, arr, cnt, wv) in groups do
              for (k, v) in List.zip (List.range cnt) wv do
                if Float32.toBits (arr.getD k 0.0) != Float32.toBits v then
                  IO.eprintln s!"line {n} op {i} cdl {nm}[{k}]"
                  ok := false
            if cl != (fl1 == 1) then
              IO.eprintln s!"line {n} op {i} cdl clamp"
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
  let path := args.getD 0 "/tmp/opencode/clf_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let ok ← checkLine line (idx + 1)
    if !ok then bad := bad + 1
  IO.println s!"{lines.length} lines checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "clf differential mismatch")
