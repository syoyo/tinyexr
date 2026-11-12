/-
  TinyEXR - Lean 4 formalization of the tocio AOT-C codegen
  (`toc_codegen_c.c`).

  The emitter is ported 1:1 so the `tocio-codegen-diff` gate can compare
  generated sources byte-for-byte: op parameters travel as IEEE-754 bit
  patterns, the hex-float literal writer reproduces `toc_sb_hexfloat`
  exactly, and the helper snippets are the verbatim C strings
  (`Tocio/CodegenSnippets.lean`).

  Scope: the scalar path (`toc_codegen_c_opts.simd = 0`). The
  `LOG_CAMERA` op has no AOT-C case in the C either (it emits nothing).
  `ACES_GAMUTCOMP13` needs the codegen-time `cg_gc_scale` pow
  approximation and is reported UNSUPPORTED by the model (never
  vectorized).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.CodegenSnippets

namespace Tocio

set_option linter.unusedVariables false

/-! ## Hex-float literals (`toc_sb_hexfloat`) -/

def hexDigChar (n : Nat) : Char :=
  "0123456789abcdef".toList.getD (n % 16) '0'

/-- Bit-exact clone of `toc_sb_hexfloat`: `-0x1.abcp+3f` style literals,
heading zeros trimmed, zero as `0x0p+0f`, inf/nan placeholders. -/
def hexFloat (u : UInt32) : String :=
  let sign := u >>> 31
  let exp := (u >>> 23) &&& 0xFF
  let mant := u &&& 0x7FFFFF
  let neg := sign != 0 && !(exp == 0 && mant == 0)
  let s := if neg then "-" else ""
  if exp == 0xFF then
    s ++ (if mant != 0 then "(0.0f/0.0f)" else "3.4028235e38f")
  else if exp == 0 && mant == 0 then s ++ "0x0p+0f"
  else
    let leading : Nat := if exp == 0 then 0 else 1
    let e : Int := if exp == 0 then -126 else (exp.toNat : Int) - 127
    let frac24 : UInt32 := mant <<< 1
    let nibbles : List Nat :=
      (List.range 6).map (fun i => ((frac24 >>> (UInt32.ofNat (20 - 4 * i))) &&& 0xF).toNat)
    let trimmed := nibbles.reverse.dropWhile (· == 0) |>.reverse
    let fracStr :=
      if trimmed.isEmpty then ""
      else "." ++ String.ofList (trimmed.map hexDigChar)
    let eAbs : Nat := e.natAbs
    s ++ "0x" ++ toString leading ++ fracStr ++ "p" ++
      (if e >= 0 then "+" else "-") ++ toString eAbs ++ "f"

/-! ## Ops with bit-pattern parameters -/

/-- A float parameter as its IEEE-754 bit pattern. -/
abbrev FB := UInt32

def fget (l : List FB) (i : Nat) : FB := l.getD i 0

def f32of (b : FB) : Float32 := Float32.ofBits b
def fbits (f : Float32) : FB := Float32.toBits f

/-- A lowered op with all numeric parameters as bit patterns. -/
inductive COp where
  | matrix (m : List FB) (off : List FB)
  | range (scale offset lo hi : List FB) (clampLo clampHi : Bool)
  | exponent (e : List FB) (mirror : Bool)
  | expLinear (scale offset gamma brk slope : List FB) (inverse mirror : Bool)
  | cdl (slope offset power : List FB) (sat : FB) (luma : List FB)
        (clamp inverse : Bool)
  | lut1d (len ch : Nat) (dmin dmax : FB) (data : List FB)
  | lut3d (size : Nat) (dmin dmax : List FB) (tet : Bool) (data : List FB)
  | fixed (style : Nat) (nparams : Nat) (params : List FB)
  | log (logSlope logOffset linSlope linOffset : List FB) (base : FB)
        (inverse : Bool)
  | logCamera

def chanName : Nat → String
  | 0 => "r"
  | 1 => "g"
  | 2 => "b"
  | _ => "a"

/-! ## Per-op emitters -/

def emitMatrix (m off : List FB) : String :=
  let rows := [0, 1, 2, 3]
  let up := ["R", "G", "B", "A"]
  let line (r : Nat) : String :=
    "  " ++ up.getD r "?" ++ " = " ++
      hexFloat (fget m r) ++ "*r + " ++ hexFloat (fget m (4 + r)) ++ "*g + " ++
      hexFloat (fget m (8 + r)) ++ "*b + " ++ hexFloat (fget m (12 + r)) ++
      "*a + " ++ hexFloat (fget off r) ++ ";\n"
  "  { float R,G,B,A;\n" ++ String.join (rows.map line) ++
    "  r=R; g=G; b=B; a=A; }\n"

def emitRange (scale offset lo hi : List FB) (clampLo clampHi : Bool) : String :=
  let one (c : Nat) : String :=
    let v := chanName c
    "  " ++ v ++ " = " ++ v ++ "*" ++ hexFloat (fget scale c) ++ " + " ++
      hexFloat (fget offset c) ++ ";" ++
      (if clampLo then
        " if(" ++ v ++ "<" ++ hexFloat (fget lo c) ++ ") " ++ v ++ "=" ++
          hexFloat (fget lo c) ++ ";"
       else "") ++
      (if clampHi then
        " if(" ++ v ++ ">" ++ hexFloat (fget hi c) ++ ") " ++ v ++ "=" ++
          hexFloat (fget hi c) ++ ";"
       else "") ++ "\n"
  String.join ((List.range 4).map one)

def emitExponent (e : List FB) (mirror : Bool) : String :=
  let one (c : Nat) : String :=
    let v := chanName c
    "  " ++ v ++ " = " ++
      (if mirror then
        "(" ++ v ++ "<0.0f?-1.0f:1.0f)*tc_powf(" ++ v ++ "<0.0f?-" ++ v ++
          ":" ++ v ++ ", "
       else
        "tc_powf(" ++ v ++ ">0.0f?" ++ v ++ ":0.0f, ") ++
      hexFloat (fget e c) ++ ");\n"
  String.join ((List.range 4).map one)

def emitExpLinear (scale offset gamma brk slope : List FB)
    (inverse mirror : Bool) : String :=
  let one (c : Nat) : String :=
    let v := chanName c
    let iv := if mirror then "_a" else v
    "  " ++
      (if mirror then
        "{float _s=" ++ v ++ "<0.0f?-1.0f:1.0f,_a=" ++ v ++ "<0.0f?-" ++ v ++
          ":" ++ v ++ ";" ++ v ++ " = _s*(("
       else v ++ " = (") ++
      (if !inverse then
        iv ++ ">" ++ hexFloat (fget brk c) ++ ") ? tc_powf(" ++ iv ++ "*" ++
          hexFloat (fget scale c) ++ "+" ++ hexFloat (fget offset c) ++ ", " ++
          hexFloat (fget gamma c) ++ ") : " ++ iv ++ "*" ++
          hexFloat (fget slope c)
       else
        let bsl := fbits (f32of (fget brk c) * f32of (fget slope c))
        let invG := fbits (1.0 / f32of (fget gamma c))
        iv ++ ">" ++ hexFloat bsl ++ ") ? (tc_powf(" ++ iv ++ ", " ++
          hexFloat invG ++ ")-" ++ hexFloat (fget offset c) ++ ")/" ++
          hexFloat (fget scale c) ++ " : " ++ iv ++ "/" ++
          hexFloat (fget slope c)) ++
      (if mirror then ");}\n" else ";\n")
  String.join ((List.range 3).map one)

def emitLog (logSlope logOffset linSlope linOffset : List FB) (base : FB)
    (inverse : Bool) : String :=
  let one (c : Nat) : String :=
    let v := chanName c
    "  " ++ v ++ " = " ++
      (if !inverse then
        "(" ++ hexFloat (fget logSlope c) ++ "*tc_log2f((" ++
          hexFloat (fget linSlope c) ++ "*" ++ v ++ "+" ++
          hexFloat (fget linOffset c) ++ "))/tc_log2f(" ++ hexFloat base ++
          ")+" ++ hexFloat (fget logOffset c) ++ ")"
       else
        "(tc_raisef(" ++ hexFloat base ++ ", (" ++ v ++ "-" ++
          hexFloat (fget logOffset c) ++ ")/" ++ hexFloat (fget logSlope c) ++
          ")-" ++ hexFloat (fget linOffset c) ++ ")/" ++
          hexFloat (fget linSlope c)) ++ ";\n"
  String.join ((List.range 3).map one)

def isZero (b : FB) : Bool := f32of b == 0.0

def emitCdl (slope offset power : List FB) (sat : FB) (luma : List FB)
    (clamp inverse : Bool) : String :=
  let lr := if isZero (fget luma 0) && isZero (fget luma 1) && isZero (fget luma 2)
            then fbits (0.2126 : Float32) else fget luma 0
  let lg := if isZero (fget luma 0) && isZero (fget luma 1) && isZero (fget luma 2)
            then fbits (0.7152 : Float32) else fget luma 1
  let lb := if isZero (fget luma 0) && isZero (fget luma 1) && isZero (fget luma 2)
            then fbits (0.0722 : Float32) else fget luma 2
  if inverse then
    let v := "  { float v0,v1,v2,L;\n  L = " ++ hexFloat lr ++ "*r+" ++
      hexFloat lg ++ "*g+" ++ hexFloat lb ++ "*b;\n"
    let body (c : Nat) : String :=
      let s := f32of (fget slope c)
      let ipow := if isZero (fget power c) then fbits (1.0 : Float32)
                  else fbits ((1.0 : Float32) / f32of (fget power c))
      "  v" ++ toString c ++ " = L" ++
        (if !isZero sat then
          "+(" ++ chanName c ++ "-L)*" ++ hexFloat (fbits ((1.0 : Float32) / f32of sat))
         else "") ++ ";" ++
        (if clamp then
          " if(v" ++ toString c ++ "<0.0f)v" ++ toString c ++ "=0.0f; if(v" ++
            toString c ++ ">1.0f)v" ++ toString c ++ "=1.0f;"
         else "") ++
        " v" ++ toString c ++ "=v" ++ toString c ++ ">=0.0f?tc_powf(v" ++
          toString c ++ ", " ++ hexFloat ipow ++ "):v" ++ toString c ++ ";\n  " ++
          chanName c ++ " = (v" ++ toString c ++ "+" ++
          hexFloat (fbits (-(f32of (fget offset c)))) ++ ")*" ++
          hexFloat (if isZero (fget slope c) then fbits (1.0 : Float32)
                    else fbits (1.0 / s)) ++ ";\n"
    v ++ String.join ((List.range 3).map body) ++ "  }\n"
  else
    let pre := "  { float v0,v1,v2,L;\n"
    let body (c : Nat) : String :=
      "  v" ++ toString c ++ " = " ++ chanName c ++ "*" ++
        hexFloat (fget slope c) ++ "+" ++ hexFloat (fget offset c) ++ ";" ++
        (if clamp then
          " if(v" ++ toString c ++ "<0.0f)v" ++ toString c ++ "=0.0f; if(v" ++
            toString c ++ ">1.0f)v" ++ toString c ++ "=1.0f;"
         else "") ++
        " v" ++ toString c ++ "=v" ++ toString c ++ ">=0.0f?tc_powf(v" ++
          toString c ++ ", " ++ hexFloat (fget power c) ++ "):v" ++
          toString c ++ ";\n"
    let post := "  L = " ++ hexFloat lr ++ "*v0+" ++ hexFloat lg ++ "*v1+" ++
      hexFloat lb ++ "*v2;\n"
    let out (c : Nat) : String :=
      "  " ++ chanName c ++ " = L+" ++ hexFloat sat ++ "*(v" ++ toString c ++
        "-L);" ++
        (if clamp then
          " if(" ++ chanName c ++ "<0.0f)" ++ chanName c ++ "=0.0f; if(" ++
            chanName c ++ ">1.0f)" ++ chanName c ++ "=1.0f;"
         else "") ++ "\n"
    pre ++ String.join ((List.range 3).map body) ++ post ++
      String.join ((List.range 3).map out) ++ "  }\n"

def emitLutArray (idx : Nat) (data : List FB) : String :=
  "static const float tc_lut" ++ toString idx ++ "[] = {" ++
    String.intercalate "," (data.map hexFloat) ++ "};\n"

/-! ## Fixed-function cases -/

def ffYc : List FB :=
  [fbits (0.2627 : Float32), fbits (0.6780 : Float32), fbits (0.0593 : Float32)]

/-- A fixed-function op's emitted statement (or UNSUPPORTED for
GamutComp13, whose codegen-time scale needs the pow approximation). -/
def emitFixed (style : Nat) (nparams : Nat) (p : List FB) :
    Except String String :=
  if style == 6 || style == 7 then
    let g := f32of (fget p 0)
    let inv := style == 7
    let e := if inv then fbits (1.0 / g - 1.0) else fbits (g - 1.0)
    .ok ("  { float Y=" ++ hexFloat (fget ffYc 0) ++ "*r+" ++
      hexFloat (fget ffYc 1) ++ "*g+" ++ hexFloat (fget ffYc 2) ++ "*b;" ++
      "if(Y>0.0f){float s=tc_powf(Y," ++ hexFloat e ++
      ");r*=s;g*=s;b*=s;}}\n")
  else if nparams >= 2 && (style == 8 || style == 9 || style == 0 || style == 1) then
    let inv := style == 9 || style == 1
    .ok ("  { float c[3]={r,g,b};tc_glow(c," ++ hexFloat (fget p 0) ++ "," ++
      hexFloat (fget p 1) ++ (if inv then ",1);" else ",0);") ++
      " r=c[0];g=c[1];b=c[2];}\n")
  else if style == 2 || style == 3 then
    let g := f32of (fget p 0)
    let gamma := if style == 3 then fbits (1.0 / g) else fbits g
    .ok ("  { float c[3]={r,g,b};tc_darktodim(c," ++ hexFloat gamma ++
      "); r=c[0];g=c[1];b=c[2];}\n")
  else if nparams >= 6 && (style == 4 || style == 5) then
    .error "UNSUPPORTED"
  else if style == 10 || style == 11 || style == 12 || style == 13 then
    let is03 := style == 10 || style == 11
    let inv := style == 11 || style == 13
    .ok ("  { float c[3]={r,g,b};tc_redmod(c," ++
      hexFloat (fbits (if is03 then (0.85 : Float32) else (0.82 : Float32))) ++
      ",0.03f," ++
      hexFloat (fbits (if is03 then (1.9098593171027443 : Float32)
                       else (1.6976527263135504 : Float32))) ++
      (if inv then ",1);" else ",0);") ++ " r=c[0];g=c[1];b=c[2];}\n")
  else if style == 14 || style == 15 then
    .ok ("  { float c[3]={r,g,b};" ++
      (if style == 14 then "tc_rgb2hsv(c);" else "tc_hsv2rgb(c);") ++
      " r=c[0];g=c[1];b=c[2];}\n")
  else if style >= 16 && style <= 21 then
    let idx := if style == 16 || style == 17 then 0
               else if style == 18 || style == 19 then 1
               else if style == 20 || style == 21 then 2 else 0
    let inv := style == 17 || style == 19 || style == 21
    let fn := match idx, inv with
      | 0, false => "tc_xyz2xyy(c)"
      | 0, true => "tc_xyy2xyz(c)"
      | 1, false => "tc_xyz2uvy(c)"
      | 1, true => "tc_uvy2xyz(c)"
      | 2, false => "tc_xyz2luv(c)"
      | _, true => "tc_luv2xyz(c)"
      | _, false => "tc_xyz2luv(c)"
    .ok ("  { float c[3]={r,g,b};" ++ fn ++ "; r=c[0];g=c[1];b=c[2];}\n")
  else if style >= 22 && style <= 25 then
    let fn := if style == 22 then "tc_pq_enc"
              else if style == 23 then "tc_pq_dec"
              else if style == 24 then "tc_hlg_enc" else "tc_hlg_dec"
    .ok ("  r=" ++ fn ++ "(r); g=" ++ fn ++ "(g); b=" ++ fn ++ "(b);\n")
  else
    .ok ""

/-! ## Assembly (`toc_emit_c`, scalar path) -/

def validFname (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    ((c ≥ 'A' && c ≤ 'Z') || (c ≥ 'a' && c ≤ 'z') || c == '_') &&
    rest.length < 128 &&
    rest.all (fun c => (c ≥ 'A' && c ≤ 'Z') || (c ≥ 'a' && c ≤ 'z') ||
      (c ≥ '0' && c ≤ '9') || c == '_')

/-- Which helper snippets an op list needs (the C's pre-scan). -/
structure Needs where
  math : Bool := false
  lut1d : Bool := false
  lut3d : Bool := false
  glow : Bool := false
  darktodim : Bool := false
  rgbhsv : Bool := false
  xyz : Bool := false
  hdr : Bool := false
  aces : Bool := false
  deriving Repr

def Needs.forOp (n : Needs) (op : COp) : Needs :=
  match op with
  | .exponent .. | .expLinear .. | .log .. | .cdl .. => { n with math := true }
  | .lut1d .. => { n with lut1d := true }
  | .lut3d .. => { n with lut3d := true }
  | .fixed style .. =>
    let n :=
      if style == 0 || style == 1 || style == 8 || style == 9 then
        { n with glow := true } else n
    let n := if style == 2 || style == 3 then { n with darktodim := true } else n
    let n := if style == 4 || style == 5 then { n with math := true, aces := true } else n
    let n := if style >= 10 && style <= 13 then { n with math := true, aces := true } else n
    let n := if style == 14 || style == 15 then { n with rgbhsv := true } else n
    let n := if style >= 16 && style <= 21 then { n with xyz := true } else n
    let n := if style >= 22 && style <= 25 then { n with hdr := true, math := true } else n
    n
  | _ => n

def preamble : String :=
  "/* Generated by tocio. SPDX-License-Identifier: BSD-3-Clause.\n" ++
  " * Color math reimplemented from OpenColorIO (BSD-3-Clause).\n" ++
  " */\n#include <stddef.h>\n"

def emitOp (k : Nat) (op : COp) : Except String String :=
  match op with
  | .matrix m off => .ok (emitMatrix m off)
  | .range scale offset lo hi cl hi' => .ok (emitRange scale offset lo hi cl hi')
  | .exponent e mirror => .ok (emitExponent e mirror)
  | .expLinear scale offset gamma brk slope inv mirror =>
    .ok (emitExpLinear scale offset gamma brk slope inv mirror)
  | .log ls lo ns no base inv => .ok (emitLog ls lo ns no base inv)
  | .logCamera => .ok ""
  | .cdl slope off power sat luma clamp inv =>
    .ok (emitCdl slope off power sat luma clamp inv)
  | .lut1d len ch dmin dmax _ =>
    .ok ("  { float c[3]={r,g,b}; tc_lut1d(tc_lut" ++ toString k ++ ", " ++
      toString len ++ ", " ++ toString ch ++ ", " ++ hexFloat dmin ++ ", " ++
      hexFloat dmax ++ ", c); r=c[0];g=c[1];b=c[2]; }\n")
  | .lut3d size dmin dmax tet _ =>
    .ok ("  { float c[3]={r,g,b}; static const float dn[3]={" ++
      hexFloat (fget dmin 0) ++ "," ++ hexFloat (fget dmin 1) ++ "," ++
      hexFloat (fget dmin 2) ++ "},dx[3]={" ++
      hexFloat (fget dmax 0) ++ "," ++ hexFloat (fget dmax 1) ++ "," ++
      hexFloat (fget dmax 2) ++ "}; tc_lut3d(tc_lut" ++ toString k ++ ", " ++
      toString size ++ ", dn, dx, " ++ (if tet then "1" else "0") ++
      ", c); r=c[0];g=c[1];b=c[2]; }\n")
  | .fixed style nparams params => emitFixed style nparams params

def emitLutArrays (ops : List COp) : String :=
  let rec go : List (Nat × COp) → String
    | [] => ""
    | (i, op) :: rest =>
      match op with
      | .lut1d len ch _ _ data =>
        emitLutArray i (data.take (len * (if ch == 1 then 1 else 3))) ++ go rest
      | .lut3d size _ _ _ data =>
        emitLutArray i (data.take (size * size * size * 3)) ++ go rest
      | _ => go rest
  go (List.zip (List.range ops.length) ops)

def emitBody (ops : List COp) : Except String String :=
  let rec go : List (Nat × COp) → Except String String
    | [] => .ok ""
    | (i, op) :: rest =>
      (emitOp i op).bind (fun s => (go rest).map (fun t => s ++ t))
  go (List.zip (List.range ops.length) ops)

/-- `toc_emit_c` for the scalar path and default function name. -/
def emitC (fname : String) (ops : List COp) : Except String String :=
  if !validFname fname then .error "INVALID_ARGUMENT"
  else
    let needs := ops.foldl Needs.forOp {}
    let pre := preamble ++
      (if needs.math then MATH_SRC else "") ++
      (if needs.lut1d then LUT1D_SRC else "") ++
      (if needs.lut3d then LUT3D_SRC else "") ++
      (if needs.glow then FIXEDFUNC_SRC_GLOW else "") ++
      (if needs.darktodim then FIXEDFUNC_SRC_DARKTODIM else "") ++
      (if needs.rgbhsv then FIXEDFUNC_SRC_RGB2HSV else "") ++
      (if needs.xyz then FIXEDFUNC_SRC_XYZ else "") ++
      (if needs.hdr then FIXEDFUNC_SRC_HDR else "") ++
      (if needs.aces then FIXEDFUNC_SRC_ACES else "") ++
      emitLutArrays ops
    let head := "void " ++ fname ++ "(float *rgba, size_t npix){\n  size_t i;\n" ++
      "  for(i=0;i<npix;++i){\n  float *px=rgba+i*4;\n" ++
      "  float r=px[0],g=px[1],b=px[2],a=px[3];\n"
    let tail := "  px[0]=r;px[1]=g;px[2]=b;px[3]=a;\n  }\n}\n"
    emitBody ops |>.map (fun b => pre ++ head ++ b ++ tail)

end Tocio
