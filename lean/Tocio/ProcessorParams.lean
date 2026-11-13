/-
  TinyEXR - Lean 4 formalization of the tocio processor lowering
  (`toc_processor.c`): numeric op parameters.

  These helpers pin the *numeric* side of the processor build: matrix
  inversion (`toc_inv4x4`, generated here with the C's exact evaluation
  order), `read_vec`/`read_scalar` parameter reads, MonCurve parameter
  derivation, Log/LogCamera fields, the CDL inverse decomposition
  (saturation matrix, inverse power, inverse slope/offset) and the
  Range inverse. All arithmetic is IEEE single precision on bit
  patterns, so `tocio-proc-params-diff` compares parameter recipes
  byte-for-byte.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ConfigQuery
import Tocio.CodegenC

namespace Tocio

set_option linter.unusedVariables false

/-! ## Scalar parsing (`toc_parse_float`) -/

def isDigit (c : Char) : Bool := c ≥ '0' && c ≤ '9'

def digitVal (c : Char) : Float := (c.toNat - '0'.toNat).toFloat

/-- The fractional part: digits after the point, each divided by the
running power of ten (the C's `frac` accumulation). -/
def parseFrac : List Char → Float → Float
  | [], _ => 0.0
  | c :: rest, sc => digitVal c / sc + parseFrac rest (sc * 10.0)

/-- `toc_parse_float`'s grammar (leading spaces/commas, optional sign,
digits with an optional fraction, optional exponent). -/
def parseCfgFloat (s : String) : Option Float :=
  let cs := s.toList.dropWhile
    (fun c => c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == ',')
  let (neg, cs) :=
    match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let intPart := cs.takeWhile isDigit
  let cs1 := cs.drop intPart.length
  let (fracPart, cs2) :=
    match cs1 with
    | '.' :: r => (r.takeWhile isDigit, r.drop (r.takeWhile isDigit).length)
    | _ => ([], cs1)
  if intPart.isEmpty && fracPart.isEmpty then none
  else
    let v := intPart.foldl (fun a c => a * 10.0 + digitVal c) 0.0
    let frac := parseFrac fracPart 10.0
    let base := (v + frac) * (if neg then -1.0 else 1.0)
    match cs2 with
    | 'e' :: r => applyExp base r
    | 'E' :: r => applyExp base r
    | _ => some base
where
  applyExp (base : Float) (r : List Char) : Option Float :=
    let (esign, r) :=
      match r with
      | '-' :: r' => (true, r')
      | '+' :: r' => (false, r')
      | r' => (false, r')
    let ds := r.takeWhile isDigit
    if ds.isEmpty then some base
    else
      let exp := ds.foldl (fun a c => if a < 10000 then a * 10 + (c.toNat - '0'.toNat) else a) 0
      let m := (List.range (min exp 400)).foldl (fun a _ => a * 10.0) 1.0
      some (if esign then base / m else base * m)

/-! ## Float helpers on bit patterns -/

def fuget (l : List FB) (i : Nat) : FB := l.getD i 0
def fadd (a b : FB) : FB := fbits (f32of a + f32of b)
def fsub (a b : FB) : FB := fbits (f32of a - f32of b)
def fmul (a b : FB) : FB := fbits (f32of a * f32of b)
def fdiv (a b : FB) : FB := fbits (f32of a / f32of b)
def fneg (a : FB) : FB := fbits (-(f32of a))
def fzero (a : FB) : Bool := f32of a == 0.0
def fconst (x : Float32) : FB := fbits x

/-- `1.0f / x` (or `1.0f` when x is zero), the C's guard pattern. -/
def finv (a : FB) : FB := if fzero a then fbits (1.0 : Float32) else fdiv (fbits (1.0 : Float32)) a

/-- The node's `!<Tag>`. -/
def tagOf : YTree → Option String
  | .scalar t _ => t
  | .seq t _ => t
  | .map t _ => t

/-- A float scalar's value (parse failure or non-scalar -> 0). -/
def nodeFloat (o : Option YTree) : FB :=
  match o with
  | some (.scalar _ s) => (parseCfgFloat s).map (fun d => fbits (Float.toFloat32 d)) |>.getD 0
  | _ => 0

/-- `read_vec`: fills `maxn` entries from a sequence (lanes past the
sequence keep the default) or broadcasts a scalar; returns the count the
C reports. -/
def readVec (node : YTree) (key : String) (maxn : Nat) (dflt : List FB) :
    List FB × Nat :=
  match node.mapGet key with
  | none => (dflt, 0)
  | some (.seq _ xs) =>
    let n := min xs.length maxn
    let vals := (List.range maxn).map (fun i =>
      if i < n then nodeFloat (xs[i]?) else fuget dflt i)
    (vals, n)
  | some (.scalar _ s) =>
    let f : FB := (parseCfgFloat s).map (fun d => fbits (Float.toFloat32 d)) |>.getD 0
    ((List.range maxn).map (fun _ => f), 1)
  | _ => (dflt, 0)

/-- `read_vec2`: snake_case first, then camelCase. -/
def readVec2 (node : YTree) (snake camel : String) (maxn : Nat) (dflt : List FB) :
    List FB × Nat :=
  let (v, n) := readVec node snake maxn dflt
  if n != 0 then (v, n) else readVec node camel maxn dflt

/-- `read_scalar`: the default when the key is absent or unparsable. -/
def readScalarD (node : YTree) (key : String) (dflt : FB) : FB :=
  match node.mapGet key with
  | some (.scalar _ s) =>
    (parseCfgFloat s).map (fun d => fbits (Float.toFloat32 d)) |>.getD dflt
  | _ => dflt

/-! ## 4x4 inversion and matvec (`toc_inv4x4`, `matvec4`) -/

/-- `toc_inv4x4` with the C's exact evaluation order (row-major input). -/
def inv4x4 (m : List FB) : Option (List FB) :=
  let g (i : Nat) := fuget m i
  let i0 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 5) (g 10)) (g 15)) (fmul (fmul (g 5) (g 11)) (g 14))) (fmul (fmul (g 9) (g 6)) (g 15))) (fmul (fmul (g 9) (g 7)) (g 14))) (fmul (fmul (g 13) (g 6)) (g 11))) (fmul (fmul (g 13) (g 7)) (g 10)))
  let i1 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 1)) (g 10)) (g 15)) (fmul (fmul (g 1) (g 11)) (g 14))) (fmul (fmul (g 9) (g 2)) (g 15))) (fmul (fmul (g 9) (g 3)) (g 14))) (fmul (fmul (g 13) (g 2)) (g 11))) (fmul (fmul (g 13) (g 3)) (g 10)))
  let i2 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 1) (g 6)) (g 15)) (fmul (fmul (g 1) (g 7)) (g 14))) (fmul (fmul (g 5) (g 2)) (g 15))) (fmul (fmul (g 5) (g 3)) (g 14))) (fmul (fmul (g 13) (g 2)) (g 7))) (fmul (fmul (g 13) (g 3)) (g 6)))
  let i3 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 1)) (g 6)) (g 11)) (fmul (fmul (g 1) (g 7)) (g 10))) (fmul (fmul (g 5) (g 2)) (g 11))) (fmul (fmul (g 5) (g 3)) (g 10))) (fmul (fmul (g 9) (g 2)) (g 7))) (fmul (fmul (g 9) (g 3)) (g 6)))
  let i4 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 4)) (g 10)) (g 15)) (fmul (fmul (g 4) (g 11)) (g 14))) (fmul (fmul (g 8) (g 6)) (g 15))) (fmul (fmul (g 8) (g 7)) (g 14))) (fmul (fmul (g 12) (g 6)) (g 11))) (fmul (fmul (g 12) (g 7)) (g 10)))
  let i5 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 0) (g 10)) (g 15)) (fmul (fmul (g 0) (g 11)) (g 14))) (fmul (fmul (g 8) (g 2)) (g 15))) (fmul (fmul (g 8) (g 3)) (g 14))) (fmul (fmul (g 12) (g 2)) (g 11))) (fmul (fmul (g 12) (g 3)) (g 10)))
  let i6 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 0)) (g 6)) (g 15)) (fmul (fmul (g 0) (g 7)) (g 14))) (fmul (fmul (g 4) (g 2)) (g 15))) (fmul (fmul (g 4) (g 3)) (g 14))) (fmul (fmul (g 12) (g 2)) (g 7))) (fmul (fmul (g 12) (g 3)) (g 6)))
  let i7 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 0) (g 6)) (g 11)) (fmul (fmul (g 0) (g 7)) (g 10))) (fmul (fmul (g 4) (g 2)) (g 11))) (fmul (fmul (g 4) (g 3)) (g 10))) (fmul (fmul (g 8) (g 2)) (g 7))) (fmul (fmul (g 8) (g 3)) (g 6)))
  let i8 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 4) (g 9)) (g 15)) (fmul (fmul (g 4) (g 11)) (g 13))) (fmul (fmul (g 8) (g 5)) (g 15))) (fmul (fmul (g 8) (g 7)) (g 13))) (fmul (fmul (g 12) (g 5)) (g 11))) (fmul (fmul (g 12) (g 7)) (g 9)))
  let i9 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 0)) (g 9)) (g 15)) (fmul (fmul (g 0) (g 11)) (g 13))) (fmul (fmul (g 8) (g 1)) (g 15))) (fmul (fmul (g 8) (g 3)) (g 13))) (fmul (fmul (g 12) (g 1)) (g 11))) (fmul (fmul (g 12) (g 3)) (g 9)))
  let i10 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 0) (g 5)) (g 15)) (fmul (fmul (g 0) (g 7)) (g 13))) (fmul (fmul (g 4) (g 1)) (g 15))) (fmul (fmul (g 4) (g 3)) (g 13))) (fmul (fmul (g 12) (g 1)) (g 7))) (fmul (fmul (g 12) (g 3)) (g 5)))
  let i11 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 0)) (g 5)) (g 11)) (fmul (fmul (g 0) (g 7)) (g 9))) (fmul (fmul (g 4) (g 1)) (g 11))) (fmul (fmul (g 4) (g 3)) (g 9))) (fmul (fmul (g 8) (g 1)) (g 7))) (fmul (fmul (g 8) (g 3)) (g 5)))
  let i12 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 4)) (g 9)) (g 14)) (fmul (fmul (g 4) (g 10)) (g 13))) (fmul (fmul (g 8) (g 5)) (g 14))) (fmul (fmul (g 8) (g 6)) (g 13))) (fmul (fmul (g 12) (g 5)) (g 10))) (fmul (fmul (g 12) (g 6)) (g 9)))
  let i13 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 0) (g 9)) (g 14)) (fmul (fmul (g 0) (g 10)) (g 13))) (fmul (fmul (g 8) (g 1)) (g 14))) (fmul (fmul (g 8) (g 2)) (g 13))) (fmul (fmul (g 12) (g 1)) (g 10))) (fmul (fmul (g 12) (g 2)) (g 9)))
  let i14 := (fadd (fsub (fsub (fadd (fadd (fmul (fmul (fneg (g 0)) (g 5)) (g 14)) (fmul (fmul (g 0) (g 6)) (g 13))) (fmul (fmul (g 4) (g 1)) (g 14))) (fmul (fmul (g 4) (g 2)) (g 13))) (fmul (fmul (g 12) (g 1)) (g 6))) (fmul (fmul (g 12) (g 2)) (g 5)))
  let i15 := (fsub (fadd (fadd (fsub (fsub (fmul (fmul (g 0) (g 5)) (g 10)) (fmul (fmul (g 0) (g 6)) (g 9))) (fmul (fmul (g 4) (g 1)) (g 10))) (fmul (fmul (g 4) (g 2)) (g 9))) (fmul (fmul (g 8) (g 1)) (g 6))) (fmul (fmul (g 8) (g 2)) (g 5)))
  let det := (fadd (fadd (fadd (fmul (g 0) i0) (fmul (g 1) i4)) (fmul (g 2) i8)) (fmul (g 3) i12))
  if fzero det then none
  else
    let d := fdiv (fbits (1.0 : Float32)) det
    some [(fmul i0 d), (fmul i1 d), (fmul i2 d), (fmul i3 d),
          (fmul i4 d), (fmul i5 d), (fmul i6 d), (fmul i7 d),
          (fmul i8 d), (fmul i9 d), (fmul i10 d), (fmul i11 d),
          (fmul i12 d), (fmul i13 d), (fmul i14 d), (fmul i15 d)]

def matvec4 (m v : List FB) : List FB :=
  (List.range 4).map (fun r =>
    fadd (fadd (fmul (fuget m (r * 4)) (fuget v 0))
               (fmul (fuget m (r * 4 + 1)) (fuget v 1)))
         (fadd (fmul (fuget m (r * 4 + 2)) (fuget v 2))
               (fmul (fuget m (r * 4 + 3)) (fuget v 3))))

/-- Suffix test (the C's `ends_with`). -/
def endsWithS (s suf : String) : Bool :=
  let sl := s.toList
  let fl := suf.toList
  fl.length <= sl.length && sl.drop (sl.length - fl.length) == fl

/-- `MonCurve` parameters from (gamma, offset): scale, offset, gamma,
breakpoint, slope (C `moncurve_params`, double intermediates). -/
def moncurve (gamma offset : FB) : List FB :=
  let G : Float := if (f32of gamma).toFloat < 1.000001 then 1.000001 else (f32of gamma).toFloat
  let O : Float := if (f32of offset).toFloat < 1e-6 then 1e-6 else (f32of offset).toFloat
  let a := (G - 1.0) / O
  let b := O * G / ((G - 1.0) * (1.0 + O))
  let f (x : Float) : FB := fbits (Float.toFloat32 x)
  let slope := a * (powf (Float.toFloat32 b) (Float.toFloat32 G)).toFloat
  [f (1.0 / (1.0 + O)), f (O / (1.0 + O)), f G, f (O / (G - 1.0)), f slope]

/-- Row-major to column-major (the C stores the transpose of the config
matrix). -/
def transpose4 (m : List FB) : List FB :=
  (List.range 16).map (fun i => fuget m ((i % 4) * 4 + i / 4))

/-- `toc_invert_op` on a Range op: the inverse `(scale, offset, min, max)`.
The inverse clamps to the forward *input* bounds, so the forward output
bounds are mapped back through the inverse; unbounded sides (the C
compares against +-3.0e38, not the 3.4e38 marker) stay unbounded. -/
def invertRange (scale offset lo hi : List FB) :
    List FB × List FB × List FB × List FB :=
  let ns := scale.map finv
  let no := (List.zip offset ns).map (fun (o, s) => fmul (fneg o) s)
  let thrHi : FB := fconst 3.0e38
  let thrLo : FB := fconst (-3.0e38)
  let aOf (i : Nat) : FB :=
    let l := fuget lo i
    if f32of l <= f32of thrLo then l
    else fadd (fmul l (fuget ns i)) (fuget no i)
  let bOf (i : Nat) : FB :=
    let h := fuget hi i
    if f32of h >= f32of thrHi then h
    else fadd (fmul h (fuget ns i)) (fuget no i)
  let newMin := (List.range 4).map (fun i =>
    if f32of (aOf i) < f32of (bOf i) then aOf i else bOf i)
  let newMax := (List.range 4).map (fun i =>
    if f32of (aOf i) < f32of (bOf i) then bOf i else aOf i)
  (ns, no, newMin, newMax)

end Tocio
