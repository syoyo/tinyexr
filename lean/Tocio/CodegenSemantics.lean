/-
  TinyEXR - semantics of the tocio AOT-C emitted statements.

  The emitted-source text is already byte-identical to the C emitter
  (`Tocio.CodegenC`, `make tocio-codegen-diff`). This module supplies the
  missing *semantic* link: a small statement AST whose evaluator is proved
  to be exactly the `Tocio.Ops` kernel for the matrix and range emits.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic
import Tocio.CodegenC
import Tocio.Ops
import Tocio.FixedFunc

namespace Tocio

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

-- Float32 replay of the `tc_lut1d` helper called by the emitted C.
def lut1dApplyF32 (data : List FB) (n ch : Nat) (dmin dmax : FB) (c : Nat) (x : FB) : FB :=
  let dm := Float32.ofBits dmin
  let dx := Float32.ofBits dmax
  let den := dx - dm
  let xv := Float32.ofBits x
  let u0 : Float32 := if den != 0 then (xv - dm) / den else 0
  let u : Float32 := if !(u0 > 0) then 0 else if u0 > 1 then 1 else u0
  let g : Float32 := u * Float32.ofNat (n - 1)
  let i : Nat := g.toUInt64.toNat
  let i0 : Nat := if i >= n - 1 then n - 2 else i
  let f : Float32 := g - Float32.ofNat i0
  let idx : Nat := if ch == 1 then i0 else i0 * 3 + c
  let idx1 : Nat := if ch == 1 then i0 + 1 else (i0 + 1) * 3 + c
  let a := Float32.ofBits (data.getD idx 0)
  let b := Float32.ofBits (data.getD idx1 0)
  Float32.toBits (a + (b - a) * f)

def mirrorSignF (v : Float32) : Float32 := if v < 0 then -1.0 else 1.0
def mirrorValF (v : Float32) : Float32 := if v < 0 then -v else v

theorem mirror_fst_proj (v : Float32) :
    (if v < 0 then ((-1.0 : Float32), -v) else (1.0, v)).1 =
      (if v < 0 then (-1.0 : Float32) else 1.0) := by
  by_cases h : v < 0 <;> simp [h]

theorem mirror_snd_proj (v : Float32) :
    (if v < 0 then ((-1.0 : Float32), -v) else (1.0, v)).2 =
      (if v < 0 then -v else v) := by
  by_cases h : v < 0 <;> simp [h]

theorem mirror_fst_if (v : Float32) :
    (if v < 0 then (-1.0 : Float32) else 1.0) = mirrorSignF v := by rfl

theorem mirror_snd_if (v : Float32) :
    (if v < 0 then -v else v) = mirrorValF v := by rfl

theorem mirror_fst (v : Float32) :
    (if v < 0 then ((-1.0 : Float32), -v) else (1.0, v)).1 = mirrorSignF v := by
  by_cases h : v < 0 <;> simp [h, mirrorSignF]

theorem mirror_snd (v : Float32) :
    (if v < 0 then ((-1.0 : Float32), -v) else (1.0, v)).2 = mirrorValF v := by
  by_cases h : v < 0 <;> simp [h, mirrorValF]

def ffComp (v : Float32 × Float32 × Float32) (c : Nat) : Float32 :=
  if c == 0 then v.1 else if c == 1 then v.2.1 else v.2.2

def ffStyleOfNat : Nat → FfStyle
  | 0 => .acesGlow10 | 1 => .acesGlow10Inv
  | 2 => .acesDarkToDim10 | 3 => .acesDarkToDim10Inv
  | 4 => .acesGamutComp13 | 5 => .acesGamutComp13Inv
  | 6 => .rec2100Surround | 7 => .rec2100SurroundInv
  | 8 => .acesGlow03 | 9 => .acesGlow03Inv
  | 10 => .acesRedMod03 | 11 => .acesRedMod03Inv
  | 12 => .acesRedMod10 | 13 => .acesRedMod10Inv
  | 14 => .rgbToHsv | 15 => .hsvToRgb
  | 16 => .xyzToXyY | 17 => .xyYToXyz
  | 18 => .xyzToUvY | 19 => .uvYToXyz
  | 20 => .xyzToLuv | 21 => .luvToXyz
  | 22 => .linToPq | 23 => .pqToLin
  | 24 => .linToHlg
  | _ => .hlgToLin

/-- Expression tree in the same evaluation order as the emitted C. -/
inductive CExpr where
  | lit (b : FB)
  | var (c : Nat)
  | mul (a b : CExpr)
  | add (a b : CExpr)
  | clampLoExpr (e : CExpr) (bound : FB) (enabled : Bool)
  | clampHiExpr (e : CExpr) (bound : FB) (enabled : Bool)
  | lut1dCall (n ch : Nat) (dmin dmax : FB) (data : List FB) (c : Nat)
  | neg (a : CExpr)
  | powE (a b : CExpr)
  | log2E (a : CExpr)
  | raiseE (a b : CExpr)
  | ifLtE (a b t e : CExpr)
  | ifGtE (a b t e : CExpr)
  | divE (a b : CExpr)
  | subE (a b : CExpr)
  | mirrorSign (a : CExpr)
  | mirrorVal (a : CExpr)
  | ffCall (style : Nat) (params : List FB) (c : Nat)
  | cdlCall (slope offset power : List FB) (sat : FB) (luma : List FB)
      (clamp inverse : Bool) (c : Nat)
  deriving Repr

def evalCExpr (px : List Float32) : CExpr → Float32
  | .lit b => Float32.ofBits b
  | .var c => px.getD c 0
  | .mul a b => evalCExpr px a * evalCExpr px b
  | .add a b => evalCExpr px a + evalCExpr px b
  | .clampLoExpr e b en =>
      let v := evalCExpr px e
      let lo := Float32.ofBits b
      if en && v < lo then lo else v
  | .neg a => -evalCExpr px a
  | .powE a b => powf (evalCExpr px a) (evalCExpr px b)
  | .log2E a => log2f (evalCExpr px a)
  | .raiseE a b => raisef (evalCExpr px a) (evalCExpr px b)
  | .ifLtE a b t e => if evalCExpr px a < evalCExpr px b then evalCExpr px t else evalCExpr px e
  | .ifGtE a b t e => if evalCExpr px a > evalCExpr px b then evalCExpr px t else evalCExpr px e
  | .divE a b => evalCExpr px a / evalCExpr px b
  | .subE a b => evalCExpr px a - evalCExpr px b
  | .mirrorSign a => mirrorSignF (evalCExpr px a)
  | .mirrorVal a => mirrorValF (evalCExpr px a)
  | .ffCall style params c =>
      let v := applyFixedFunc (ffStyleOfNat style) (params.map Float32.ofBits)
        (px.getD 0 0, px.getD 1 0, px.getD 2 0)
      ffComp v c
  | .cdlCall slope offset power sat luma clamp inverse c =>
      let v := applyCdl (slope.map Float32.ofBits) (offset.map Float32.ofBits)
        (power.map Float32.ofBits) (Float32.ofBits sat) (luma.map Float32.ofBits)
        clamp inverse
        (px.getD 0 0, px.getD 1 0, px.getD 2 0, px.getD 3 0)
      [v.1, v.2.1, v.2.2.1, v.2.2.2].getD c 0
  | .lut1dCall n ch dmin dmax data c =>
      Float32.ofBits (lut1dApplyF32 data n ch dmin dmax c (Float32.toBits (px.getD c 0)))
  | .clampHiExpr e b en =>
      let v := evalCExpr px e
      let hi := Float32.ofBits b
      if en && v > hi then hi else v

/-- One emitted statement (assignment or conditional clamp). -/
inductive CStmt where
  | set (c : Nat) (e : CExpr)
  | clampLo (c : Nat) (bound : FB)
  | clampHi (c : Nat) (bound : FB)
  | setAll (es : List CExpr)
  deriving Repr

def evalStmts : List CStmt → List Float32 → List Float32
  | [], px => px
  | .set c e :: ss, px => evalStmts ss (px.set c (evalCExpr px e))
  | .clampLo c b :: ss, px =>
      let v := px.getD c 0
      let lo := Float32.ofBits b
      evalStmts ss (if v < lo then px.set c lo else px)
  | .setAll es :: ss, px =>
      let e0 := evalCExpr px (es.getD 0 (.lit 0))
      let e1 := evalCExpr px (es.getD 1 (.lit 0))
      let e2 := evalCExpr px (es.getD 2 (.lit 0))
      let e3 := evalCExpr px (es.getD 3 (.lit 0))
      evalStmts ss ((((px.set 0 e0).set 1 e1).set 2 e2).set 3 e3)
  | .clampHi c b :: ss, px =>
      let v := px.getD c 0
      let hi := Float32.ofBits b
      evalStmts ss (if v > hi then px.set c hi else px)

theorem ofBits_fget_eq (l : List FB) (i : Nat) :
    Float32.ofBits (fget l i) = Float32.ofBits (l[i]?.getD 0) := rfl

theorem getD_eq_getOpt {α : Type} (l : List α) (i : Nat) (d : α) :
    l.getD i d = l[i]?.getD d := rfl

theorem evalCExpr_dite (px : List Float32) {c : Prop} [Decidable c] (a b : CExpr) :
    evalCExpr px (if c then a else b) = if c then evalCExpr px a else evalCExpr px b := by
  by_cases h : c <;> simp [h]

theorem evalCExpr_ite (px : List Float32) (c : Bool) (a b : CExpr) :
    evalCExpr px (if c then a else b) = if c then evalCExpr px a else evalCExpr px b := by
  by_cases h : c <;> simp [h]

theorem mul_ite_f32 (a : Float32) {c : Prop} [Decidable c] (b d : Float32) :
    a * (if c then b else d) = if c then a * b else a * d := by
  by_cases h : c <;> simp [h]

def pxList (px : Pixel) : List Float32 := [px.1, px.2.1, px.2.2.1, px.2.2.2]

def listPx (v : List Float32) : Pixel :=
  (v.getD 0 0, v.getD 1 0, v.getD 2 0, v.getD 3 0)

def matrixExprAux (m off : List FB) (r : Nat) : CExpr :=
  let t0 : CExpr := .mul (.lit (fget m r)) (.var 0)
  let t1 : CExpr := .mul (.lit (fget m (4 + r))) (.var 1)
  let t2 : CExpr := .mul (.lit (fget m (8 + r))) (.var 2)
  let t3 : CExpr := .mul (.lit (fget m (12 + r))) (.var 3)
  CExpr.add (CExpr.add (CExpr.add (CExpr.add t0 t1) t2) t3) (.lit (fget off r))

def compileMatrix (m off : List FB) : List CStmt :=
  [.setAll ((List.range 4).map (fun r => matrixExprAux m off r))]

theorem eval_compile_matrix (m off : List FB) (px : Pixel) :
    listPx (evalStmts (compileMatrix m off) (pxList px)) = applyMatrix (m.map Float32.ofBits) (off.map Float32.ofBits) px := by
  have hzero : (0 : Float32) = 0.0 := by rfl
  have hmap0 : ∀ (o : Option FB),
      (Option.map Float32.ofBits o).getD (0.0 : Float32) = Float32.ofBits (o.getD 0) := by
    intro o; cases o <;> rfl
  change listPx (evalStmts [.setAll [matrixExprAux m off 0, matrixExprAux m off 1,
      matrixExprAux m off 2, matrixExprAux m off 3]] (pxList px)) = _
  ext <;> simp [matrixExprAux, evalStmts, evalCExpr, listPx, pxList, applyMatrix, fget, hzero, ← hmap0]

def rangeExpr (scale offset lo hi : List FB) (clampLo clampHi : Bool) (c : Nat) : CExpr :=
  let e : CExpr := .add (.mul (.var c) (.lit (fget scale c))) (.lit (fget offset c))
  .clampHiExpr (.clampLoExpr e (fget lo c) clampLo) (fget hi c) clampHi

def compileRange (scale offset lo hi : List FB) (clampLo clampHi : Bool) : List CStmt :=
  [.setAll ((List.range 4).map (fun c => rangeExpr scale offset lo hi clampLo clampHi c))]

theorem eval_compile_range (scale offset lo hi : List FB) (clampLo clampHi : Bool)
    (px : Pixel) :
    listPx (evalStmts (compileRange scale offset lo hi clampLo clampHi) (pxList px)) =
      applyRange (scale.map Float32.ofBits) (offset.map Float32.ofBits)
        (lo.map Float32.ofBits) (hi.map Float32.ofBits) clampLo clampHi px := by
  have hzero : (0 : Float32) = 0.0 := by rfl
  have hmap0 : ∀ (o : Option FB),
      (Option.map Float32.ofBits o).getD (0.0 : Float32) = Float32.ofBits (o.getD 0) := by
    intro o; cases o <;> rfl
  change listPx (evalStmts [.setAll [rangeExpr scale offset lo hi clampLo clampHi 0,
      rangeExpr scale offset lo hi clampLo clampHi 1,
      rangeExpr scale offset lo hi clampLo clampHi 2,
      rangeExpr scale offset lo hi clampLo clampHi 3]] (pxList px)) = _
  ext <;> simp [rangeExpr, evalStmts, evalCExpr, listPx, pxList, applyRange,
    fget, hzero, ← hmap0]

def compileLut1d (n ch : Nat) (dmin dmax : FB) (data : List FB) : List CStmt :=
  [.setAll ([.lut1dCall n ch dmin dmax data 0,
             .lut1dCall n ch dmin dmax data 1,
             .lut1dCall n ch dmin dmax data 2,
             .var 3])]

theorem eval_compile_lut1d (n ch : Nat) (dmin dmax : FB) (data : List FB) (px : Pixel) :
    let out := evalStmts (compileLut1d n ch dmin dmax data) (pxList px)
    out.getD 0 0 = Float32.ofBits (lut1dApplyF32 data n ch dmin dmax 0 (Float32.toBits px.1)) &&
    out.getD 1 0 = Float32.ofBits (lut1dApplyF32 data n ch dmin dmax 1 (Float32.toBits px.2.1)) &&
    out.getD 2 0 = Float32.ofBits (lut1dApplyF32 data n ch dmin dmax 2 (Float32.toBits px.2.2.1)) := by
  unfold compileLut1d
  simp [evalStmts, evalCExpr, pxList]

def compileExponent (e : List FB) (mirror : Bool) (ch : Nat) : List CStmt :=
  let one (i : Nat) : CExpr :=
    if i >= ch then .var i else
    if mirror then
      let sgn : CExpr := .ifLtE (.var i) (.lit 0) (.lit (Float32.toBits (-1.0))) (.lit (Float32.toBits 1.0))
      let v : CExpr := .ifLtE (.var i) (.lit 0) (.neg (.var i)) (.var i)
      .mul sgn (.powE v (.lit (e.getD i 0)))
    else
      let v : CExpr := .ifGtE (.var i) (.lit 0) (.var i) (.lit 0)
      .powE v (.lit (e.getD i 0))
  [.setAll ([one 0, one 1, one 2, one 3])]

theorem eval_compile_exponent (e : List FB) (mirror : Bool) (ch : Nat) (px : Pixel) :
    listPx (evalStmts (compileExponent e mirror ch) (pxList px)) =
      applyExponent (e.map Float32.ofBits) mirror ch px := by
  have hmap0 : ∀ (o : Option FB),
      (Option.map Float32.ofBits o).getD (0.0 : Float32) = Float32.ofBits (o.getD 0) := by
    intro o; cases o <;> rfl
  have hb0 : Float32.ofBits (0 : FB) = 0.0 := rfl
  have hbm1 : Float32.ofBits (Float32.toBits (-1.0 : Float32)) = -1.0 := by native_decide
  have hb1 : Float32.ofBits (Float32.toBits (1.0 : Float32)) = 1.0 := by native_decide
  by_cases hm : mirror
  · by_cases h0 : ch ≤ 0 <;> by_cases h1 : ch ≤ 1 <;> by_cases h2 : ch ≤ 2 <;>
      by_cases h3 : ch ≤ 3 <;>
      ext <;> simp [hm, h0, h1, h2, h3, compileExponent, evalStmts, evalCExpr,
        listPx, pxList, applyExponent, hmap0, hb0, hbm1, hb1]
  · by_cases h0 : ch ≤ 0 <;> by_cases h1 : ch ≤ 1 <;> by_cases h2 : ch ≤ 2 <;>
      by_cases h3 : ch ≤ 3 <;>
      ext <;> simp [hm, h0, h1, h2, h3, compileExponent, evalStmts, evalCExpr,
        listPx, pxList, applyExponent, hmap0, hb0, hbm1, hb1]


def effCh (ch : Nat) : Nat := Nat.min ch 3

theorem effCh_eq (ch : Nat) : (if ch < 3 then ch else 3) = effCh ch := by
  unfold effCh
  by_cases h : ch < 3
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · have h3 : 3 ≤ ch := by omega
    simp [h, Nat.min_eq_right h3]

/-- The single-channel exp-linear step, factored out of `applyExpLinear`. -/
def expLinearStep (scale offset gamma brk slope : List Float32)
    (inverse mirror : Bool) (n i : Nat) (v : Float32) : Float32 :=
  if i >= n then v
  else
    let s : Float32 := if mirror then mirrorSignF v else 1.0
    let x : Float32 := if mirror then mirrorValF v else v
    if !inverse then
      s * (if x > brk.getD i 0.0 then
        powf (x * scale.getD i 0.0 + offset.getD i 0.0) (gamma.getD i 0.0)
      else x * slope.getD i 0.0)
    else
      let ybrk := brk.getD i 0.0 * slope.getD i 0.0
      s * (if x > ybrk then
        (powf x (1.0 / gamma.getD i 0.0) - offset.getD i 0.0) / scale.getD i 0.0
      else x / slope.getD i 0.0)

theorem applyExpLinear_eq_steps (scale offset gamma brk slope : List Float32)
    (inverse mirror : Bool) (ch : Nat) (px : Pixel) :
    applyExpLinear scale offset gamma brk slope inverse mirror ch px =
      (expLinearStep scale offset gamma brk slope inverse mirror (effCh ch) 0 px.1,
       expLinearStep scale offset gamma brk slope inverse mirror (effCh ch) 1 px.2.1,
       expLinearStep scale offset gamma brk slope inverse mirror (effCh ch) 2 px.2.2.1,
       expLinearStep scale offset gamma brk slope inverse mirror (effCh ch) 3 px.2.2.2) := by
  have hz : (0.0 : Float32) = 0 := rfl
  by_cases hm : mirror <;>
    by_cases hp0 : px.1 < 0 <;> by_cases hp1 : px.2.1 < 0 <;>
    by_cases hp2 : px.2.2.1 < 0 <;> by_cases hp3 : px.2.2.2 < 0 <;>
    simp [applyExpLinear, expLinearStep, effCh_eq, hz, hm, hp0, hp1, hp2, hp3,
      mirrorSignF, mirrorValF]

def compileExpLinearOne (scale offset gamma brk slope : List FB)
    (inverse mirror : Bool) (ch i : Nat) : CExpr :=
  if i >= effCh ch then .var i else
    let sgn : CExpr := if mirror then .mirrorSign (.var i) else .lit (Float32.toBits (1.0 : Float32))
    let xv : CExpr := if mirror then .mirrorVal (.var i) else .var i
    if !inverse then
      .mul sgn (.ifLtE (.lit (fget brk i)) xv
        (.powE (.add (.mul xv (.lit (fget scale i))) (.lit (fget offset i)))
               (.lit (fget gamma i)))
        (.mul xv (.lit (fget slope i))))
    else
      let ybrk : CExpr := .mul (.lit (fget brk i)) (.lit (fget slope i))
      .mul sgn (.ifLtE ybrk xv
        (.divE (.subE (.powE xv (.divE (.lit (Float32.toBits (1.0 : Float32))) (.lit (fget gamma i))))
                      (.lit (fget offset i))) (.lit (fget scale i)))
        (.divE xv (.lit (fget slope i))))

def compileExpLinear (scale offset gamma brk slope : List FB)
    (inverse mirror : Bool) (ch : Nat) : List CStmt :=
  [.setAll ((List.range 4).map (fun i => compileExpLinearOne scale offset gamma brk slope inverse mirror ch i))]

theorem eval_compile_explin_one (scale offset gamma brk slope : List FB)
    (inverse mirror : Bool) (ch i : Nat) (px : Pixel) :
    evalCExpr (pxList px) (compileExpLinearOne scale offset gamma brk slope inverse mirror ch i) =
      expLinearStep (scale.map Float32.ofBits) (offset.map Float32.ofBits)
        (gamma.map Float32.ofBits) (brk.map Float32.ofBits) (slope.map Float32.ofBits)
        inverse mirror (effCh ch) i ((pxList px).getD i 0) := by
  have hmap0 : ∀ (o : Option FB),
      (Option.map Float32.ofBits o).getD (0.0 : Float32) = Float32.ofBits (o.getD 0) := by
    intro o; cases o <;> rfl
  have hb1 : Float32.ofBits (Float32.toBits (1.0 : Float32)) = 1.0 := by decide
  by_cases hi : i >= effCh ch
  · simp [compileExpLinearOne, expLinearStep, evalCExpr, evalCExpr_ite, evalCExpr_dite,
      pxList, fget, List.getD, hmap0, hb1, hi, mul_ite_f32]
  · by_cases hinv : inverse <;> by_cases hm : mirror <;>
      (simp [compileExpLinearOne, expLinearStep, evalCExpr, evalCExpr_ite,
        evalCExpr_dite, pxList, fget, List.getD, hmap0, hb1, hi, hinv, hm];
       try (split <;> simp_all))

theorem eval_compile_explin (scale offset gamma brk slope : List FB)
    (inverse mirror : Bool) (ch : Nat) (px : Pixel) :
    listPx (evalStmts (compileExpLinear scale offset gamma brk slope inverse mirror ch) (pxList px)) =
      applyExpLinear (scale.map Float32.ofBits) (offset.map Float32.ofBits)
        (gamma.map Float32.ofBits) (brk.map Float32.ofBits) (slope.map Float32.ofBits)
        inverse mirror ch px := by
  rw [applyExpLinear_eq_steps]
  simp [compileExpLinear, evalStmts, listPx, pxList]
  constructor
  · simpa [pxList] using eval_compile_explin_one scale offset gamma brk slope inverse mirror ch 0 px
  constructor
  · simpa [pxList] using eval_compile_explin_one scale offset gamma brk slope inverse mirror ch 1 px
  constructor
  · simpa [pxList] using eval_compile_explin_one scale offset gamma brk slope inverse mirror ch 2 px
  · simpa [pxList] using eval_compile_explin_one scale offset gamma brk slope inverse mirror ch 3 px


/-- C log kernel step; the emitted C omits the interpreter's tiny-floor
    clamp, so the equivalence theorem assumes a positive linear argument. -/
def logStep (base : Float32) (logSlope logOffset linSlope linOffset : List Float32)
    (inverse : Bool) (i : Nat) (v : Float32) : Float32 :=
  if i >= 3 then v
  else if !inverse then
    let a := linSlope.getD i 0.0 * v + linOffset.getD i 0.0
    logSlope.getD i 0.0 * (log2f a / log2f base) + logOffset.getD i 0.0
  else
    let e := (v - logOffset.getD i 0.0) / logSlope.getD i 0.0
    let p := raisef base e
    (p - linOffset.getD i 0.0) / linSlope.getD i 0.0

theorem applyLog_eq_logStep (base : Float32)
    (logSlope logOffset linSlope linOffset : List Float32)
    (inverse : Bool) (ch : Nat) (px : Pixel)
    (hch : 3 ≤ ch)
    (ha0 : 0 < linSlope[0]?.getD 0 * px.1 + linOffset[0]?.getD 0)
    (ha1 : 0 < linSlope[1]?.getD 0 * px.2.1 + linOffset[1]?.getD 0)
    (ha2 : 0 < linSlope[2]?.getD 0 * px.2.2.1 + linOffset[2]?.getD 0) :
    applyLog base logSlope logOffset linSlope linOffset inverse ch px =
      (logStep base logSlope logOffset linSlope linOffset inverse 0 px.1,
       logStep base logSlope logOffset linSlope linOffset inverse 1 px.2.1,
       logStep base logSlope logOffset linSlope linOffset inverse 2 px.2.2.1,
       px.2.2.2) := by
  have hz : (0.0 : Float32) = 0 := rfl
  have he : effCh ch = 3 := by simp [effCh, Nat.min_eq_right hch]
  have ha0n : 0 < linSlope[0]?.getD 0 * px.1 + linOffset[0]?.getD 0 := by simpa [hz] using ha0
  have ha1n : 0 < linSlope[1]?.getD 0 * px.2.1 + linOffset[1]?.getD 0 := by simpa [hz] using ha1
  have ha2n : 0 < linSlope[2]?.getD 0 * px.2.2.1 + linOffset[2]?.getD 0 := by simpa [hz] using ha2
  by_cases hinv : inverse <;>
    simp [applyLog, logStep, effCh_eq, he, hch, hz, hinv, ha0, ha1, ha2, ha0n, ha1n, ha2n, hz, pxList]

def compileLogOne (base : FB) (logSlope logOffset linSlope linOffset : List FB)
    (inverse : Bool) (i : Nat) : CExpr :=
  if i >= effCh 3 then .var i else
  if !inverse then
    .add (.mul (.lit (fget logSlope i))
      (.divE (.log2E (.add (.mul (.lit (fget linSlope i)) (.var i)) (.lit (fget linOffset i))))
             (.log2E (.lit base))))
      (.lit (fget logOffset i))
  else
    .divE (.subE (.raiseE (.lit base)
      (.divE (.subE (.var i) (.lit (fget logOffset i))) (.lit (fget logSlope i))))
      (.lit (fget linOffset i))) (.lit (fget linSlope i))

def compileLog (base : FB) (logSlope logOffset linSlope linOffset : List FB)
    (inverse : Bool) : List CStmt :=
  [.setAll ((List.range 4).map (fun i => compileLogOne base logSlope logOffset linSlope linOffset inverse i))]

theorem eval_compile_log_one (base : FB) (logSlope logOffset linSlope linOffset : List FB)
    (inverse : Bool) (i : Nat) (px : Pixel) :
    evalCExpr (pxList px) (compileLogOne base logSlope logOffset linSlope linOffset inverse i) =
      logStep (Float32.ofBits base) (logSlope.map Float32.ofBits) (logOffset.map Float32.ofBits)
        (linSlope.map Float32.ofBits) (linOffset.map Float32.ofBits) inverse i
        ((pxList px).getD i 0) := by
  have hmap0 : ∀ (o : Option FB),
      (Option.map Float32.ofBits o).getD (0.0 : Float32) = Float32.ofBits (o.getD 0) := by
    intro o; cases o <;> rfl
  by_cases hi : i >= effCh 3
  · have hi3 : 3 ≤ i := by simpa [effCh] using hi
    simp [compileLogOne, logStep, hi, hi3, evalCExpr, evalCExpr_dite, hmap0, effCh, fget]
  · have hi3 : ¬ 3 ≤ i := by simpa [effCh] using hi
    by_cases hinv : inverse
    · simp [compileLogOne, hi, hi3, hinv, logStep, evalCExpr, evalCExpr_dite, hmap0, effCh, fget]
    · simp [compileLogOne, hi, hi3, hinv, logStep, evalCExpr, evalCExpr_dite, hmap0, effCh, fget]

theorem eval_compile_log (base : FB) (logSlope logOffset linSlope linOffset : List FB)
    (inverse : Bool) (ch : Nat) (px : Pixel) (hch : 3 ≤ ch)
    (hpos : ∀ i, i < 3 → 0 <
      Float32.ofBits (fget linSlope i) * (pxList px).getD i 0 +
        Float32.ofBits (fget linOffset i)) :
    listPx (evalStmts (compileLog base logSlope logOffset linSlope linOffset inverse) (pxList px)) =
      applyLog (Float32.ofBits base) (logSlope.map Float32.ofBits)
        (logOffset.map Float32.ofBits) (linSlope.map Float32.ofBits)
        (linOffset.map Float32.ofBits) inverse ch px := by
  have hbmap : ∀ (o : Option FB), Float32.ofBits (o.getD 0) = (o.map Float32.ofBits).getD 0 := by
    intro o; cases o <;> rfl
  rw [applyLog_eq_logStep (Float32.ofBits base) (logSlope.map Float32.ofBits)
      (logOffset.map Float32.ofBits) (linSlope.map Float32.ofBits)
      (linOffset.map Float32.ofBits) inverse ch px hch]
  · simp [compileLog, evalStmts, listPx, pxList]
    constructor
    · simpa [pxList] using eval_compile_log_one base logSlope logOffset linSlope linOffset inverse 0 px
    constructor
    · simpa [pxList] using eval_compile_log_one base logSlope logOffset linSlope linOffset inverse 1 px
    constructor
    · simpa [pxList] using eval_compile_log_one base logSlope logOffset linSlope linOffset inverse 2 px
    · simpa [pxList, logStep, effCh] using eval_compile_log_one base logSlope logOffset linSlope linOffset inverse 3 px
  · simpa [pxList, fget, hbmap, List.getD] using hpos 0 (by omega)
  · simpa [pxList, fget, hbmap, List.getD] using hpos 1 (by omega)
  · simpa [pxList, fget, hbmap, List.getD] using hpos 2 (by omega)


/-- CDL luma weights with the C's all-zero fallback. -/
def cdlLumaFB (luma : List FB) : Float32 × Float32 × Float32 :=
  let lr := Float32.ofBits (fget luma 0)
  let lg := Float32.ofBits (fget luma 1)
  let lb := Float32.ofBits (fget luma 2)
  if lr == 0.0 && lg == 0.0 && lb == 0.0 then (0.2126, 0.7152, 0.0722)
  else (lr, lg, lb)

def clampExpr (e : CExpr) (clamp : Bool) : CExpr :=
  .clampHiExpr (.clampLoExpr e (Float32.toBits (0.0 : Float32)) clamp)
    (Float32.toBits (1.0 : Float32)) clamp

def cdlExpr (slope offset power : List FB) (saturation : FB)
    (luma : List FB) (clamp inverse : Bool) : List CExpr :=
  let (lr, lg, lb) := cdlLumaFB luma
  let v (i : Nat) : CExpr :=
    let x : CExpr := .add (.mul (.var i) (.lit (fget slope i))) (.lit (fget offset i))
    clampExpr (.ifLtE (.lit (Float32.toBits (0.0 : Float32))) x
      (.powE x (.lit (fget power i))) x) clamp
  let l : CExpr := .add (.add (.mul (.lit (Float32.toBits lr)) (v 0))
    (.mul (.lit (Float32.toBits lg)) (v 1)))
    (.mul (.lit (Float32.toBits lb)) (v 2))
  let outF (i : Nat) : CExpr :=
    clampExpr (.add l (.mul (.lit saturation) (.subE (v i) l))) clamp
  let linv : CExpr :=
    .add (.add (.mul (.lit (Float32.toBits lr)) (.var 0))
      (.mul (.lit (Float32.toBits lg)) (.var 1)))
      (.mul (.lit (Float32.toBits lb)) (.var 2))
  let undo (i : Nat) : CExpr :=
    let divsat : CExpr := .divE (.subE (.var i) linv) (.lit saturation)
    let satnz : CExpr := .ifLtE (.lit (Float32.toBits (0.0 : Float32)))
      (.lit saturation) divsat
      (.ifGtE (.lit (Float32.toBits (0.0 : Float32))) (.lit saturation)
        divsat (.lit (Float32.toBits (0.0 : Float32))))
    let x0 : CExpr := .add linv satnz
    let x1 := clampExpr x0 clamp
    let x2 := .ifLtE (.lit (Float32.toBits (0.0 : Float32))) x1
      (.powE x1 (.divE (.lit (Float32.toBits (1.0 : Float32))) (.lit (fget power i)))) x1
    let snz : CExpr := .ifLtE (.lit (Float32.toBits (0.0 : Float32)))
      (.lit (fget slope i)) (.lit (fget slope i))
      (.ifGtE (.lit (Float32.toBits (0.0 : Float32))) (.lit (fget slope i))
        (.lit (fget slope i)) (.lit (Float32.toBits (1.0 : Float32))))
    .divE (.subE x2 (.lit (fget offset i))) snz
  if !inverse then [outF 0, outF 1, outF 2, .var 3]
  else [undo 0, undo 1, undo 2, .var 3]

/-- The AOT-C emitter lowers a CDL op to an inline block; this AST records
    it as one helper call per channel, whose semantics is `applyCdl`. The
    emitter's byte-identical text is pinned by `make tocio-codegen-diff`. -/
def compileCdl (slope offset power : List FB) (saturation : FB)
    (luma : List FB) (clamp inverse : Bool) : List CStmt :=
  [.setAll ((List.range 4).map (fun c =>
    if c < 3 then .cdlCall slope offset power saturation luma clamp inverse c
    else .var 3))]

theorem applyCdl_alpha (slope offset power : List Float32) (sat : Float32)
    (luma : List Float32) (clamp inverse : Bool) (px : Pixel) :
    (applyCdl slope offset power sat luma clamp inverse px).2.2.2 = px.2.2.2 := by
  unfold applyCdl
  split <;> rfl

theorem eval_compile_cdl (slope offset power : List FB) (saturation : FB)
    (luma : List FB) (clamp inverse : Bool) (px : Pixel) :
    listPx (evalStmts (compileCdl slope offset power saturation luma clamp inverse) (pxList px)) =
      applyCdl (slope.map Float32.ofBits) (offset.map Float32.ofBits)
        (power.map Float32.ofBits) (Float32.ofBits saturation) (luma.map Float32.ofBits)
        clamp inverse px := by
  simp [compileCdl, evalStmts, evalCExpr, listPx, pxList]
  generalize hv : applyCdl (slope.map Float32.ofBits) (offset.map Float32.ofBits)
      (power.map Float32.ofBits) (Float32.ofBits saturation) (luma.map Float32.ofBits)
      clamp inverse px = v
  cases v with
  | mk a bc =>
      cases bc with
      | mk b cd =>
          cases cd with
          | mk c d =>
              have hd : d = px.2.2.2 := by
                have hh := congrArg (fun p : Pixel => p.2.2.2) hv
                have halpha : (applyCdl (slope.map Float32.ofBits) (offset.map Float32.ofBits)
                    (power.map Float32.ofBits) (Float32.ofBits saturation) (luma.map Float32.ofBits)
                    clamp inverse px).2.2.2 = px.2.2.2 := by exact applyCdl_alpha _ _ _ _ _ _ _ _
                have hhd : d = (applyCdl (slope.map Float32.ofBits) (offset.map Float32.ofBits)
                    (power.map Float32.ofBits) (Float32.ofBits saturation) (luma.map Float32.ofBits)
                    clamp inverse px).2.2.2 := by simpa using hh.symm
                exact hhd.trans halpha
              subst d
              rfl



/-- The AOT-C emitter lowers a FixedFunction op to a helper call; this AST
    records that call, whose body is the C helper pinned byte-for-byte by
    `make tocio-codegen-diff`. -/
def compileFixedFunc (style : Nat) (params : List FB) : List CStmt :=
  [.setAll [.ffCall style params 0, .ffCall style params 1,
    .ffCall style params 2, .var 3]]

theorem eval_compile_fixedfunc (style : Nat) (params : List FB) (px : Pixel) :
    listPx (evalStmts (compileFixedFunc style params) (pxList px)) =
      let v := applyFixedFunc (ffStyleOfNat style) (params.map Float32.ofBits)
        (px.1, px.2.1, px.2.2.1)
      (v.1, v.2.1, v.2.2, px.2.2.2) := by
  simp [compileFixedFunc, evalStmts, evalCExpr, listPx, pxList, ffComp]



def logCamStep (base : Float32) (ls lo ns no brk lslope loff : List Float32)
    (inverse : Bool) (i : Nat) (v : Float32) : Float32 :=
  if i >= 3 then v
  else if !inverse then
    if brk.getD i 0.0 < v then
      let a := ns.getD i 0.0 * v + no.getD i 0.0
      ls.getD i 0.0 * (log2f a / log2f base) + lo.getD i 0.0
    else lslope.getD i 0.0 * v + loff.getD i 0.0
  else
    let ybrk := lslope.getD i 0.0 * brk.getD i 0.0 + loff.getD i 0.0
    if ybrk < v then
      let p := raisef base ((v - lo.getD i 0.0) / ls.getD i 0.0)
      (p - no.getD i 0.0) / ns.getD i 0.0
    else (v - loff.getD i 0.0) / lslope.getD i 0.0

def compileLogCamOne (base : FB) (ls lo ns no brk lslope loff : List FB)
    (inverse : Bool) (i : Nat) : CExpr :=
  if i >= effCh 3 then .var i else
  if !inverse then
    .ifGtE (.var i) (.lit (fget brk i))
      (.add (.mul (.lit (fget ls i))
        (.divE (.log2E (.add (.mul (.lit (fget ns i)) (.var i)) (.lit (fget no i))))
               (.log2E (.lit base)))) (.lit (fget lo i)))
      (.add (.mul (.lit (fget lslope i)) (.var i)) (.lit (fget loff i)))
  else
    let ybrk := .add (.mul (.lit (fget lslope i)) (.lit (fget brk i))) (.lit (fget loff i))
    .ifGtE (.var i) ybrk
      (.divE (.subE (.raiseE (.lit base)
        (.divE (.subE (.var i) (.lit (fget lo i))) (.lit (fget ls i)))) (.lit (fget no i)))
        (.lit (fget ns i)))
      (.divE (.subE (.var i) (.lit (fget loff i))) (.lit (fget lslope i)))

def compileLogCam (base : FB) (ls lo ns no brk lslope loff : List FB)
    (inverse : Bool) : List CStmt :=
  [.setAll ((List.range 4).map (fun i => compileLogCamOne base ls lo ns no brk lslope loff inverse i))]

end Tocio
