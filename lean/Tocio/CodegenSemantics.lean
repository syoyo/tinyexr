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

def effCh (ch : Nat) : Nat := Nat.min ch 3

theorem effCh_eq (ch : Nat) : (if ch < 3 then ch else 3) = effCh ch := by
  unfold effCh
  by_cases h : ch < 3
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · have h3 : 3 ≤ ch := by omega
    simp [h, Nat.min_eq_right h3]

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

end Tocio
