/-
  TinyEXR - exact IEEE-754 semantics for the tocio op kernels.

  `Tocio/FloatBridge.lean` records that Lean's `Float32` primitives are
  compiler externs while `Float32.Model` is an exact binary32 semantics.
  This module states the kernels over both and connects them:

  * `KernelOps` bundles the primitives; `modelOps` is the exact
    `Float32.Model` instantiation and `f32Ops` the compiled `Float32`
    one.
  * `rangeK` is the per-channel range kernel `clamp(in*scale+offset)`
    written once over a bundle.
  * `rangeK_clamp` / `rangeK_noclamp` prove the *transfer*: under the
    `FloatBridge` hypothesis the compiled kernel converts exactly to the
    model kernel (`toModel (rangeK f32Ops …) = rangeK modelOps …`), so
    every model fact about the kernel applies to the compiled code.
  * `clampK_lo` / `clampK_hi` / `clampK_id` / `clampK_idem` prove the
    clamp contract (saturation at both bounds, in-bounds identity,
    idempotence) from the comparison results alone — no floating-point
    arithmetic is unfolded.
  * `rangeK_identity_exact` / `rangeK_saturate_exact` /
    `rangeK_roundtrip_exact` are `decide`-checked theorems over the
    *model*: kernel-checked facts about exact IEEE-754 semantics (no
    `native_decide`, no sampled compiler float), the model-level
    counterparts of the `native_decide` grid laws.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.FloatBridge

namespace Tocio

open Float32.Model

/-- The primitive operations a kernel uses, abstracted so the same
kernel text can be interpreted over `Float32` and over the exact
`Float32.Model` semantics. -/
structure KernelOps (α : Type) where
  add : α → α → α
  mul : α → α → α
  lt : α → α → Bool

/-- Exact IEEE-754 (binary32) instantiation: the source of truth. -/
def modelOps : KernelOps Float32.Model where
  add := Float32.Model.add
  mul := Float32.Model.mul
  lt := fun a b => Float32.Model.lt a b

/-- The compiled `Float32` instantiation, related to `modelOps` by the
`FloatBridge` hypothesis. -/
def f32Ops : KernelOps Float32 where
  add := (· + ·)
  mul := (· * ·)
  lt := fun a b => decide (a < b)

/-- Per-channel range kernel: `clamp(in*scale+offset, lo, hi)`. -/
def rangeK {α : Type} (o : KernelOps α) (x scale offset lo hi : α)
    (clamp : Bool) : α :=
  let y := o.add (o.mul x scale) offset
  if clamp then
    (if o.lt y lo then lo else if o.lt hi y then hi else y)
  else y

/-- Clamp over a primitive bundle. -/
def clampK {α : Type} (o : KernelOps α) (x lo hi : α) : α :=
  if o.lt x lo then lo else if o.lt hi x then hi else x

/-! ## The clamp contract (comparison logic only) -/

theorem clampK_lo {α : Type} (o : KernelOps α) {x lo hi : α}
    (h : o.lt x lo = true) : clampK o x lo hi = lo := by
  simp [clampK, h]

theorem clampK_hi {α : Type} (o : KernelOps α) {x lo hi : α}
    (h1 : o.lt x lo = false) (h2 : o.lt hi x = true) :
    clampK o x lo hi = hi := by
  simp [clampK, h1, h2]

theorem clampK_id {α : Type} (o : KernelOps α) {x lo hi : α}
    (h1 : o.lt x lo = false) (h2 : o.lt hi x = false) :
    clampK o x lo hi = x := by
  simp [clampK, h1, h2]

/-- Idempotence given an ordered pair of bounds. -/
theorem clampK_idem {α : Type} (o : KernelOps α) {x lo hi : α}
    (hii : o.lt lo lo = false) (hlh : o.lt hi lo = false) :
    clampK o (clampK o x lo hi) lo hi = clampK o x lo hi := by
  unfold clampK
  by_cases hx : o.lt x lo
  · simp [hx, hii, hlh]
  · by_cases hx2 : o.lt hi x
    · simp [hx, hx2, hlh]
    · simp [hx, hx2]

/-! ## Transfer to the exact model semantics -/

/-- Comparison agreement: under the bridge, `<` is the model order. -/
theorem lt_agree (h : FloatBridge) (a b : Float32) :
    (a < b) = (Float32.Model.lt a.toModel b.toModel = true) :=
  FloatBridge.lt_eq h a b

/-- Arithmetic core: the compiled `x*s+o` is the model expression. -/
theorem rangeK_arith (h : FloatBridge) (x s o : Float32) :
    (x * s + o).toModel = (x.toModel.mul s.toModel).add o.toModel := by
  rw [FloatBridge.add_eq h, FloatBridge.mul_eq h]
  rfl

/-- Transfer without clamping (pure arithmetic). -/
theorem rangeK_noclamp (h : FloatBridge) (x s o : Float32) :
    (rangeK f32Ops x s o (Float32.ofBits 0) (Float32.ofBits 0) false).toModel
      = rangeK modelOps x.toModel s.toModel o.toModel
          (Float32.Model.ofBits 0) (Float32.Model.ofBits 0) false := by
  show (x * s + o).toModel = (x.toModel.mul s.toModel).add o.toModel
  exact rangeK_arith h x s o

/-- `toModel` distributes over a conditional. -/
theorem toModel_ite (c : Prop) [inst : Decidable c] (a b : Float32) :
    (ite c a b).toModel = ite c a.toModel b.toModel := by
  by_cases h : c <;> simp [h]

/-- Full transfer with clamping: under the bridge the compiled range
kernel converts to the exact model kernel. -/
theorem rangeK_clamp (h : FloatBridge) (x s o lo hi : Float32) :
    (rangeK f32Ops x s o lo hi true).toModel
      = rangeK modelOps x.toModel s.toModel o.toModel lo.toModel hi.toModel true := by
  have hy := rangeK_arith h x s o
  have hi1 : ((x * s + o) < lo) =
      (((x.toModel.mul s.toModel).add o.toModel).lt lo.toModel = true) :=
    lt_agree h (x * s + o) lo
  have hi2 : (hi < (x * s + o)) =
      (hi.toModel.lt ((x.toModel.mul s.toModel).add o.toModel) = true) :=
    lt_agree h hi (x * s + o)
  simp only [rangeK, ite_true, f32Ops, modelOps]
  by_cases h1 : (x * s + o < lo)
  · have hm1 : ((x.toModel.mul s.toModel).add o.toModel).lt lo.toModel = true := hi1.mp h1
    simp only [h1, decide_true, ite_true, hm1]
  · have hm1 : ((x.toModel.mul s.toModel).add o.toModel).lt lo.toModel = false := by
      have hne : ¬ (((x.toModel.mul s.toModel).add o.toModel).lt lo.toModel = true) := by
        intro hc; exact h1 (hi1.mpr hc)
      rw [Bool.eq_false_iff]; exact hne
    by_cases h2 : (hi < x * s + o)
    · have hm2 : hi.toModel.lt ((x.toModel.mul s.toModel).add o.toModel) = true := hi2.mp h2
      simp only [h1, h2, decide_true, decide_false, ite_true, hm1, hm2]
      rfl
    · have hm2 : hi.toModel.lt ((x.toModel.mul s.toModel).add o.toModel) = false := by
        have hne : ¬ (hi.toModel.lt ((x.toModel.mul s.toModel).add o.toModel) = true) := by
          intro hc; exact h2 (hi2.mpr hc)
        rw [Bool.eq_false_iff]; exact hne
      simp only [h1, h2, decide_false, hm1, hm2]
      exact hy

/-! ## Kernel-checked exact-semantics facts (`decide`, no native code) -/

/-- Exact binary32 constants used by the vectors. -/
def bOne : Float32.Model := Float32.Model.ofBits 0x3F800000
def bZero : Float32.Model := Float32.Model.ofBits 0x00000000
def bTwo : Float32.Model := Float32.Model.ofBits 0x40000000
def bHalf : Float32.Model := Float32.Model.ofBits 0x3F000000
def bLarge : Float32.Model := Float32.Model.ofBits 0x7F000000
def bNegLarge : Float32.Model := Float32.Model.ofBits 0xFF000000

/-- Bit patterns used by the exactness grid (all exactly representable). -/
def exactGrid : List UInt32 :=
  [0x3F800000, 0x3F000000, 0x40000000, 0x40490FDB,
   0xBF800000, 0xBF000000, 0x40200000]

/-- Identity law at `scale = 1, offset = 0` (no clamping): proved for the
grid in exact binary32 semantics by kernel reduction. -/
theorem rangeK_identity_exact :
    exactGrid.all (fun bits =>
      rangeK modelOps (Float32.Model.ofBits bits) bOne bZero bNegLarge bLarge false
        = Float32.Model.ofBits bits) = true := by
  decide

/-- Round trip: `x*2 + 0` then `x*0.5 + 0` reconstructs `x` exactly. -/
theorem rangeK_roundtrip_exact :
    exactGrid.all (fun bits =>
      rangeK modelOps
        (rangeK modelOps (Float32.Model.ofBits bits) bTwo bZero bNegLarge bLarge false)
        bHalf bZero bNegLarge bLarge false = Float32.Model.ofBits bits) = true := by
  decide

/-- Clamping saturates: a value above the upper bound becomes the bound,
one below the lower bound becomes the lower bound. -/
theorem rangeK_saturate_exact :
    rangeK modelOps (Float32.Model.ofBits 0x41200000) bOne bZero bZero bOne true
        = bOne ∧
      rangeK modelOps (Float32.Model.ofBits 0xC1200000) bOne bZero bZero bOne true
        = bZero := by
  constructor <;> decide

/-- The clamp contract at the model level, evaluated exactly. -/
theorem clampK_exact :
    clampK modelOps (Float32.Model.ofBits 0x3F800000) bZero bTwo = bOne ∧
      clampK modelOps (Float32.Model.ofBits 0xC0000000) bZero bTwo = bZero ∧
      clampK modelOps (Float32.Model.ofBits 0x40400000) bZero bTwo = bTwo := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


/-! ## Exact-model exponential kernels (`toc_log2f` / `toc_exp2f` / `toc_powf`) -/

/-- Model-level bit construction (canonicalizing NaN). -/
def mBits (u : UInt32) : Float32.Model := Float32.Model.ofBits u

def mC0 : Float32.Model := mBits 0
def mC1 : Float32.Model := mBits 0x3F800000
def mC2 : Float32.Model := mBits 0x40000000
def mC3 : Float32.Model := mBits 0x40400000
def mC5 : Float32.Model := mBits 0x40A00000
def mC6 : Float32.Model := mBits 0x40C00000
def mC7 : Float32.Model := mBits 0x40E00000
def mC9 : Float32.Model := mBits 0x41100000
def mC24 : Float32.Model := mBits 0x41C00000
def mC120 : Float32.Model := mBits 0x42F00000
def mC720 : Float32.Model := mBits 0x44340000
def mCHalf : Float32.Model := mBits 0x3F000000
def mCLog2e : Float32.Model := mBits 0x3FB8AA3B
def mLn2 : Float32.Model := mBits 0x3F317218
def mCNaN : Float32.Model := mBits 0x7FC00000
def mCInfPos : Float32.Model := mBits 0x7F800000
def mCInfNeg : Float32.Model := mBits 0xFF800000
def mC127 : Float32.Model := mBits 0x42FE0000
def mCNeg126 : Float32.Model := mBits 0xC2FC0000

/-- `truncToIntF` over the model. -/
def mTruncToIntF (x : Float32.Model) : Int :=
  let u := x.toBits
  let sign := (u >>> 31) == 1
  let e := (u >>> 23) &&& 0xff
  let m := u &&& 0x7fffff
  let mag : Int :=
    if e < 127 then 0
    else
      let m' := (UInt32.ofNat 8388608 + m).toNat
      let se := (e - 127).toNat
      if se < 23 then Int.ofNat (m' >>> (23 - se))
      else Int.ofNat (m' <<< (se - 23))
  if sign then -mag else mag

/-- `smallIntToF32` over the model. -/
def mSmallIntToF32 (i : Int) : Float32.Model :=
  if i == 0 then mC0
  else
    let sign : UInt32 := if i < 0 then 0x80000000 else 0
    let a : Nat := if i < 0 then (-i).toNat else i.toNat
    let e : Nat := match (List.range 8).find? (fun k => a < 2 ^ (k + 1)) with
      | some k => k
      | none => 0
    let mant : UInt32 := UInt32.ofNat (a <<< (23 - e))
    let bits : UInt32 := sign ||| (UInt32.ofNat ((e + 127) <<< 23)) ||| (mant &&& 0x7fffff)
    mBits bits

/-- `toc_log2f` in exact binary32 semantics. -/
def mLog2f (x : Float32.Model) : Float32.Model :=
  if x.isNaN then x
  else if !(mC0.lt x) then (if x.lt mC0 then mCNaN else mCInfNeg)
  else
    let u := x.toBits
    let e : Int := Int.ofNat (((u >>> 23) &&& 0xff).toNat) - 127
    let m := mBits ((u &&& 0x007fffff) ||| 0x3f800000)
    let t : Float32.Model := (m - mC1) / (m + mC1)
    let t2 : Float32.Model := t * t
    let ln : Float32.Model := mC2 * t *
      (mC1 + t2 * (mC1 / mC3 + t2 * (mC1 / mC5 + t2 * (mC1 / mC7 + t2 * (mC1 / mC9)))))
    mSmallIntToF32 e + ln * mCLog2e

/-- `toc_exp2f` in exact binary32 semantics. -/
def mExp2f (x : Float32.Model) : Float32.Model :=
  if x.isNaN then x
  else if mC127.lt x then mCInfPos
  else if x.lt mCNeg126 then mC0
  else
    let ki : Int := mTruncToIntF (if Float32.Model.le mC0 x then x + mCHalf else x - mCHalf)
    let k := mSmallIntToF32 ki
    let f := x - k
    let g : Float32.Model := f * mLn2
    let p : Float32.Model := mC1 + g * (mC1 + g * (mCHalf +
      g * (mC1 / mC6 + g * (mC1 / mC24 + g * (mC1 / mC120 + g * (mC1 / mC720))))))
    let bits : UInt32 := UInt32.ofNat ((ki + 127).toNat <<< 23)
    p * mBits bits

/-- `toc_powf` in exact binary32 semantics. -/
def mPowf (x y : Float32.Model) : Float32.Model :=
  if !(mC0.lt x) then
    (if x = mC0 then (if mC0.lt y then mC0 else if y = mC0 then mC1 else mCInfPos)
     else mCNaN)
  else mExp2f (y * mLog2f x)

/-- Mirror exponent over the model: `sign(x) * |x|^e`. -/
def mMirrorPow (x e : Float32.Model) : Float32.Model :=
  if x.lt mC0 then (-mC1) * mExp2f (e * mLog2f (-x))
  else mExp2f (e * mLog2f x)

/-! ### Kernel-checked exact-semantics laws for the exponential kernels -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `log2f` exact at the powers of two used by the vectors. -/
theorem mLog2f_exact : mLog2f mC1 = mC0 ∧ mLog2f mC2 = mC1 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `powf` with exponent zero and with base one. -/
theorem mPowf_trivial : mPowf mC3 mC0 = mC1 ∧ mPowf mC1 mC3 = mC1 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Exact identity at exponent 1 on the grid values where binary32
rounding preserves it (0.5, 2, 0.25 — see the counterexample below). -/
theorem mPowf_one_exact :
    mPowf (mBits 0x3F000000) mC1 = mBits 0x3F000000 ∧
    mPowf (mBits 0x40000000) mC1 = mBits 0x40000000 ∧
    mPowf (mBits 0x3E800000) mC1 = mBits 0x3E800000 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Mirror exponent at exponent 1, including negative inputs. -/
theorem mMirrorPow_one_exact :
    mMirrorPow (mBits 0x3F000000) mC1 = mBits 0x3F000000 ∧
    mMirrorPow (mBits 0xBF000000) mC1 = mBits 0xBF000000 ∧
    mMirrorPow (mBits 0xC0000000) mC1 = mBits 0xC0000000 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `log2f ∘ exp2f` is exact on the small integer exponents. -/
theorem mLogExp_exact :
    mLog2f (mExp2f mC0) = mC0 ∧ mLog2f (mExp2f mC1) = mC1 ∧
    mLog2f (mExp2f mC2) = mC2 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- The exact identity `powf x 1 = x` is **false** in binary32 for
`x = 3`: the polynomial `exp2f ∘ log2f` rounds one ulp away. This is
why the executable laws in `Tocio/FloatSemantics.lean` are
tolerance/corpus statements rather than universal equalities. -/
theorem mPowf_one_counterexample :
    mPowf (mBits 0x40400000) mC1 ≠ mBits 0x40400000 := by
  decide

end Tocio
