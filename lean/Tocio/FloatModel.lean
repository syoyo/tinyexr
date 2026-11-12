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

end Tocio
