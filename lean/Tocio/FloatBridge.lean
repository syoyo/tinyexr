/-
  TinyEXR - the float-semantics bridge for the tocio kernel proofs.

  Lean 4.35 ships an exact IEEE-754 model for `Float32`
  (`Init.Data.Float.Model.Float32`: `Float32.Model` is a bit-pattern
  subtype of `UInt32` whose `add`/`sub`/`mul`/`div`/`sqrt`/comparisons
  are *defined* via `UnpackedFloat` round-to-nearest operations).
  However, the operations on `Float32` itself are compiler externs
  (`@[extern "lean_float32_add"]`), i.e. they have no kernel equations.
  The toolchain's own documentation (Init/Data/Float/Float32.lean,
  "Like other low-level types ... Some of the operations on `Float32`
  are defined in terms of their `Float32.Model` counterparts, while
  others are opaque to Lean's kernel") asks users who want to prove
  properties of `Float32` programs to *prove the equivalence to the
  model themselves* and then transfer lemmas.

  That equivalence is not provable in Lean's kernel, so this module
  records it as an explicit hypothesis (`FloatBridge`) rather than as
  an axiom: the axiom gate stays clean, float proofs can be carried
  out *relative to* the bridge, and the sampled-grid `native_decide`
  fixtures in `Tocio/FloatSemantics.lean` remain the executable
  evidence until a kernel-level model connection exists.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Math

namespace Tocio

open Float32.Model

/-- Model-level single-precision addition. -/
def f32AddM (a b : Float32) : Float32 := Float32.ofModel (a.toModel.add b.toModel)

/-- Model-level subtraction. -/
def f32SubM (a b : Float32) : Float32 := Float32.ofModel (a.toModel.sub b.toModel)

/-- Model-level multiplication. -/
def f32MulM (a b : Float32) : Float32 := Float32.ofModel (a.toModel.mul b.toModel)

/-- Model-level division. -/
def f32DivM (a b : Float32) : Float32 := Float32.ofModel (a.toModel.div b.toModel)

/-- Model-level negation. -/
def f32NegM (a : Float32) : Float32 := Float32.ofModel (-a.toModel)

/-- Model-level `a < b`. -/
def f32LtM (a b : Float32) : Bool := a.toModel.lt b.toModel

/-- Model-level `a ≤ b`. -/
def f32LeM (a b : Float32) : Bool := a.toModel.le b.toModel

/-- The bridge hypothesis: every `Float32` primitive used by the tocio
kernels implements its `Float32.Model` counterpart.  This is the
statement the toolchain leaves to users; it is not provable in Lean's
kernel (the primitives are externs) and is therefore a hypothesis, not
an axiom.  Under it, the exact IEEE-754 semantics of `Float32.Model`
can be used to reason about the kernel definitions. -/
def FloatBridge : Prop :=
  (∀ a b : Float32, a + b = f32AddM a b) ∧
  (∀ a b : Float32, a - b = f32SubM a b) ∧
  (∀ a b : Float32, a * b = f32MulM a b) ∧
  (∀ a b : Float32, a / b = f32DivM a b) ∧
  (∀ a : Float32, -a = f32NegM a) ∧
  (∀ a b : Float32, (a < b) = f32LtM a b) ∧
  (∀ a b : Float32, (a ≤ b) = f32LeM a b)

/-- Projection lemmas: under the bridge each primitive carries its exact
model semantics, which is what transfer proofs consume. -/
theorem FloatBridge.add_eq (h : FloatBridge) (a b : Float32) :
    a + b = f32AddM a b := h.1 a b

theorem FloatBridge.mul_eq (h : FloatBridge) (a b : Float32) :
    a * b = f32MulM a b := h.2.2.1 a b

theorem FloatBridge.div_eq (h : FloatBridge) (a b : Float32) :
    a / b = f32DivM a b := h.2.2.2.1 a b

theorem FloatBridge.lt_eq (h : FloatBridge) (a b : Float32) :
    (a < b) = f32LtM a b := h.2.2.2.2.2.1 a b

end Tocio
