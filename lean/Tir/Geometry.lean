/-
  TinyEXR - Lean 4 model of the tir (tiny image resize) axis geometry.

  Mirrors `axis_geom_init` / `axis_center` / `filter_radius` in
  `tools/resize/src/tir_table.c`. The coefficient *values* are built with
  libm (`sin`, `exp`, `sqrt`) and are therefore pinned by the C-vs-Lean
  differential gate rather than re-derived here; this module fixes the
  geometry and the parameter semantics that determine the table layout.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tir

set_option linter.unusedVariables false

/-- `tir_filter`. -/
inductive Filter where
  | box
  | triangle
  | bspline
  | gaussian
  | mitchell
  | catmullRom
  | lanczos2
  | lanczos3
  | kaiser
  deriving Repr, DecidableEq, Inhabited

/-- `tir_edge_mode`. -/
inductive Edge where
  | clamp
  | reflect
  | wrap
  deriving Repr, DecidableEq, Inhabited

/-- `tir_registration`. -/
inductive Registration where
  | cellCentered
  | gridVertex
  deriving Repr, DecidableEq, Inhabited

/-- `tir_pixel_type`. -/
inductive PixelType where
  | f32
  | f16
  | u8
  | u16
  deriving Repr, DecidableEq, Inhabited

/-- `tir_mode`. -/
inductive Mode where
  | general
  | normalMap
  | heightmap
  deriving Repr, DecidableEq, Inhabited

/-- `filter_radius`: half-width in source samples (before `filter_scale`).
  The Gaussian is truncated at 3 sigma with a 0.5 floor. -/
def filterRadius (f : Filter) (sigma : Float) : Float :=
  match f with
  | .box => 0.5
  | .triangle => 1.0
  | .gaussian => if 3.0 * sigma < 0.5 then 0.5 else 3.0 * sigma
  | .lanczos3 => 3.0
  | .kaiser => 3.0
  | _ => 2.0

/-- `axis_geom`. -/
structure AxisGeom where
  ratio : Float
  support : Float
  kscale : Float
  boxSb : Float
  isDown : Bool
  useVertex : Bool
  deriving Repr

/-- `Nat` → `Float` (C `(double)` cast of a non-negative count). -/
def natToFloat (n : Nat) : Float := Float.ofNat n

/-- `axis_geom_init`. `filterScale` is the resolved positive scale and
  `sigma` the resolved Gaussian sigma (the C validates both up front). -/
def axisGeomInit (s d : Nat) (f : Filter) (reg : Registration)
    (filterScale sigma : Float) : AxisGeom :=
  let useVertex := reg == .gridVertex && d > 1 && s > 1
  let ratio : Float :=
    if useVertex then natToFloat (s - 1) / natToFloat (d - 1)
    else natToFloat s / natToFloat d
  let fscale0 : Float := (if ratio > 1.0 then ratio else 1.0) * filterScale
  let fscale : Float := if fscale0 < 1.0 then 1.0 else fscale0
  { ratio := ratio
    support := filterRadius f sigma * fscale
    kscale := fscale
    boxSb := 0.5 * fscale
    isDown := ratio > 1.0
    useVertex := useVertex }

/-- `axis_center`: source coordinate of output sample `i`. -/
def axisCenter (g : AxisGeom) (s d : Nat) (i : Nat) : Float :=
  if g.useVertex then
    natToFloat i * (natToFloat (s - 1) / natToFloat (d - 1))
  else
    (natToFloat i + 0.5) * (natToFloat s / natToFloat d) - 0.5

/-- The vertex flag only turns on with both axes above one sample. -/
theorem axisGeomInit_useVertex_imp (s d : Nat) (f : Filter) (reg : Registration)
    (filterScale sigma : Float) (h : (axisGeomInit s d f reg filterScale sigma).useVertex = true) :
    1 < d ∧ 1 < s := by
  unfold axisGeomInit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

end Tir
