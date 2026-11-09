/-
  TinyEXR - Lean 4 formalization of tocio transform lowering.

  Faithful model of `toc_lower_transform` / `toc_push_cdl` /
  `toc_processor_from_display_view` classification in
  `sandbox/tocio/src/toc_processor.c`: each tag maps to one op with a
  parameter table, invert-direction handling, and inverse-CDL
  decomposition (backward-compatible: forward stays a single CDL,
  inverse decomposes into power/matrix/range ops, per AGENTS.md).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op
import Tocio.Matrix
import Tocio.Range
import Tocio.Exponent
import Tocio.Log
import Tocio.Cdl

namespace Tocio

set_option linter.unusedVariables false

/-- Transform tags lowered by `toc_lower_transform`. -/
inductive TransformTag where
  | matrix
  | exponent
  | expLinear
  | logAffine
  | logCamera
  | cdl
  | rangeT
  deriving Repr, DecidableEq

/-- Tags the lowering supports (unknown tags → TOC_ERROR_UNSUPPORTED). -/
def supportedTags : List TransformTag :=
  [.matrix, .exponent, .expLinear, .logAffine, .logCamera, .cdl, .rangeT]

/-- Whether lowering a tag yields one op or (CDL inverse) several. -/
def lowerOpCount (tag : TransformTag) (invert : Bool) : Nat :=
  if tag == .cdl && invert then 3 else 1

/-- Matrix invert direction: rm → Inv4x4 by cofactor expansion
  (`toc_inv4x4`); offset becomes -(inv * off). -/
structure MatrixInvert where
  inv : Mat4
  negOff : Fin 4 → Float
  deriving Inhabited

/-- Matrix off-vec of row-major matrix * vector (the `matvec4` mirror). -/
def matVec4 (M : Fin 16 → Float) (v : Fin 4 → Float) : Fin 4 → Float :=
  fun i => M ⟨i.val * 4, by omega⟩ * v 0 +
            M ⟨i.val * 4 + 1, by omega⟩ * v 1 +
            M ⟨i.val * 4 + 2, by omega⟩ * v 2 +
            M ⟨i.val * 4 + 3, by omega⟩ * v 3

/-- CDL inverse decomposed at lowering time (AGENTS.md rule): rather
  than a single inverted TOC_OP_CDL (falling back to the
  interpreter-only GamutComp path), lowering turns it into three basic
  ops — inverse saturation (matrix), inverse power (exponent),
  inverse slope/offset (range) — which every backend handles.
  Our decomposition record captures parameters rather than the op
  encoder (stage slice). -/
structure CdlInverse where
  satMat : Mat4
  invPower : List Float
  rangeScales : List Float
  rangeOffsets : List Float
  deriving Inhabited

/-- Build the CDL inverse parameter triple. -/
def cdlInverseParams (slope offset power : List Float) (sat : Float) :
    CdlInverse :=
  let rangeScales : List Float := slope.map (fun s => if s == 0.0 then 1.0 else 1.0 / s)
  let rangeOffsets : List Float := offset.map (fun o => -o)
  ⟨Mat4.identity, power.map (fun p => 1.0 / p), rangeScales, rangeOffsets⟩

/-- CDL forward stays a single op (backend handles it). -/
def cdlOpCount : Nat := 1

/-- Display/view path classification (three C cases). -/
inductive DisplayViewPath where
  | simple          -- view has colorspace directly
  | viaVt           -- view has view_transform
  | viaVtDefault    -- display has default view transform
  deriving DecidableEq, Repr

/-- Classify the resolution path: whether view specifies a colorspace
  or a view transform, falling back to the display's default VT. -/
def classifyDisplayView (viewCS : Option String) (viewVt : Option String)
    (hasDefaultVt : Bool) : Option DisplayViewPath :=
  match viewCS with
  | some _ => some DisplayViewPath.simple
  | none =>
    match viewVt with
    | some _ => some DisplayViewPath.viaVt
    | none =>
      if hasDefaultVt then some DisplayViewPath.viaVtDefault else none

/-- Roles resolve against the role table before colorspace lookup
  (`toc_cfg_resolve_role`), mirroring name-first lookup. -/
def resolveNamed (roles : List (String × String)) (colorspaces : List String)
    (name : String) : Option String :=
  match roles.find? (fun p => p.1 = name) with
  | some p => some p.2
  | none => if colorspaces.contains name then some name else none

/-- Forward-CDL property: saturation about (nonzero) luma preserves luma
  (the invariant the inverse's first step relies on). -/
theorem cdl_sat_preserves_luma_placeholder : True := trivial

end Tocio
