/-
  TinyEXR - Lean 4 formalization of tocio transform lowering.

  First slice: transform kinds (matrix, range, exponent, etc.) and a
  lowering function that maps a transform to an op list. Full config
  resolution and nested transforms come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op
import Tocio.Processor

namespace Tocio

/-- Transform kinds in OCIO. -/
inductive TransformKind where
  | colorSpace
  | displayView
  | matrix
  | range
  | exponent
  | cdl
  | fixedFunc (style : FfStyle)
  | noop
  deriving Repr

/-- Lower a single transform kind to an op list. -/
def lowerTransform (t : TransformKind) : OpList :=
  match t with
  | .colorSpace => OpList.empty
  | .displayView => OpList.empty
  | .matrix => OpList.append OpList.empty OpKind.matrix
  | .range => OpList.append OpList.empty OpKind.range
  | .exponent => OpList.append OpList.empty OpKind.exponent
  | .cdl => OpList.append OpList.empty OpKind.cdl
  | .fixedFunc _ => OpList.append OpList.empty OpKind.fixedfunc
  | .noop => OpList.empty

/-- Lowering a noop produces an empty op list. -/
theorem lower_noop_empty : (lowerTransform TransformKind.noop).length = 0 := by
  unfold lowerTransform OpList.length OpList.empty
  rfl

/-- Lowering a matrix produces a 1-op list. -/
theorem lower_matrix_one : (lowerTransform TransformKind.matrix).length = 1 := by
  unfold lowerTransform OpList.length OpList.empty OpList.append
  simp

/-- Lowering preserves: noop has length 0. -/
theorem lower_noop_zero : (lowerTransform .noop).ops = [] := by
  unfold lowerTransform OpList.empty
  rfl

end Tocio