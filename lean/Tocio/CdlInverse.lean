/-
  TinyEXR - Lean 4 formalization of CDL inverse decomposition.

  Models the tocio approach: CDL inverse is decomposed at lowering time into
  MatrixTransform (inverse saturation) + ExponentTransform (inverse power) +
  RangeTransform (inverse slope/offset).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op
import Tocio.Processor
import Tocio.Transform

namespace Tocio

/-- A lowered CDL inverse produces 3 ops: matrix, exponent, range. -/
def cdlInverseOps : OpList :=
  OpList.append (OpList.append (OpList.append OpList.empty OpKind.matrix) OpKind.exponent) OpKind.range

/-- CDL inverse produces 3 ops. -/
theorem cdlInverse_length : cdlInverseOps.length = 3 := by
  unfold cdlInverseOps OpList.length OpList.empty OpList.append
  simp

/-- CDL forward produces 1 op. -/
def cdlForwardOps : OpList := OpList.append OpList.empty OpKind.cdl

theorem cdlForward_length : cdlForwardOps.length = 1 := by
  unfold cdlForwardOps OpList.length OpList.empty OpList.append
  simp

end Tocio