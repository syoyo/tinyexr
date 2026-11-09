/-
  TinyEXR - Lean 4 formalization of the tocio LogCamera op.

  First slice: LogCamera (affine log + linear segment below break).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- LogCamera forward: if x >= linBreak then log(x) else linear segment. -/
def logCameraFwd (base linBreak linSlope linOffset logSlope logOffset x : Float) : Float :=
  if x >= linBreak then (Float.log x / Float.log base) * logSlope + logOffset
  else x * linSlope + linOffset

end Tocio