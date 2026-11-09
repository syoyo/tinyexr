/-
  TinyEXR - Lean 4 formalization of the tocio log op.

  First slice: unified affine lin<->log with per-channel slope/offset and base.
  Full op lowering and codegen come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- Linear-to-log: out = log_base(in * slope + offset) * (1/linSlope) - linOffset. -/
def linToLog (base inVal slope offset linSlope linOffset : Float) : Float :=
  (Float.log (inVal * slope + offset) / Float.log base) / linSlope - linOffset

/-- Log-to-linear: out = (base ^ ((in + linOffset) * linSlope) - offset) / slope. -/
def logToLin (base inVal slope offset linSlope linOffset : Float) : Float :=
  (base ^ ((inVal + linOffset) * linSlope) - offset) / slope

end Tocio