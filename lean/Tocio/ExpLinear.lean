/-
  TinyEXR - Lean 4 formalization of the tocio ExponentWithLinear (MonCurve) op.

  First slice: the piecewise linear/power curve. Full op lowering comes later.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- ExponentWithLinear forward: y = (x*scale+offset)^gamma if x > breakpoint,
    else x*slope. Mirror applies sign. -/
def expLinearFwd (scale offset gamma breakpoint slope x : Float) : Float :=
  if x > breakpoint then (x * scale + offset) ^ gamma else x * slope

/-- Inverse is the analytic inverse (placeholder). -/
def expLinearInv (scale offset gamma breakpoint slope x : Float) : Float :=
  if x > breakpoint ^ gamma then (x ^ (1.0 / gamma) - offset) / scale else x / slope

end Tocio