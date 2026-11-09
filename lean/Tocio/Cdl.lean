/-
  TinyEXR - Lean 4 formalization of the tocio CDL op.

  First slice: CDL (slope, offset, power, saturation about luma). The inverse
  decomposition (saturation->Matrix, power->Exponent, slope/offset->Range) is
  modelled at the lowering level in a later slice.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- Luma from RGB using the CDL luma coefficients. -/
def cdlLuma (r g b lr lg lb : Float) : Float :=
  r * lr + g * lg + b * lb

/-- CDL forward (per channel, before saturation): (in * slope + offset) ^ power. -/
def cdlChannel (inVal slope offset power : Float) : Float :=
  (inVal * slope + offset) ^ power

/-- CDL saturation: mix between luma and the channel value. -/
def cdlSat (channel luma sat : Float) : Float :=
  luma + (channel - luma) * sat

end Tocio