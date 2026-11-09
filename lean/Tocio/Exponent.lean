/-
  TinyEXR - Lean 4 formalization of the tocio exponent op.

  First slice: per-channel exponent (out = pow(max(0,in), e)) with mirror
  (sign(x)*pow(|x|,e)) mode. Full op lowering and codegen come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- Mirror exponent: sign(x) * |x|^e. -/
def mirrorPow (x e : Float) : Float :=
  if x ≥ 0.0 then x ^ e else -( (-x) ^ e )

/-- Plain exponent: max(0,x)^e. -/
def plainPow (x e : Float) : Float :=
  if x ≥ 0.0 then x ^ e else 0.0

-- When e=1, mirrorPow is identity.
-- theorem mirrorPow_one (x : Float) : mirrorPow x 1.0 = x := by sorry

end Tocio