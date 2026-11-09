/-
  TinyEXR - Lean 4 formalization of the tocio range op.

  First slice: per-channel range clamp (out = clamp(in*scale+offset, min, max))
  and the identity property when scale=1, offset=0, min=-inf, max=+inf (modelled
  as no clamping). Full op lowering and codegen come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- Clamp a Float to [lo, hi]. -/
def clampf (x lo hi : Float) : Float :=
  if x < lo then lo else if x > hi then hi else x

/-- Per-channel range op (scalar, channel 0). -/
def rangeOp (scale offset lo hi x : Float) : Float :=
  clampf (x * scale + offset) lo hi

-- When scale=1, offset=0, and bounds are non-restrictive, rangeOp is identity.
-- (Proof deferred to a later slice: requires Float arithmetic simplification lemmas.)

end Tocio