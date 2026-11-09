/-
  TinyEXR - Lean 4 formalization of range op inverse properties.

  Proves that clampf is identity when x is not below lo and not above hi.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Range

namespace Tocio

/-- clampf is identity when x is not below lo and not above hi. -/
theorem clampf_identity' (x lo hi : Float) (hlo : ¬ (x < lo)) (hhi : ¬ (hi < x)) :
    clampf x lo hi = x := by
  unfold clampf
  simp [hlo, hhi]

/-- rangeOp is identity under the same conditions (with x*scale+offset = x). -/
theorem rangeOp_identity' (x scale offset lo hi : Float)
    (hs : x * scale + offset = x) (hlo : ¬ (x < lo)) (hhi : ¬ (hi < x)) :
    rangeOp scale offset lo hi x = x := by
  unfold rangeOp
  rw [hs]
  exact clampf_identity' x lo hi hlo hhi

end Tocio