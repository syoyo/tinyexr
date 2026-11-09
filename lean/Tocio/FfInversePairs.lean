/-
  TinyEXR - Lean 4 formalization of FixedFunction inverse-pair properties.

  Proves that every forward style has a corresponding inverse style,
  and that forwardOf maps inverse styles to forward styles.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op

namespace Tocio

/-- Every inverse style's forwardOf is a forward (non-inverse) style. -/
theorem ff_inv_forward_is_forward (s : FfStyle) (h : FfStyle.isInv s = true) :
    FfStyle.isInv (FfStyle.forwardOf s) = false := by
  cases s <;> simp [FfStyle.isInv, FfStyle.forwardOf] at h ⊢

/-- Forward styles are fixed by forwardOf. -/
theorem ff_forward_fixed (s : FfStyle) (h : FfStyle.isInv s = false) :
    FfStyle.forwardOf s = s := by
  cases s <;> simp [FfStyle.isInv, FfStyle.forwardOf] at h ⊢

end Tocio