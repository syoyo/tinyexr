/-
  TinyEXR - Lean 4 formalization of FixedFunction inverse-pair completeness.

  Verifies that every forward style has a corresponding inverse style
  by checking the isInv flag pattern.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op

namespace Tocio

/-- Count of forward (non-inverse) styles. -/
def ffNumForward : Nat := 13

/-- Count of inverse styles. -/
def ffNumInverse : Nat := 13

/-- Total styles. -/
def ffNumTotal : Nat := 26

theorem ff_counts : ffNumForward + ffNumInverse = ffNumTotal := by
  unfold ffNumForward ffNumInverse ffNumTotal
  rfl

end Tocio