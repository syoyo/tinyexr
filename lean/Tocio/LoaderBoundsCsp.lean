/-
  TinyEXR - allocation guards for the tocio CSP and .cube LUT readers.

  The C readers call `toc_values_fit(count, p, end)` before indexing the
  text and check exact counts afterwards. These lemmas capture the guard's
  soundness for the Lean models.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic
import Tocio.Csp
import Tocio.LutFile
import Tocio.LoaderBounds

namespace Tocio

set_option linter.unusedVariables false

/-- CSP's guard is the same `toc_values_fit` predicate used by the SPI
  reader, so a "fits" answer bounds the count by the available characters. -/
theorem valuesFitC_sound {count avail : Nat} (ha : 2 ≤ avail)
    (h : valuesFitC count avail = true) : count ≤ avail := by
  change spiValuesFit count avail = true at h
  exact spiValuesFit_le ha h

/-- The .cube reader's guard is `want ≤ remaining`. -/
theorem cube_valuesFit_sound {want remaining : Nat}
    (h : valuesFit want remaining = true) : want ≤ remaining := by
  unfold valuesFit at h
  simpa using h

/-- A valid 1D cube's sample count is bounded by the declared size × channels. -/
theorem cube1d_count_bound (n ch : Nat) (hvalid : 2 ≤ n ∧ n ≤ 256)
    (hch : ch == 1 || ch == 3) : n * ch ≤ 256 * 3 := by
  rw [Bool.or_eq_true] at hch
  rcases hch with h1 | h3
  · have hc : ch = 1 := by simpa using h1
    rw [hc]
    omega
  · have hc : ch = 3 := by simpa using h3
    rw [hc]
    omega

/-- A valid 3D cube's sample count is bounded by 256³ × 3. -/
theorem cube3d_count_bound (n : Nat) (hvalid : 2 ≤ n ∧ n ≤ 256) :
    n * n * n * 3 ≤ 256 * 256 * 256 * 3 := by
  have hnle : n ≤ 256 := hvalid.2
  have h2 : n * n ≤ 256 * 256 := Nat.mul_le_mul hnle hnle
  have h3 : n * n * n ≤ 256 * 256 * 256 := Nat.mul_le_mul h2 hnle
  exact Nat.mul_le_mul_right 3 h3

end Tocio
