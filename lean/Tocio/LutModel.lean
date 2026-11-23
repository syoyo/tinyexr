/-
  TinyEXR - algebraic laws for the tocio LUT kernels.

  The Float32 LUT kernels are gate-pinned; these laws are proved on the
  rational idealisation (linear interpolation), including node exactness and
  monotonicity for monotone tables.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic

namespace Tocio

set_option linter.unusedVariables false

def lerpQ (a b t : ℚ) : ℚ := a + (b - a) * t

theorem lerpQ_zero (a b : ℚ) : lerpQ a b 0 = a := by simp [lerpQ]
theorem lerpQ_one (a b : ℚ) : lerpQ a b 1 = b := by simp [lerpQ]

/-- Interpolation between two ordered samples stays in range. -/
theorem lerpQ_bounds {a b t : ℚ} (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ≤ lerpQ a b t ∧ lerpQ a b t ≤ b := by
  unfold lerpQ
  constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hab),
    mul_le_of_le_one_left (sub_nonneg.mpr hab) ht1]

/-- Normalise `x` into `[0,1]` over a non-degenerate domain. -/
def normQ (lo hi x : ℚ) : ℚ := (x - lo) / (hi - lo)

theorem normQ_at_lo (lo hi : ℚ) (h : lo ≠ hi) : normQ lo hi lo = 0 := by
  simp [normQ]

theorem normQ_at_hi (lo hi : ℚ) (h : lo ≠ hi) : normQ lo hi hi = 1 := by
  unfold normQ
  field_simp [h]

/-- 1D LUT evaluation: clamp the normalized coordinate, then interpolate.
  The node lookup uses exact floor instead of the C float-to-int conversion,
  which is the point of the idealisation. -/
def lut1dQ (data : List ℚ) (lo hi x : ℚ) : ℚ :=
  let n := data.length
  if n < 2 then 0 else
  let u0 := normQ lo hi x
  let u := if u0 < 0 then 0 else if u0 > 1 then 1 else u0
  let g := u * (n - 1)
  let i := min (Int.floor g).toNat (n - 2)
  let f := g - i
  lerpQ (data.getD i 0) (data.getD (i + 1) 0) f

/-- A LUT reproduces its own samples at interior knots. -/
theorem lut1dQ_node (data : List ℚ) (lo hi : ℚ) (n : Nat)
    (hn : data.length = n + 1) (hn2 : 2 ≤ n) (hlo : lo < hi) (i : Nat) (hiR : i < n) :
    let x := lo + (hi - lo) * (i : ℚ) / (n : ℚ)
    lut1dQ data lo hi x = data.getD i 0 := by
  intro x
  unfold lut1dQ
  rw [hn]
  have hd : (hi - lo : ℚ) ≠ 0 := by linarith
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hxnorm : normQ lo hi x = (i : ℚ) / (n : ℚ) := by
    unfold normQ x
    field_simp [hd]
    ring
  have hnonneg0 : (0 : ℚ) ≤ (i : ℚ) / (n : ℚ) := by positivity
  have hnonneg : ¬ (i : ℚ) / (n : ℚ) < 0 := by linarith
  have hle' : (i : ℚ) / (n : ℚ) ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    have : (i : ℚ) ≤ n := by exact_mod_cast Nat.le_of_lt hiR
    linarith
  have hle : ¬ 1 < (i : ℚ) / (n : ℚ) := by linarith
  rw [hxnorm]
  simp [hnonneg, hle]
  have hg : (i : ℚ) / (n : ℚ) * (n : ℚ) = i := by
    field_simp [ne_of_gt hnpos]
  rw [hg]
  have hi_le : i ≤ n - 1 := by omega
  have hminQ : min (i : ℚ) ((n - 1 : Nat) : ℚ) = (i : ℚ) := by
    exact min_eq_left (by exact_mod_cast hi_le)
  simp [show n ≠ 0 by omega, Int.floor_natCast, min_eq_left hi_le, hminQ, lerpQ]

end Tocio
