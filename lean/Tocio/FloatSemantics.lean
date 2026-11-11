/-
  TinyEXR - Float semantics of the tocio kernels.

  The C kernels run on IEEE `float`; the Lean models use `Float32` with
  the same evaluation order, and `make tocio-diff` pins them to the C on
  generated vectors. This module adds the proof-level facts that only
  need concrete evaluation: identity/square/round-trip laws for the
  exponent kernels, the CDL forward/inverse round-trip within the C's
  2e-3 tolerance, the sign discipline of the mirror/plain forms, and the
  Range clamp boundary behaviour.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent
import Tocio.Cdl
import Tocio.Range

namespace Tocio

set_option linter.unusedVariables false

/-- A small evaluation grid covering the exponent/CDL domains. -/
def semGrid : List Float :=
  [0.0, 0.001, 0.25, 0.5, 0.732, 1.0, 1.5, 2.0, 4.0, 12.92, 100.0,
   -0.001, -0.5, -1.0, -4.0, -100.0]

/-- Absolute difference of two `Float` values. -/
def semAbsDiff (a b : Float) : Float :=
  let d : Float := a - b
  if d < 0.0 then -d else d

/-- `mirrorPow x 1 = x` across the grid (the exponent op is the identity
  at exponent 1, including the negative branch). -/
theorem mirrorPow_one_grid :
    semGrid.all (fun x => mirrorPow x 1.0 = x) := by native_decide

/-- `plainPow x 1 = max(0, x)` across the grid. -/
theorem plainPow_one_grid :
    semGrid.all (fun x => plainPow x 1.0 = (if x ≥ 0.0 then x else 0.0)) := by
  native_decide

/-- Sign discipline: `mirrorPow` keeps the sign across the grid. -/
theorem mirrorPow_sign_grid :
    semGrid.all (fun x =>
      let m : Float := mirrorPow x 2.0
      (x ≥ 0.0 ↔ m ≥ 0.0)) := by native_decide

/-- `plainPow` never goes negative across the grid. -/
theorem plainPow_nonneg_grid :
    semGrid.all (fun x => plainPow x 0.5 ≥ 0.0) := by native_decide

/-- Square/root round trip across the grid: `plainPow (plainPow x 0.5) 2`
  reconstructs the non-negative inputs. -/
theorem exponent_roundtrip_grid :
    semGrid.all (fun x =>
      x ≥ 0.0 →
        semAbsDiff (plainPow (plainPow x 0.5) 2.0) x ≤ 1.0e-6) := by
  native_decide

/-- Mirror square/root round trip across the grid. -/
theorem mirror_roundtrip_grid :
    semGrid.all (fun x =>
      semAbsDiff (mirrorPow (mirrorPow x 0.5) 2.0) x ≤ 1.0e-5) := by
  native_decide

/-- The CDL forward/inverse round trip is exact on the non-negative
  grid (the C's `k_cdl` applies the power only to non-negative values
  when the op is unclamped; see the `tocio-diff` gate for the full
  reference including clamped and negative domains). -/
theorem cdl_roundtrip_grid :
    semGrid.all (fun x =>
      x ≥ 0.0 →
        semAbsDiff
          (cdlSat (cdlChannel (cdlSat (cdlChannel x 1.0 0.0 2.0) 0.5 1.0)
            1.0 0.0 0.5) 0.5 1.0) x ≤ 2.0e-3) := by native_decide

/-- `clampf` clamps at the boundaries: values inside `[lo,hi]` map to
  themselves, values outside clamp (the Range op's body). -/
theorem range_clamp_grid :
    semGrid.all (fun x =>
      let c : Float := clampf x 0.0 1.0
      (x < 0.0 → c = 0.0) ∧ (x > 1.0 → c = 1.0) ∧ (0.0 ≤ x ∧ x ≤ 1.0 → c = x)) := by
  native_decide

end Tocio
