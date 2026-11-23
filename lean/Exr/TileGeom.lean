/-
  TinyEXR - 64-bit ceil-division used by tile geometry (task.md S4).

  The C computes `((int64_t)value + divisor - 1) / divisor` so large tile
  sizes cannot overflow the 32-bit `value + divisor - 1` expression.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Exr

set_option linter.unusedVariables false

def ceilDivPos (value divisor : Int) : Int := (value + divisor - 1) / divisor

theorem ceilDivPos_pos {v d : Int} (hv : 0 < v) (hd : 0 < d) : 0 < ceilDivPos v d := by
  change 0 < (v + d - 1) / d
  have hsum : 0 < v + d - 1 := by omega
  have hle : 1 ≤ (v + d - 1) / d := by
    apply Int.le_ediv_of_mul_le hd
    omega
  omega

theorem ceilDivPos_covers {v d : Int} (hv : 0 < v) (hd : 0 < d) :
    v ≤ d * ceilDivPos v d := by
  change v ≤ d * ((v + d - 1) / d)
  let n : Int := v + d - 1
  change v ≤ d * (n / d)
  have hr : n % d < d := Int.emod_lt_of_pos n hd
  have hdecomp := Int.emod_add_mul_ediv n d
  omega

end Exr
