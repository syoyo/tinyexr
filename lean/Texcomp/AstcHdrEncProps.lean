/-
   TinyEXR - algebraic bounds for the ASTC HDR encoder kernels.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcHdrEnc
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false

/-- The per-texel projection weight is always a 6-bit weight in `[0, 64]`.
A non-positive squared endpoint distance selects zero. -/
theorem hdrProjW_bounds (px q0 d : List Int) (dl : Int) (chs : List Nat) :
    0 ≤ hdrProjW px q0 d dl chs ∧ hdrProjW px q0 d dl chs ≤ 64 := by
  unfold hdrProjW
  split
  · norm_num
  · rename_i hdl
    have hdlpos : 0 < dl := by omega
    let dot0 := chs.foldl (fun acc c =>
      acc + ((px.getD c 0) - q0.getD c 0) * d.getD c 0) 0
    let dot := if dot0 < 0 then 0 else if dot0 > dl then dl else dot0
    have hdot0 : 0 ≤ dot := by
      dsimp [dot]
      split <;> omega
    have hdotdl : dot ≤ dl := by
      dsimp [dot]
      split <;> omega
    have hnum0 : 0 ≤ dot * 64 + dl / 2 := by
      have hhalf : 0 ≤ dl / 2 := by omega
      nlinarith
    have hnumlt : dot * 64 + dl / 2 < 64 * dl + dl := by
      have hhalf : dl / 2 < dl := by omega
      nlinarith
    change 0 ≤ (dot * 64 + dl / 2) / dl ∧ (dot * 64 + dl / 2) / dl ≤ 64
    constructor
    · rw [Int.le_ediv_iff_mul_le hdlpos]
      simpa using hnum0
    · rw [Int.ediv_le_iff_le_mul hdlpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnumlt

end Texcomp
