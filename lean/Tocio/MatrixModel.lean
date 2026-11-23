/-
  TinyEXR - algebraic laws for the tocio matrix kernel.

  The Float32 kernel in `Tocio.Ops` is gate-pinned; these laws are proved on
  the corresponding rational model, where IEEE rounding cannot interfere.
  They justify the identity/inverse rewrites used by lowering.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic

namespace Tocio

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- Column-major 4x4 matrix as 16 rationals. -/
def matIdQ : List ℚ :=
  (List.range 16).map (fun i => if i % 5 == 0 then 1 else 0)

def matApplyQ (m : List ℚ) (v : List ℚ) : List ℚ :=
  (List.range 4).map (fun i =>
    m.getD i 0 * v.getD 0 0 +
    m.getD (i + 4) 0 * v.getD 1 0 +
    m.getD (i + 8) 0 * v.getD 2 0 +
    m.getD (i + 12) 0 * v.getD 3 0)

def matMulQ (a b : List ℚ) : List ℚ :=
  (List.range 16).map (fun k =>
    let i := k % 4
    let j := k / 4
    a.getD i 0 * b.getD (j * 4) 0 +
    a.getD (i + 4) 0 * b.getD (j * 4 + 1) 0 +
    a.getD (i + 8) 0 * b.getD (j * 4 + 2) 0 +
    a.getD (i + 12) 0 * b.getD (j * 4 + 3) 0)

theorem matIdQ_length : matIdQ.length = 16 := by simp [matIdQ]

theorem matId_apply (v : List ℚ) (hv : v.length = 4) : matApplyQ matIdQ v = v := by
  apply List.ext_get
  · simp [matApplyQ]; omega
  · intro n hn
    have hn4 : n < 4 := by simpa [matApplyQ] using hn
    interval_cases n <;> simp [matApplyQ, matIdQ, hv] 

theorem matApply_mul (a b : List ℚ) (v : List ℚ) :
    matApplyQ (matMulQ a b) v = matApplyQ a (matApplyQ b v) := by
  apply List.ext_get
  · simp [matApplyQ, matMulQ]
  · intro n hn
    have hn4 : n < 4 := by simpa [matApplyQ, matMulQ] using hn
    interval_cases n <;> simp [matApplyQ, matMulQ] <;> ring

theorem matMul_assoc (a b c : List ℚ) :
    matMulQ (matMulQ a b) c = matMulQ a (matMulQ b c) := by
  apply List.ext_get
  · simp [matMulQ]
  · intro n hn
    have hn16 : n < 16 := by simpa [matMulQ] using hn
    interval_cases n <;> simp [matMulQ] <;> ring

/-- Any explicit right inverse cancels on vectors. -/
theorem matApply_inv {m inv v : List ℚ} (hv : v.length = 4)
    (h : matMulQ m inv = matIdQ) :
    matApplyQ m (matApplyQ inv v) = v := by
  rw [← matApply_mul, h, matId_apply v hv]

end Tocio
