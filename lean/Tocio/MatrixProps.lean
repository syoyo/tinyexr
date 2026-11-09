/-
  TinyEXR - Lean 4 formalization of matrix op properties.

  Proves structural properties of the identity matrix.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity matrix has 1.0 on the diagonal. -/
theorem mat4_identity_diag (i : Fin 4) :
    (Mat4.identity.m ⟨i.val + 4 * i.val, by omega⟩) = 1.0 := by
  unfold Mat4.identity
  simp
  have : (i.val + 4 * i.val) % 5 = 0 := by
    omega
  simp [this]

/-- Identity matrix has 0.0 off the diagonal. -/
theorem mat4_identity_offdiag (i j : Fin 4) (h : i ≠ j) :
    (Mat4.identity.m ⟨i.val + 4 * j.val, by omega⟩) = 0.0 := by
  unfold Mat4.identity
  simp
  have : (i.val + 4 * j.val) % 5 ≠ 0 := by
    omega
  simp [this]

end Tocio