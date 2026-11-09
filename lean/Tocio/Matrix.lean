/-
  TinyEXR - Lean 4 formalization of the tocio matrix op.

  First slice: 4x4 column-major matrix multiply on RGBA vectors, plus the
  identity matrix and its left/right identity property. Full op lowering
  and codegen equivalence come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- A 4x4 column-major matrix. -/
structure Mat4 where
  m : Fin 16 → Float
  deriving Inhabited

/-- Apply a matrix to an RGBA vector (col-major: out_i = sum_j m[i+4*j] * v_j). -/
def Mat4.apply (M : Mat4) (v : Fin 4 → Float) : Fin 4 → Float :=
  fun i => M.m ⟨i.val, by omega⟩ * v 0 +
            M.m ⟨i.val + 4, by omega⟩ * v 1 +
            M.m ⟨i.val + 8, by omega⟩ * v 2 +
            M.m ⟨i.val + 12, by omega⟩ * v 3

/-- Identity matrix. -/
def Mat4.identity : Mat4 := ⟨fun idx => if idx.val % 5 = 0 then 1.0 else 0.0⟩

-- Identity property is stated as a goal for a later slice; Float arithmetic
-- requires explicit simplification lemmas not yet available.

end Tocio