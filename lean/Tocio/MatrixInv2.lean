/-
  TinyEXR - Lean 4 formalization of matrix identity on basis vectors.

  Proves that the identity matrix maps each basis vector to itself,
  using native_decide on concrete values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Basis vector 0 maps to itself under identity. -/
theorem mat4_identity_basis0 :
    Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) 0 = 1.0 := by
  native_decide

/-- Basis vector 1 maps to itself under identity. -/
theorem mat4_identity_basis1 :
    Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) 1 = 1.0 := by
  native_decide

/-- Basis vector 2 maps to itself under identity. -/
theorem mat4_identity_basis2 :
    Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) 2 = 1.0 := by
  native_decide

/-- Basis vector 3 maps to itself under identity. -/
theorem mat4_identity_basis3 :
    Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) 3 = 1.0 := by
  native_decide

/-- Zero vector maps to zero under identity. -/
theorem mat4_identity_zero_vec :
    Mat4.identity.apply (fun _ => 0.0) 0 = 0.0 := by
  native_decide

end Tocio