/-
  TinyEXR - Lean 4 formalization of matrix identity on basis vectors.

  Proves that the identity matrix maps basis vectors correctly,
  using native_decide on concrete values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity maps basis vector 0 (output component 0) to 1.0. -/
theorem mat4_id_basis0_0 :
    Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨0, by decide⟩ = 1.0 := by
  native_decide

/-- Identity maps basis vector 0 (output component 1) to 0.0. -/
theorem mat4_id_basis0_1 :
    Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨1, by decide⟩ = 0.0 := by
  native_decide

/-- Identity maps basis vector 1 (output component 1) to 1.0. -/
theorem mat4_id_basis1_1 :
    Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨1, by decide⟩ = 1.0 := by
  native_decide

/-- Identity maps basis vector 2 (output component 2) to 1.0. -/
theorem mat4_id_basis2_2 :
    Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨2, by decide⟩ = 1.0 := by
  native_decide

/-- Identity maps basis vector 3 (output component 3) to 1.0. -/
theorem mat4_id_basis3_3 :
    Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨3, by decide⟩ = 1.0 := by
  native_decide

/-- Identity maps zero vector to zero. -/
theorem mat4_id_zero_0 :
    Mat4.identity.apply (fun _ => 0.0) ⟨0, by decide⟩ = 0.0 := by
  native_decide

end Tocio