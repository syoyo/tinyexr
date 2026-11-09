/-
  TinyEXR - Lean 4 formalization of matrix identity on unit vectors.

  Proves that the identity matrix maps e_i to e_i for all i,
  using native_decide on concrete values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- e_0 maps to e_0. -/
theorem mat4_id_e0_0 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨0, by decide⟩ = 1.0 := by native_decide
theorem mat4_id_e0_1 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨1, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e0_2 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨2, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e0_3 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨3, by decide⟩ = 0.0 := by native_decide

/-- e_1 maps to e_1. -/
theorem mat4_id_e1_0 : Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨0, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e1_1 : Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨1, by decide⟩ = 1.0 := by native_decide
theorem mat4_id_e1_2 : Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨2, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e1_3 : Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨3, by decide⟩ = 0.0 := by native_decide

/-- e_2 maps to e_2. -/
theorem mat4_id_e2_0 : Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨0, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e2_1 : Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨1, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e2_2 : Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨2, by decide⟩ = 1.0 := by native_decide
theorem mat4_id_e2_3 : Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨3, by decide⟩ = 0.0 := by native_decide

/-- e_3 maps to e_3. -/
theorem mat4_id_e3_0 : Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨0, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e3_1 : Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨1, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e3_2 : Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨2, by decide⟩ = 0.0 := by native_decide
theorem mat4_id_e3_3 : Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨3, by decide⟩ = 1.0 := by native_decide

end Tocio