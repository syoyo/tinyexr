/-
  TinyEXR - Lean 4 formalization of matrix identity on a concrete vector.

  Proves that the identity matrix maps (1,2,3,4) to (1,2,3,4),
  using native_decide on concrete values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity maps (1,2,3,4) component 0 to 1.0. -/
theorem mat4_id_vec_1234_0 :
    Mat4.identity.apply (fun i => Float.ofNat (i.val + 1)) ⟨0, by decide⟩ = 1.0 := by
  native_decide

/-- Identity maps (1,2,3,4) component 1 to 2.0. -/
theorem mat4_id_vec_1234_1 :
    Mat4.identity.apply (fun i => Float.ofNat (i.val + 1)) ⟨1, by decide⟩ = 2.0 := by
  native_decide

/-- Identity maps (1,2,3,4) component 2 to 3.0. -/
theorem mat4_id_vec_1234_2 :
    Mat4.identity.apply (fun i => Float.ofNat (i.val + 1)) ⟨2, by decide⟩ = 3.0 := by
  native_decide

/-- Identity maps (1,2,3,4) component 3 to 4.0. -/
theorem mat4_id_vec_1234_3 :
    Mat4.identity.apply (fun i => Float.ofNat (i.val + 1)) ⟨3, by decide⟩ = 4.0 := by
  native_decide

end Tocio