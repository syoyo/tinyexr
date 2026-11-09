/-
  TinyEXR - Lean 4 formalization of matrix structural properties.

  Proves specific element values of the identity matrix.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity matrix (0,0) = 1.0. -/
theorem mat4_id_00 : (Mat4.identity.m ⟨0, by decide⟩) = 1.0 := by native_decide

/-- Identity matrix (1,1) = 1.0. -/
theorem mat4_id_11 : (Mat4.identity.m ⟨5, by decide⟩) = 1.0 := by native_decide

/-- Identity matrix (2,2) = 1.0. -/
theorem mat4_id_22 : (Mat4.identity.m ⟨10, by decide⟩) = 1.0 := by native_decide

/-- Identity matrix (3,3) = 1.0. -/
theorem mat4_id_33 : (Mat4.identity.m ⟨15, by decide⟩) = 1.0 := by native_decide

/-- Identity matrix (0,1) = 0.0. -/
theorem mat4_id_01 : (Mat4.identity.m ⟨4, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (1,0) = 0.0. -/
theorem mat4_id_10 : (Mat4.identity.m ⟨1, by decide⟩) = 0.0 := by native_decide

end Tocio