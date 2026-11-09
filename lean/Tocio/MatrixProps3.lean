/-
  TinyEXR - Lean 4 formalization of matrix structural properties (extended).

  Proves additional element values of the identity matrix.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity matrix (0,2) = 0.0. -/
theorem mat4_id_02 : (Mat4.identity.m ⟨2, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (0,3) = 0.0. -/
theorem mat4_id_03 : (Mat4.identity.m ⟨3, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (1,2) = 0.0. -/
theorem mat4_id_12 : (Mat4.identity.m ⟨6, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (1,3) = 0.0. -/
theorem mat4_id_13 : (Mat4.identity.m ⟨7, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (2,0) = 0.0. -/
theorem mat4_id_20 : (Mat4.identity.m ⟨8, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (2,1) = 0.0. -/
theorem mat4_id_21 : (Mat4.identity.m ⟨9, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (2,3) = 0.0. -/
theorem mat4_id_23 : (Mat4.identity.m ⟨11, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (3,0) = 0.0. -/
theorem mat4_id_30 : (Mat4.identity.m ⟨12, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (3,1) = 0.0. -/
theorem mat4_id_31 : (Mat4.identity.m ⟨13, by decide⟩) = 0.0 := by native_decide

/-- Identity matrix (3,2) = 0.0. -/
theorem mat4_id_32 : (Mat4.identity.m ⟨14, by decide⟩) = 0.0 := by native_decide

end Tocio