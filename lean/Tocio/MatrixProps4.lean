/-
  TinyEXR - Lean 4 formalization of matrix op properties.

  Proves that applying identity matrix to basis vectors preserves them,
  using native_decide on concrete values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Matrix

namespace Tocio

/-- Identity maps (1,0,0,0) component 0 to 1.0. -/
theorem mat4_id_1000_0 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨0, by decide⟩ = 1.0 := by native_decide

/-- Identity maps (1,0,0,0) component 1 to 0.0. -/
theorem mat4_id_1000_1 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨1, by decide⟩ = 0.0 := by native_decide

/-- Identity maps (1,0,0,0) component 2 to 0.0. -/
theorem mat4_id_1000_2 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨2, by decide⟩ = 0.0 := by native_decide

/-- Identity maps (1,0,0,0) component 3 to 0.0. -/
theorem mat4_id_1000_3 : Mat4.identity.apply (fun i => if i.val = 0 then 1.0 else 0.0) ⟨3, by decide⟩ = 0.0 := by native_decide

/-- Identity maps (0,1,0,0) component 1 to 1.0. -/
theorem mat4_id_0100_1 : Mat4.identity.apply (fun i => if i.val = 1 then 1.0 else 0.0) ⟨1, by decide⟩ = 1.0 := by native_decide

/-- Identity maps (0,0,1,0) component 2 to 1.0. -/
theorem mat4_id_0010_2 : Mat4.identity.apply (fun i => if i.val = 2 then 1.0 else 0.0) ⟨2, by decide⟩ = 1.0 := by native_decide

/-- Identity maps (0,0,0,1) component 3 to 1.0. -/
theorem mat4_id_0001_3 : Mat4.identity.apply (fun i => if i.val = 3 then 1.0 else 0.0) ⟨3, by decide⟩ = 1.0 := by native_decide

/-- Identity maps (0,0,0,0) to (0,0,0,0). -/
theorem mat4_id_0000_0 : Mat4.identity.apply (fun _ => 0.0) ⟨0, by decide⟩ = 0.0 := by native_decide

end Tocio