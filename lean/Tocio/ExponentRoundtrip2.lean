/-
  TinyEXR - Lean 4 formalization of exponent op inverse properties.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- mirrorPow with e=2 of 2.0 gives 4.0. -/
theorem mirrorPow_2_2 : mirrorPow 2.0 2.0 = 4.0 := by native_decide

/-- mirrorPow with e=0.5 of 4.0 gives 2.0. -/
theorem mirrorPow_4_half2 : mirrorPow 4.0 0.5 = 2.0 := by native_decide

/-- plainPow with e=2 of 3.0 gives 9.0. -/
theorem plainPow_3_2 : plainPow 3.0 2.0 = 9.0 := by native_decide

/-- plainPow with e=0.5 of 9.0 gives 3.0. -/
theorem plainPow_9_half : plainPow 9.0 0.5 = 3.0 := by native_decide

end Tocio