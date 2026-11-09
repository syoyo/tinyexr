/-
  TinyEXR - Lean 4 formalization of exponent op round-trip.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- mirrorPow with e=3 of 2.0 gives 8.0. -/
theorem mirrorPow_2_3 : mirrorPow 2.0 3.0 = 8.0 := by native_decide

/-- mirrorPow with e=0.5 of 9.0 gives 3.0. -/
theorem mirrorPow_9_half2 : mirrorPow 9.0 0.5 = 3.0 := by native_decide

/-- plainPow with e=3 of 2.0 gives 8.0. -/
theorem plainPow_2_3 : plainPow 2.0 3.0 = 8.0 := by native_decide

/-- plainPow with e=0.5 of 4.0 gives 2.0. -/
theorem plainPow_4_half2 : plainPow 4.0 0.5 = 2.0 := by native_decide

end Tocio