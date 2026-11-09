/-
  TinyEXR - Lean 4 formalization of exponent op round-trip.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- plainPow and its inverse round-trip for e=2, x=4.0. -/
theorem exponent_roundtrip_2_4 : plainPow (plainPow 4.0 0.5) 2.0 = 4.0 := by native_decide

/-- mirrorPow with e=2 of 3.0 gives 9.0. -/
theorem mirrorPow_3_2_check : mirrorPow 3.0 2.0 = 9.0 := by native_decide

/-- mirrorPow with e=0.5 of 4.0 gives 2.0. -/
theorem mirrorPow_4_half : mirrorPow 4.0 0.5 = 2.0 := by native_decide

end Tocio