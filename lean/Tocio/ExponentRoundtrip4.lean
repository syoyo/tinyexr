/-
  TinyEXR - Lean 4 formalization of exponent op round-trip.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- mirrorPow with e=2 of 5.0 gives 25.0. -/
theorem mirrorPow_5_2 : mirrorPow 5.0 2.0 = 25.0 := by native_decide

/-- mirrorPow with e=0.5 of 16.0 gives 4.0. -/
theorem mirrorPow_16_half : mirrorPow 16.0 0.5 = 4.0 := by native_decide

/-- plainPow with e=2 of 5.0 gives 25.0. -/
theorem plainPow_5_2 : plainPow 5.0 2.0 = 25.0 := by native_decide

/-- plainPow with e=0.5 of 16.0 gives 4.0. -/
theorem plainPow_16_half : plainPow 16.0 0.5 = 4.0 := by native_decide

end Tocio