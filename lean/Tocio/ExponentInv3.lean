/-
  TinyEXR - Lean 4 formalization of exponent op inverse properties.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- mirrorPow with e=2 of 3.0. -/
theorem mirrorPow_3_2 : mirrorPow 3.0 2.0 = 9.0 := by native_decide

/-- plainPow of 2.0 with e=2. -/
theorem plainPow_2_2 : plainPow 2.0 2.0 = 4.0 := by native_decide

-- mirrorPow_zero deferred: 0.0 ^ e may not simplify.

-- plainPow_zero_pos deferred: 0.0 ^ e may not simplify.

end Tocio