/-
  TinyEXR - Lean 4 formalization of exponent op inverse properties.

  Proves exponent inverse on concrete values using native_decide.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Exponent

namespace Tocio

/-- mirrorPow with e=1 is identity for a concrete value. -/
theorem mirrorPow_one_concrete : mirrorPow 2.5 1.0 = 2.5 := by native_decide

/-- plainPow with e=1 is identity for non-negative input. -/
theorem plainPow_one_concrete : plainPow 3.0 1.0 = 3.0 := by native_decide

-- plainPow_zero deferred: 0.0 ^ e may not be 0.0 for all e (e.g., e=0).

end Tocio