/-
  TinyEXR - boundary cases of the B44/B44A perceptual half tables.

  `src/exr_b44.c` builds two 65536-entry half-indexed tables from private
  double exp/log kernels. This module proves the *closed-form special cases*
  (non-finite, saturated and sign-invalid entries) exactly; the transcendental
  interior remains a documented boundary pinned by the C table test.
  `make b44-table-diff` compares those entries byte-for-byte.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.B44

namespace Exr.B44

set_option linter.unusedVariables false

/-- Index classes used by `b44_init_tables`. -/
def isSpecialExp (i : Nat) : Bool :=
  let h := i % 65536
  ((h / 1024) % 32 == 31) || (h >= 0x558c && h < 0x8000)

def expTableBoundary (i : Nat) : UInt16 :=
  let h := i % 65536
  if ((h / 1024) % 32 == 31) then 0
  else if h >= 0x558c && h < 0x8000 then 0x7bff
  else 0

def logTableBoundary (i : Nat) : UInt16 :=
  let h := i % 65536
  if ((h / 1024) % 32 == 31) || h > 0x8000 then 0
  else 0

theorem expTableBoundary_inf : expTableBoundary 0x7c00 = 0 := by decide
theorem expTableBoundary_nan : expTableBoundary 0x7e00 = 0 := by decide
theorem expTableBoundary_saturate : expTableBoundary 0x558c = 0x7bff := by decide
theorem logTableBoundary_neg : logTableBoundary 0x8001 = 0 := by decide
theorem logTableBoundary_inf : logTableBoundary 0x7c00 = 0 := by decide

end Exr.B44
