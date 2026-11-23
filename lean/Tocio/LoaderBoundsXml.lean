/-
  TinyEXR - Safety invariants of the tocio CLF minimal XML reader.

  The C reader is a flat pointer cursor: every loop iteration advances at
  least one byte, tag/attribute names are capped at 63 characters, and the
  cursor never moves past the end of the buffer. These lemmas capture those
  properties for the Lean port in `Tocio.ClfXml`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ClfXml

namespace Tocio

set_option linter.unusedVariables false

theorem dropSp_length_le (cs : List Char) : (dropSp cs).length ≤ cs.length := by
  unfold dropSp
  induction cs with
  | nil => simp
  | cons c cs ih =>
      by_cases h : xsp c
      · simp [List.dropWhile, h]
        omega
      · simp [List.dropWhile, h]

/-- Name scans are suffix-bounded. -/
theorem xnameChar_length_le : ∀ cs : List Char, (xnameChar cs).length ≤ cs.length
  | [] => by simp [xnameChar]
  | c :: cs => by
      unfold xnameChar
      by_cases h : c.val > 32 && c != '>'
      · simp [List.takeWhile, h]
        have ih := xnameChar_length_le cs
        simpa [xnameChar] using ih
      · simp [List.takeWhile, h]

end Tocio
