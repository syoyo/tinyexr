/-
  TinyEXR - Allocation guards for the tocio CLF LUT readers.

  A successful CLF 1D/3D LUT parse must never hand the kernels a sample
  buffer shorter than the declared dimensions. The readers already call
  `spiValuesFit` before `xfloats` and check the exact count afterwards;
  these lemmas record the two invariants involved: the float scanner never
  over-fills its budget, and a "fits" answer really bounds the count by the
  available characters.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Clf
import Tocio.LoaderBounds

namespace Tocio

set_option linter.unusedVariables false

theorem xfloatSeg_length_le (fuel : Nat) (cs : List Char) (acc : List Float32) (max : Nat)
    (hacc : acc.length ≤ max) : (xfloatSeg fuel cs acc max).1.length ≤ max := by
  induction fuel generalizing cs acc with
  | zero => exact hacc
  | succ n ih =>
      unfold xfloatSeg
      split
      · exact hacc
      · rename_i hne
        cases hr : readF32 cs with
        | none => exact hacc
        | some pv =>
            have hlen : (acc ++ [pv.1]).length ≤ max := by
              simp
              omega
            simpa [hr] using ih (cs := pv.2) (acc := acc ++ [pv.1]) hlen

theorem xfloatsAux_length_le (fuel : Nat) (cs : List Char) (max : Nat) (acc : List Float32)
    (hacc : acc.length ≤ max) : (xfloatsAux fuel cs max acc).1.length ≤ max := by
  induction fuel generalizing cs acc with
  | zero => exact hacc
  | succ n ih =>
      unfold xfloatsAux
      split
      · exact hacc
      · rename_i hne
        by_cases htxt : (xt cs).1 == ""
        · simp [htxt]
          exact hacc
        · have hs := xfloatSeg_length_le n (xt cs).1.toList acc max hacc
          by_cases hdone : !(xfloatSeg n (xt cs).1.toList acc max).2.2 &&
              !((xfloatSeg n (xt cs).1.toList acc max).2.1.dropWhile (fun c => c.val ≤ 32)).isEmpty
          · simp [htxt, hdone]
            exact hs
          · simpa [htxt, hdone] using
              (ih (cs := (xt cs).2) (acc := (xfloatSeg n (xt cs).1.toList acc max).1) hs)

theorem xfloats_length_le (cs : List Char) (max : Nat) :
    (xfloats cs max).1.length ≤ max := by
  unfold xfloats
  apply xfloatsAux_length_le
  simp

/-- `toc_values_fit` soundness for a CLF LUT Array tail: when at least two
  characters remain, the declared value count is bounded by the tail length. -/
theorem clf_values_fit_sound {count avail : Nat} (havail : 2 ≤ avail)
    (h : spiValuesFit count avail = true) : count ≤ avail :=
  spiValuesFit_le havail h

end Tocio
