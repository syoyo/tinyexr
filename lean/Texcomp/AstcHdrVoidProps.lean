/-
   TinyEXR - ASTC HDR void-extent writer/decoder contract.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcHdrPack
import Texcomp.AstcHdr
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false

theorem hdrWriteVoidExtent_length (r g b a : Nat) :
    (hdrWriteVoidExtent r g b a).length = 16 := by
  simp [hdrWriteVoidExtent]

theorem low8_high8_eq (x : Nat) :
    (x &&& 0xFF) ||| ((x >>> 8) <<< 8) = x := by
  have hlow : x &&& 0xFF = x % 2 ^ 8 := by
    simpa using (Nat.and_two_pow_sub_one_eq_mod x 8)
  rw [hlow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 ^ 8 : Nat) = 256 by decide]
  change x % 256 ||| x / 256 * 256 = x
  have hmod := Nat.mod_lt x (by decide : 0 < 2 ^ 8)
  have hor := Nat.two_pow_add_eq_or_of_lt (b := x % 2 ^ 8) (i := 8)
    (a := x / 2 ^ 8) hmod
  norm_num at hor
  rw [Nat.mul_comm, Nat.or_comm, ← hor]
  simpa [Nat.add_comm] using Nat.mod_add_div x 256

theorem hdrWriteVoidExtent_mode (r g b a : Nat) :
    rdBits (hdrWriteVoidExtent r g b a) 0 11 = 0x7FC := by
  simp [hdrWriteVoidExtent, rdBits, List.range_succ]

theorem astcDecodeBlockHdr_void (bw bh r g b a : Nat)
    (hbw : 0 < bw) (hbh : 0 < bh)
    (hr : r < 2 ^ 16) (hg : g < 2 ^ 16) (hb : b < 2 ^ 16) (ha : a < 2 ^ 16)
    (t : Fin (bw * bh)) :
    astcDecodeBlockHdr (hdrWriteVoidExtent r g b a) bw bh t =
      (halfToFloat r, halfToFloat g, halfToFloat b, halfToFloat a) := by
  unfold astcDecodeBlockHdr
  rw [hdrWriteVoidExtent_mode]
  simp [hdrWriteVoidExtent, low8_high8_eq r, low8_high8_eq g,
    low8_high8_eq b, low8_high8_eq a]

end Texcomp
