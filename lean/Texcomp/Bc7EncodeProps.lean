/-
   TinyEXR - structural properties of the BC7 encoder pack path.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Encode
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false

theorem bc7SetBits_pos (acc bitpos val nbits : Nat) :
    (bc7SetBits acc bitpos val nbits).2 = bitpos + nbits := rfl

theorem bc7SetBits_lt {acc bitpos val nbits : Nat} (hacc : acc < 2 ^ bitpos) :
    (bc7SetBits acc bitpos val nbits).1 < 2 ^ (bitpos + nbits) := by
  simp only [bc7SetBits]
  have hmask : (1 <<< nbits) - 1 < 2 ^ nbits := by
    rw [Nat.one_shiftLeft]
    exact Nat.sub_lt (Nat.two_pow_pos nbits) (by decide)
  have hfield := Nat.and_lt_two_pow val hmask
  have hacc' : acc < 2 ^ (bitpos + nbits) :=
    Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right _ _))
  have hshift : ((val &&& ((1 <<< nbits) - 1)) <<< bitpos) < 2 ^ (bitpos + nbits) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    simpa [Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right hfield (Nat.two_pow_pos bitpos)
  exact Nat.or_lt_two_pow hacc' hshift

theorem bc7PackByte_lt (bits i : Nat) : (bits >>> (8 * i)) &&& 0xFF < 256 := by
  have h := Nat.and_lt_two_pow (bits >>> (8 * i)) (by decide : (255 : Nat) < 2 ^ 8)
  simpa using h

theorem bc7PackCandidate_length (c : Bc7Candidate) :
    (bc7PackCandidate c).length = 16 := by
  simp [bc7PackCandidate]

theorem bc7PackCandidate_lt (c : Bc7Candidate) :
    ∀ b ∈ bc7PackCandidate c, b < 256 := by
  intro b hb
  rw [bc7PackCandidate, List.mem_map] at hb
  obtain ⟨i, _, hi⟩ := hb
  rw [← hi]
  exact bc7PackByte_lt _ i

theorem bc7Weights2_sym (s : Fin 4) :
    bc7Weights2[s.val]! = 64 - bc7Weights2[3 - s.val]! := by decide +revert

theorem bc7Weights3_sym (s : Fin 8) :
    bc7Weights3[s.val]! = 64 - bc7Weights3[7 - s.val]! := by decide +revert

theorem bc7Weights4_sym (s : Fin 16) :
    bc7Weights4[s.val]! = 64 - bc7Weights4[15 - s.val]! := by decide +revert

/-- Reversing the interpolation weight and swapping the endpoint pair leaves
the reconstructed 8-bit channel unchanged. -/
theorem bc7ReconLerp_swap (a b w : Nat) (hw : w ≤ 64) :
    (((64 - (64 - w)) * b + (64 - w) * a + 32) >>> 6) &&& 0xFF =
      (((64 - w) * a + w * b + 32) >>> 6) &&& 0xFF := by
  have hw' : 64 - (64 - w) = w := Nat.sub_sub_self hw
  rw [hw', Nat.add_comm (w * b) ((64 - w) * a)]

/-- Reversal symmetry for every supported palette width (2/3/4 bits). -/
theorem bc7WeightsForBits_sym (bits s : Nat) (hb0 : 2 ≤ bits) (hb1 : bits ≤ 4)
    (hs : s < 2 ^ bits) :
    (bc7WeightsForBits bits).getD (2 ^ bits - 1 - s) 0 =
      64 - (bc7WeightsForBits bits).getD s 0 := by
  interval_cases bits <;> interval_cases s <;> decide

/-- Reconstructed colour/alpha always has four channels. -/
theorem bc7ReconColor_length (c : Bc7Candidate) (subset sel asel : Nat) :
    (bc7ReconColor c subset sel asel).length = 4 := by
  unfold bc7ReconColor
  split <;> simp

theorem bc7ByteAnd_lt (x : Nat) : x &&& 0xFF < 256 := by
  have h := Nat.and_lt_two_pow (x := x) (y := 255) (n := 8) (by norm_num)
  simpa using h

/-- Every quantised BC7 endpoint is an 8-bit value. -/
theorem bc7Unquant_lt (q bits : Nat) : bc7Unquant q bits < 256 := by
  unfold bc7Unquant
  split <;> exact bc7ByteAnd_lt _

/-- Decoded endpoint (with or without a p-bit) is an 8-bit value. -/
theorem bc7DecodeEndpoint_lt (q p precision hasPbit : Nat) :
    bc7DecodeEndpoint q p precision hasPbit < 256 := by
  unfold bc7DecodeEndpoint
  split <;> exact bc7Unquant_lt _ _

/-- All reconstructed colour/alpha channels are 8-bit values. -/
theorem bc7ReconColor_lt (c : Bc7Candidate) (subset sel asel : Nat) :
    ∀ x ∈ bc7ReconColor c subset sel asel, x < 256 := by
  intro x hx
  unfold bc7ReconColor at hx
  split at hx
  · simp only [List.mem_append, List.mem_singleton, List.mem_map] at hx
    rcases hx with ⟨comp, _, rfl⟩ | rfl
    · exact bc7ByteAnd_lt _
    · norm_num
  · simp only [List.mem_append, List.mem_singleton, List.mem_map] at hx
    rcases hx with ⟨comp, _, rfl⟩ | rfl
    · exact bc7ByteAnd_lt _
    · exact bc7ByteAnd_lt _

/-- The palette has one entry per subset. -/
theorem bc7FillPalette_length (c : Bc7Candidate) :
    (bc7FillPalette c).length = bc7NumSubsets.getD c.mode 1 := by
  simp [bc7FillPalette]

/-- Every per-subset palette has the mode's common selector count. -/
theorem bc7FillPalette_entry_length (c : Bc7Candidate) (p : List (List Nat))
    (hp : p ∈ bc7FillPalette c) :
    p.length =
      max (1 <<< (bc7ColorIndexBits.getD c.mode 0 + c.indexSelector))
        (if bc7AlphaIndexBits.getD c.mode 0 > c.indexSelector then
          1 <<< (bc7AlphaIndexBits.getD c.mode 0 - c.indexSelector)
         else 1 <<< (bc7ColorIndexBits.getD c.mode 0 + c.indexSelector)) := by
  rw [bc7FillPalette, List.mem_map] at hp
  obtain ⟨subset, _, rfl⟩ := hp
  simp

end Texcomp
