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

end Texcomp
