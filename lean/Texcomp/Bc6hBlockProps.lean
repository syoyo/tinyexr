/-
  TinyEXR - every BC6H mode candidate and both per-block encoders emit
  exactly sixteen bytes.

  Each mode encoder returns `none` or `some (bytes, err)`, and every `some`
  branch ends in a little-endian byte map over `List.range 16`. This module
  proves that shape once per mode (using `dsimp only` to expose the outer
  `match`/`if` without unfolding the encoding math), then shows that the
  per-block mode selection fold preserves the sixteen-byte invariant.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncodeProps
import Texcomp.Bc6hEncodeBlock
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- A candidate is good when it fails, or its output is sixteen bytes whose
entries are all byte-valued. -/
def Bc6hGoodCand (c : Option (List Nat × Nat)) : Prop :=
  match c with
  | none => True
  | some (b, _) => b.length = 16 ∧ ∀ x ∈ b, x < 256

@[simp] theorem bc6hByteExpr_lt (bits i : Nat) :
    (bits >>> (8 * i)) &&& 0xFF < 256 := bc6hByte_lt bits i

@[simp] theorem bc6hMap16_lt (bits : Nat) :
    ∀ x ∈ (List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), x < 256 := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact bc6hByte_lt _ i

/-! ## Unsigned modes -/

theorem bc6hEncMode0Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode0Uf16 pix) := by
  unfold bc6hEncMode0Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode1Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode1Uf16 pix) := by
  unfold bc6hEncMode1Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode2Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode2Uf16 pix) := by
  unfold bc6hEncMode2Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode3Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode3Uf16 pix) := by
  unfold bc6hEncMode3Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode4Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode4Uf16 pix) := by
  unfold bc6hEncMode4Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode5Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode5Uf16 pix) := by
  unfold bc6hEncMode5Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode6Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode6Uf16 pix) := by
  unfold bc6hEncMode6Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode7Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode7Uf16 pix) := by
  unfold bc6hEncMode7Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode8Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode8Uf16 pix) := by
  unfold bc6hEncMode8Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode9Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode9Uf16 pix) := by
  unfold bc6hEncMode9Uf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode10Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode10Uf16 pix) := by
  unfold bc6hEncMode10Uf16; dsimp only; simp [Bc6hGoodCand]

/- Modes 12/13 gate on a signed-delta range check. Generalising the
   one-region prelude keeps the outer `if` exposed without inlining the
   refinement math. -/

theorem bc6hEncMode12Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode12Uf16 pix) := by
  unfold bc6hEncMode12Uf16
  generalize hqr : bc6hEncOneRegion 12 4095 pix = qr
  dsimp
  split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode13Uf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode13Uf16 pix) := by
  unfold bc6hEncMode13Uf16
  generalize hqr : bc6hEncOneRegion 16 65535 pix = qr
  dsimp
  split <;> simp [Bc6hGoodCand]

/-! ## Signed modes -/

theorem bc6hEncMode0Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode0Sf16 pix) := by
  unfold bc6hEncMode0Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode1Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode1Sf16 pix) := by
  unfold bc6hEncMode1Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode2Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode2Sf16 pix) := by
  unfold bc6hEncMode2Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode3Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode3Sf16 pix) := by
  unfold bc6hEncMode3Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode4Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode4Sf16 pix) := by
  unfold bc6hEncMode4Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode5Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode5Sf16 pix) := by
  unfold bc6hEncMode5Sf16; dsimp only; split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode9Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode9Sf16 pix) := by
  unfold bc6hEncMode9Sf16; dsimp only; split <;> simp [Bc6hGoodCand]

theorem bc6hEncMode12Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode12Sf16 pix) := by
  unfold bc6hEncMode12Sf16
  generalize hqr : bc6hEncOneRegionS 12 2048 pix = qr
  dsimp
  split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode13Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode13Sf16 pix) := by
  unfold bc6hEncMode13Sf16
  generalize hqr : bc6hEncOneRegionS 16 32768 pix = qr
  dsimp
  split <;> simp [Bc6hGoodCand]

theorem bc6hEncMode6Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode6Sf16 pix) := by
  unfold bc6hEncMode6Sf16 bc6hEncMode678Sf16
  dsimp only
  split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode7Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode7Sf16 pix) := by
  unfold bc6hEncMode7Sf16 bc6hEncMode678Sf16
  dsimp only
  split <;> simp [Bc6hGoodCand]
theorem bc6hEncMode8Sf16_good (pix : List (List UInt32)) :
    Bc6hGoodCand (bc6hEncMode8Sf16 pix) := by
  unfold bc6hEncMode8Sf16 bc6hEncMode678Sf16
  dsimp only
  split <;> simp [Bc6hGoodCand]

attribute [simp]
  bc6hEncMode0Uf16_good bc6hEncMode1Uf16_good bc6hEncMode2Uf16_good
  bc6hEncMode3Uf16_good bc6hEncMode4Uf16_good bc6hEncMode5Uf16_good
  bc6hEncMode6Uf16_good bc6hEncMode7Uf16_good bc6hEncMode8Uf16_good
  bc6hEncMode9Uf16_good bc6hEncMode10Uf16_good
  bc6hEncMode12Uf16_good bc6hEncMode13Uf16_good
  bc6hEncMode0Sf16_good bc6hEncMode1Sf16_good bc6hEncMode2Sf16_good
  bc6hEncMode3Sf16_good bc6hEncMode4Sf16_good bc6hEncMode5Sf16_good
  bc6hEncMode6Sf16_good bc6hEncMode7Sf16_good bc6hEncMode8Sf16_good
  bc6hEncMode9Sf16_good
  bc6hEncMode12Sf16_good bc6hEncMode13Sf16_good

/-! ## The selection fold preserves sixteen-byte outputs -/

theorem bc6hTryCandidate_good (st : Nat × List Nat) (c : Option (List Nat × Nat))
    (hst : st.2.length = 16) (hc : Bc6hGoodCand c) :
    (bc6hTryCandidate st c).2.length = 16 := by
  cases c with
  | none => simp [bc6hTryCandidate, hst]
  | some p =>
      rcases p with ⟨b, e⟩
      simp only [Bc6hGoodCand] at hc
      simp only [bc6hTryCandidate]
      split <;> simp_all

theorem bc6hTryGuarded_good (st : Nat × List Nat) (c : Option (List Nat × Nat))
    (hst : st.2.length = 16) (hc : Bc6hGoodCand c) :
    (bc6hTryGuarded st c).2.length = 16 := by
  unfold bc6hTryGuarded
  split
  · exact bc6hTryCandidate_good st c hst hc
  · exact hst

theorem foldl_bc6hTryGuarded_good (cs : List (Option (List Nat × Nat)))
    (st : Nat × List Nat) (hst : st.2.length = 16)
    (hcs : ∀ c ∈ cs, Bc6hGoodCand c) :
    (cs.foldl bc6hTryGuarded st).2.length = 16 := by
  induction cs generalizing st with
  | nil => exact hst
  | cons c cs ih =>
      exact ih (bc6hTryGuarded st c)
        (bc6hTryGuarded_good st c hst (hcs c (by simp)))
        (fun y hy => hcs y (by simp [hy]))

theorem bc6hEncodeBlockUf16_length (pix : List (List UInt32)) :
    (bc6hEncodeBlockUf16 pix).length = 16 := by
  unfold bc6hEncodeBlockUf16
  dsimp only
  apply foldl_bc6hTryGuarded_good
  · exact bc6hEncPackOneRegion_length _ _ _
  · simp

theorem bc6hEncodeBlockSf16_length (pix : List (List UInt32)) :
    (bc6hEncodeBlockSf16 pix).length = 16 := by
  unfold bc6hEncodeBlockSf16
  dsimp only
  apply foldl_bc6hTryGuarded_good
  · simp [bc6hTryCandidate_good, bc6hEncPackOneRegion_length]
  · simp

/-- Successful image compression emits exactly the advertised block-grid byte
count. Unlike `bc6hCompressImage_length`, this needs no per-block hypothesis:
the two block encoders are proved to emit sixteen bytes for every block. -/
theorem bc6hCompressImage_length_uncond (src : List UInt32) (w h : Nat) (sf : Bool)
    (out : List Nat) (hout : bc6hCompressImage src w h sf = some out) :
    out.length = bc6hCompressedSize2 w h := by
  unfold bc6hCompressImage at hout
  by_cases hz : w == 0 || h == 0
  · simp [hz] at hout
  · by_cases hs : src.length < w * h * 3
    · simp [hz, hs] at hout
    · simp [hz, hs, Option.some.injEq] at hout
      subst out
      let bx := (w + 3) / 4
      have hlen := bc6h_range_foldr_append_length
        (((w + 3) / 4) * ((h + 3) / 4)) 16
        (fun bi => (if sf then bc6hEncodeBlockSf16 (bc6hGather src w h bx bi)
                     else bc6hEncodeBlockUf16 (bc6hGather src w h bx bi)))
        (fun bi => by
          by_cases hsf : sf
          · simp [hsf, bc6hEncodeBlockSf16_length]
          · simp [hsf, bc6hEncodeBlockUf16_length])
      simpa [bc6hCompressedSize2, bx, Nat.mul_assoc] using hlen

end Texcomp
