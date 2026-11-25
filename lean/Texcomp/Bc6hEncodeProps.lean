/-
   TinyEXR - structural properties of the BC6H encoder wire writer.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncodeImage
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false

/-- Serialize the low 128 bits of a word as sixteen little-endian bytes. -/
def bc6hWordBytes (bits : Nat) : List Nat :=
  (List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF)

theorem bc6hWordBytes_length (bits : Nat) : (bc6hWordBytes bits).length = 16 := by
  simp [bc6hWordBytes]

theorem bc6hByte_lt (bits i : Nat) : (bits >>> (8 * i)) &&& 0xFF < 256 := by
  have h := Nat.and_lt_two_pow (bits >>> (8 * i)) (by decide : (255 : Nat) < 2 ^ 8)
  simpa using h

theorem bc6hWordBytes_lt (bits : Nat) : ∀ b ∈ bc6hWordBytes bits, b < 256 := by
  intro b hb
  rw [bc6hWordBytes, List.mem_map] at hb
  obtain ⟨i, _, rfl⟩ := hb
  exact bc6hByte_lt bits i

/-- Writing an `n`-bit field advances the cursor by exactly `n`. -/
theorem bc6hEncPut_pos (acc : Nat × Nat) (v n : Nat) :
    (bc6hEncPut acc v n).2 = acc.2 + n := rfl

/-- If the accumulated word is bounded by its cursor, appending a field keeps
the word bounded by the advanced cursor. -/
theorem bc6hEncPut_lt {acc : Nat × Nat} {v n : Nat}
    (hacc : acc.1 < 2 ^ acc.2) :
    (bc6hEncPut acc v n).1 < 2 ^ (acc.2 + n) := by
  simp only [bc6hEncPut]
  have hmask : (1 <<< n) - 1 < 2 ^ n := by
    rw [Nat.one_shiftLeft]
    exact Nat.sub_lt (Nat.two_pow_pos n) (by decide)
  have hfield := Nat.and_lt_two_pow v hmask
  have hacc' : acc.1 < 2 ^ (acc.2 + n) :=
    Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right _ _))
  have hshift : ((v &&& ((1 <<< n) - 1)) <<< acc.2) < 2 ^ (acc.2 + n) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    simpa [Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right hfield (Nat.two_pow_pos acc.2)
  exact Nat.or_lt_two_pow hacc' hshift

theorem foldl_bc6hEncPut_pos (xs : List Nat) (value width : Nat → Nat)
    (st : Nat × Nat) :
    (xs.foldl (fun st i => bc6hEncPut st (value i) (width i)) st).2 =
      st.2 + (xs.map width).sum := by
  induction xs generalizing st with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, bc6hEncPut_pos, ih, List.map_cons, List.sum_cons]
      omega

theorem foldl_bc6hEncPut_lt (xs : List Nat) (value width : Nat → Nat)
    (st : Nat × Nat) (hst : st.1 < 2 ^ st.2) :
    (xs.foldl (fun st i => bc6hEncPut st (value i) (width i)) st).1 <
      2 ^ (st.2 + (xs.map width).sum) := by
  induction xs generalizing st with
  | nil => simpa using hst
  | cons x xs ih =>
      rw [List.foldl_cons]
      have hnext := bc6hEncPut_lt (v := value x) (n := width x) hst
      have hb := ih (bc6hEncPut st (value x) (width x)) hnext
      rw [bc6hEncPut_pos] at hb
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc] using hb

theorem bc6hEncTail_width_sum (anchor : Nat) (ha0 : 0 < anchor) (ha16 : anchor < 16) :
    ((List.range 16).map (fun i => if i == 0 || i == anchor then 2 else 3)).sum = 46 := by
  interval_cases anchor <;> decide

theorem bc6hEncTail_eq_fold (acc : Nat × Nat) (bestP anchor : Nat) (bsel : List Nat) :
    bc6hEncTail acc bestP anchor bsel =
      ((List.range 16).foldl (fun st i =>
        bc6hEncPut st (bsel.getD i 0) (if i == 0 || i == anchor then 2 else 3))
        (bc6hEncPut acc bestP 5)).1 := rfl

theorem bc6hEncTail_pos (acc : Nat × Nat) (bestP anchor : Nat) (bsel : List Nat)
    (ha0 : 0 < anchor) (ha16 : anchor < 16) :
    ((List.range 16).foldl (fun st i =>
      bc6hEncPut st (bsel.getD i 0) (if i == 0 || i == anchor then 2 else 3))
      (bc6hEncPut acc bestP 5)).2 = acc.2 + 51 := by
  rw [foldl_bc6hEncPut_pos, bc6hEncPut_pos, bc6hEncTail_width_sum anchor ha0 ha16]

theorem bc6hEncTail_lt (acc : Nat × Nat) (bestP anchor : Nat) (bsel : List Nat)
    (ha0 : 0 < anchor) (ha16 : anchor < 16) (hacc : acc.1 < 2 ^ acc.2) :
    bc6hEncTail acc bestP anchor bsel < 2 ^ (acc.2 + 51) := by
  rw [bc6hEncTail_eq_fold]
  have hfirst := bc6hEncPut_lt (v := bestP) (n := 5) hacc
  have hb := foldl_bc6hEncPut_lt (List.range 16)
    (fun i => bsel.getD i 0)
    (fun i => if i == 0 || i == anchor then 2 else 3)
    (bc6hEncPut acc bestP 5) hfirst
  rw [bc6hEncTail_width_sum anchor ha0 ha16, bc6hEncPut_pos] at hb
  simpa [Nat.add_assoc] using hb

theorem bc6hEncPackOneRegion_length (lo hi sel : List Nat) :
    (bc6hEncPackOneRegion lo hi sel).length = 16 := by
  simp [bc6hEncPackOneRegion]

theorem bc6hEncPackOneRegion_lt (lo hi sel : List Nat) :
    ∀ b ∈ bc6hEncPackOneRegion lo hi sel, b < 256 := by
  intro b hb
  rw [bc6hEncPackOneRegion, List.mem_map] at hb
  obtain ⟨i, _, hi⟩ := hb
  rw [← hi]
  exact bc6hByte_lt _ i

/-- The raw 32-bit two's-complement image of an integer. -/
theorem int32Bits_eq_emod (x : Int) :
    (Int32.ofInt x).toUInt32.toNat = (x.emod 0x100000000).toNat := by
  change (BitVec.ofInt 32 x).toNat = (x % Int.ofNat (2 ^ 32)).toNat
  rw [BitVec.toNat_ofInt]
  congr 1

private theorem two_pow_bits_dvd_2_32 {bits : Nat} (hle : bits ≤ 31) :
    Int.ofNat (2 ^ bits) ∣ Int.ofNat (2 ^ 32) :=
  Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 (by omega : bits ≤ 32))

private theorem two_pow_int_pos (n : Nat) : 0 < Int.ofNat (2 ^ n) :=
  Int.ofNat_lt.mpr (Nat.two_pow_pos n)

private theorem int32LowBits_eq_emod_pow (x : Int) (bits : Nat) (hle : bits ≤ 31) :
    (Int32.ofInt x).toUInt32.toNat &&& (2 ^ bits - 1) =
      (x.emod (Int.ofNat (2 ^ bits))).toNat := by
  rw [int32Bits_eq_emod, Nat.and_two_pow_sub_one_eq_mod]
  change (x.emod (Int.ofNat (2 ^ 32))).toNat % 2 ^ bits =
    (x.emod (Int.ofNat (2 ^ bits))).toNat
  have hinner : (x.emod (Int.ofNat (2 ^ 32))).emod (Int.ofNat (2 ^ bits)) =
      x.emod (Int.ofNat (2 ^ bits)) := by
    change (x % Int.ofNat (2 ^ 32)) % Int.ofNat (2 ^ bits) = x % Int.ofNat (2 ^ bits)
    exact Int.emod_emod_of_dvd x (two_pow_bits_dvd_2_32 hle)
  change (x.emod (Int.ofNat (2 ^ 32))).toNat % (Int.ofNat (2 ^ bits)).toNat =
    (x.emod (Int.ofNat (2 ^ bits))).toNat
  rw [← Int.toNat_emod (x := x.emod (Int.ofNat (2 ^ 32)))
    (y := Int.ofNat (2 ^ bits)) (Int.emod_nonneg x (two_pow_int_pos 32).ne')
    (two_pow_int_pos bits).le]
  change ((x.emod (Int.ofNat (2 ^ 32))).emod (Int.ofNat (2 ^ bits))).toNat =
    (x.emod (Int.ofNat (2 ^ bits))).toNat
  rw [hinner]

/-- Clamp to the mathematical N-bit signed range before taking its low bits. -/
def bc6hClampSignedN (v : Int) (bits : Nat) : Int :=
  let half := Int.ofNat (1 <<< (bits - 1))
  if v < -half then -half else if v > half - 1 then half - 1 else v

theorem bc6hClampSignedN_bounds (v : Int) (bits : Nat) (hb : 0 < bits) :
    -Int.ofNat (2 ^ bits) ≤ bc6hClampSignedN v bits ∧
      bc6hClampSignedN v bits < Int.ofNat (2 ^ bits) := by
  have hH0 : 0 ≤ Int.ofNat (2 ^ (bits - 1)) :=
    Int.ofNat_le.mpr (Nat.zero_le _)
  have hBpos : 0 < Int.ofNat (2 ^ bits) := two_pow_int_pos bits
  have hHB : Int.ofNat (2 ^ (bits - 1)) ≤ Int.ofNat (2 ^ bits) :=
    Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bits - 1 ≤ bits))
  simp only [bc6hClampSignedN, Nat.one_shiftLeft]
  split
  · constructor <;> omega
  · split <;> constructor <;> omega

theorem bc6hPackSignedN_eq_emod (v : Int) (bits : Nat) (hb : 0 < bits) (hle : bits ≤ 31) :
    bc6hPackSignedN v bits = ((bc6hClampSignedN v bits).emod (Int.ofNat (2 ^ bits))).toNat := by
  unfold bc6hPackSignedN bc6hClampSignedN
  dsimp only
  simp only [Nat.one_shiftLeft]
  split
  · exact int32LowBits_eq_emod_pow _ bits hle
  · split
    · exact int32LowBits_eq_emod_pow _ bits hle
    · exact int32LowBits_eq_emod_pow _ bits hle

theorem bc6hPackSignedN_lt (v : Int) (bits : Nat) (hb : 0 < bits) (hle : bits ≤ 31) :
    bc6hPackSignedN v bits < 2 ^ bits := by
  rw [bc6hPackSignedN_eq_emod v bits hb hle]
  exact (Int.toNat_lt_toNat (two_pow_int_pos bits)).2
    (Int.emod_lt_of_pos _ (two_pow_int_pos bits))

theorem bc6hPackSignedN_nonneg (v : Int) (bits : Nat) (hb : 0 < bits) (hle : bits ≤ 31)
    (hv0 : 0 ≤ v) (hv1 : v < Int.ofNat (1 <<< (bits - 1))) :
    bc6hPackSignedN v bits = v.toNat := by
  rw [bc6hPackSignedN_eq_emod v bits hb hle]
  have hc : bc6hClampSignedN v bits = v := by
    unfold bc6hClampSignedN
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hc]
  change (v % Int.ofNat (2 ^ bits)).toNat = v.toNat
  have hHB : Int.ofNat (2 ^ (bits - 1)) ≤ Int.ofNat (2 ^ bits) :=
    Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bits - 1 ≤ bits))
  rw [Int.emod_eq_of_lt hv0 (Int.lt_of_lt_of_le
    (by simpa only [Nat.one_shiftLeft] using hv1) hHB)]

theorem bc6hPackSignedN_neg (v : Int) (bits : Nat) (hb : 0 < bits) (hle : bits ≤ 31)
    (hv0 : -Int.ofNat (1 <<< (bits - 1)) ≤ v) (hv1 : v < 0) :
    bc6hPackSignedN v bits = (v + (1 <<< bits)).toNat := by
  rw [bc6hPackSignedN_eq_emod v bits hb hle]
  have hc : bc6hClampSignedN v bits = v := by
    unfold bc6hClampSignedN
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hv0' : -Int.ofNat (2 ^ (bits - 1)) ≤ v := by
    simpa only [Nat.one_shiftLeft] using hv0
  have hHB : Int.ofNat (2 ^ (bits - 1)) ≤ Int.ofNat (2 ^ bits) :=
    Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bits - 1 ≤ bits))
  have hsum0 : 0 ≤ v + Int.ofNat (2 ^ bits) := by omega
  have hsumlt : v + Int.ofNat (2 ^ bits) < Int.ofNat (2 ^ bits) := by omega
  have hm : v.emod (Int.ofNat (2 ^ bits)) = v + Int.ofNat (2 ^ bits) := by
    change v % Int.ofNat (2 ^ bits) = v + Int.ofNat (2 ^ bits)
    rw [Int.emod_eq_iff (two_pow_int_pos bits).ne']
    refine ⟨hsum0, ?_, ?_⟩
    · simpa [Int.natAbs_of_nonneg (two_pow_int_pos bits).le] using hsumlt
    · simp
  rw [hc, hm]
  simp only [Nat.one_shiftLeft, Int.ofNat_eq_natCast]

theorem bc6hPackSigned10_eq (q : Int) :
    bc6hPackSigned10 q = bc6hPackSignedN q 10 := by
  simp [bc6hPackSigned10, bc6hPackSignedN]

theorem bc6hPackSigned10_lt (q : Int) : bc6hPackSigned10 q < 1024 := by
  rw [bc6hPackSigned10_eq]
  simpa using bc6hPackSignedN_lt q 10 (by decide) (by decide)

/-- A candidate step never increases the accumulated reconstruction error. -/
theorem bc6hTryCandidate_error_le (st : Nat × List Nat) (c : Option (List Nat × Nat)) :
    (bc6hTryCandidate st c).1 ≤ st.1 := by
  cases c with
  | none => simp [bc6hTryCandidate]
  | some p =>
      rcases p with ⟨b, e⟩
      simp only [bc6hTryCandidate]
      split <;> omega

theorem bc6hTryGuarded_error_le (st : Nat × List Nat) (c : Option (List Nat × Nat)) :
    (bc6hTryGuarded st c).1 ≤ st.1 := by
  unfold bc6hTryGuarded
  split
  · exact bc6hTryCandidate_error_le st c
  · exact Nat.le_refl _

theorem foldl_bc6hTryGuarded_error_le (cs : List (Option (List Nat × Nat)))
    (st : Nat × List Nat) :
    (cs.foldl bc6hTryGuarded st).1 ≤ st.1 := by
  induction cs generalizing st with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
      exact Nat.le_trans (ih (bc6hTryGuarded st c)) (bc6hTryGuarded_error_le st c)

/-- Generic foldr-append length for a fixed block size. -/
theorem bc6h_map_foldr_append_length {α : Type} (l : List α) (f : α → List Nat) (c : Nat)
    (hf : ∀ x ∈ l, (f x).length = c) :
    ((l.map f).foldr (· ++ ·) []).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have hxs := ih (fun y hy => hf y (by simp [hy]))
      simp only [List.map_cons, List.foldr_cons, List.length_append, hx, hxs,
        List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem bc6h_range_foldr_append_length (n c : Nat) (f : Nat → List Nat)
    (hf : ∀ k, (f k).length = c) :
    ((List.range n).foldr (fun k acc => f k ++ acc) []).length = n * c := by
  rw [← List.foldr_map]
  change (((List.range n).map f).foldr (fun a acc => a ++ acc) []).length = n * c
  rw [bc6h_map_foldr_append_length (List.range n) f c (fun k _ => hf k),
    List.length_range]

/-- Every 4x4 gather produces exactly sixteen RGB texels. -/
theorem bc6hGather_length (src : List UInt32) (w h bx bi : Nat) :
    (bc6hGather src w h bx bi).length = 16 := by
  simp [bc6hGather]

/-- Successful image compression emits exactly the advertised block-grid byte
count, assuming each selected block encoder returns sixteen bytes. -/
theorem bc6hCompressImage_length (src : List UInt32) (w h : Nat) (sf : Bool)
    (out : List Nat)
    (hblk : ∀ pix : List (List UInt32),
      (if sf then bc6hEncodeBlockSf16 pix else bc6hEncodeBlockUf16 pix).length = 16)
    (hout : bc6hCompressImage src w h sf = some out) :
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
        (fun bi => hblk (bc6hGather src w h bx bi))
      simpa [bc6hCompressedSize2, bx, Nat.mul_assoc] using hlen

end Texcomp
