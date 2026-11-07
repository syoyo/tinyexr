/-
  TinyEXR - exact dyadic mass behind descending PIZ canonical assignment.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizCodebookTotal
import Exr.PizLengthTable

namespace Exr.Piz.Canonical

def deeper : List Nat → Nat → Nat
  | [],_ => 0
  | depth::rest,cutoff => (if cutoff < depth then 2^(58-depth) else 0)+deeper rest cutoff

def shallower : List Nat → Nat → Nat
  | [],_ => 0
  | depth::rest,cutoff =>
    (if depth = 0 then 0 else if depth ≤ cutoff then 2^(58-depth) else 0)+shallower rest cutoff

def Complete (lengths : List Nat) : Prop :=
  (∀ depth ∈ lengths, depth ≤ 58) ∧ Frequency.tableMass 58 lengths = 2^58

theorem mass_split (lengths : List Nat) (cutoff : Nat) :
    Frequency.tableMass 58 lengths = deeper lengths cutoff+shallower lengths cutoff := by
  rw [Frequency.tableMass_eq_sum]
  induction lengths with
  | nil => rfl
  | cons depth rest ih =>
    simp only [List.map_cons,List.sum_cons,deeper,shallower]
    by_cases hz : depth = 0
    · subst depth
      simp only [ite_true, Nat.not_lt_zero,ite_false,Nat.zero_add] at *
      exact ih
    · by_cases hc : depth ≤ cutoff
      · have hnot : ¬cutoff < depth := by omega
        simp only [hz,ite_false,hc,ite_true,hnot]
        omega
      · have hlt : cutoff < depth := by omega
        simp only [hz,ite_false,hc,hlt,ite_true,Nat.zero_add]
        omega

theorem shallower_divisible (lengths : List Nat) (cutoff : Nat) (hc : cutoff ≤ 58) :
    2^(58-cutoff) ∣ shallower lengths cutoff := by
  induction lengths with
  | nil => exact Nat.dvd_zero _
  | cons depth rest ih =>
    unfold shallower
    apply Nat.dvd_add ?_ ih
    by_cases hz : depth = 0
    · rw [ite_eq_left hz]
      exact Nat.dvd_zero _
    · rw [ite_eq_right hz]
      by_cases hd : depth ≤ cutoff
      · rw [ite_eq_left hd,show 58-depth = (58-cutoff)+(cutoff-depth) by omega,Nat.pow_add]
        exact Nat.dvd_mul_right _ _
      · rw [ite_eq_right hd]
        exact Nat.dvd_zero _

theorem deeper_divisible (lengths : List Nat) (hcomplete : Complete lengths)
    (cutoff : Nat) (hc : cutoff ≤ 58) : 2^(58-cutoff) ∣ deeper lengths cutoff := by
  have hs := shallower_divisible lengths cutoff hc
  have ht : 2^(58-cutoff) ∣ 2^58 := by
    conv_rhs => rw [show 58 = (58-cutoff)+cutoff from by omega,Nat.pow_add]
    exact Nat.dvd_mul_right _ _
  rw [← hcomplete.2,mass_split lengths cutoff] at ht
  exact (Nat.dvd_add_iff_left hs).mpr ht

theorem deeper_top (lengths : List Nat) (hc : ∀ depth ∈ lengths, depth ≤ 58) : deeper lengths 58 = 0 := by
  induction lengths with
  | nil => rfl
  | cons depth rest ih =>
    have hd := hc depth List.mem_cons_self
    rw [deeper,ite_eq_right (by omega),Nat.zero_add]
    exact ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))

theorem lengthCount_cons (depth : Nat) (rest : List Nat) (cutoff : Nat) :
    lengthCount (depth::rest) cutoff = (if depth = cutoff then 1 else 0)+lengthCount rest cutoff := by
  by_cases he : depth = cutoff <;> simp [lengthCount,he,Nat.add_comm]

/-- Crossing one depth adds precisely that depth's dyadic block allocation. -/
theorem deeper_step (lengths : List Nat) (depth : Nat) (hd : 0 < depth) :
    deeper lengths (depth-1) = deeper lengths depth+lengthCount lengths depth*2^(58-depth) := by
  induction lengths with
  | nil => simp [deeper,lengthCount]
  | cons value rest ih =>
    simp only [deeper,lengthCount_cons]
    rw [ih]
    by_cases he : value = depth
    · subst value
      have hlt : depth-1 < depth := by omega
      simp only [hlt,ite_true,Nat.lt_irrefl,ite_false,Nat.zero_add,
        Nat.add_mul,Nat.one_mul]
      omega
    · have hiff : (depth-1 < value) = (depth < value) := propext (by omega)
      simp only [hiff,he,ite_false,Nat.zero_add]
      omega

/-- Descending canonical starts are exact occupied dyadic mass, not rounded
approximations. Completeness supplies divisibility at every depth. -/
theorem codeStart_mass (lengths : List Nat) (hc : Complete lengths) (k : Nat) (hk : k < 58) :
    codeStart lengths k*2^k = deeper lengths (58-k) := by
  induction k with
  | zero => simp only [codeStart,Nat.zero_mul,Nat.sub_zero,deeper_top lengths hc.1]
  | succ k ih =>
    have hk' : k < 58 := by omega
    have hdepth : 0 < 58-k := by omega
    have hcut : 58-(k+1) = (58-k)-1 := by omega
    have hstep : deeper lengths (58-(k+1)) =
        (codeStart lengths k+lengthCount lengths (58-k))*2^k := by
      rw [hcut,deeper_step lengths (58-k) hdepth,← ih hk']
      rw [show 58-(58-k) = k by omega,← Nat.add_mul]
    have hdiv : 2^(k+1) ∣ deeper lengths (58-(k+1)) := by
      have hh := deeper_divisible lengths hc (58-(k+1)) (by omega)
      simpa only [Nat.sub_sub_self (by omega : k+1 ≤ 58)] using hh
    have hquot : deeper lengths (58-(k+1))/2^(k+1) =
        (codeStart lengths k+lengthCount lengths (58-k))/2 := by
      rw [hstep,Nat.pow_succ]
      simpa only [Nat.mul_comm (2^k) 2] using
        Nat.mul_div_mul_right (codeStart lengths k+lengthCount lengths (58-k)) 2 (Nat.two_pow_pos k)
    rw [codeStart,← hquot]
    exact Nat.div_mul_cancel hdiv

end Exr.Piz.Canonical
