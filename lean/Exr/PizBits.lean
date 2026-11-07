/-
  TinyEXR - bounded MSB-first PIZ bit readers and wire-field inverses.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Piz
import Mathlib.Tactic.Ring

namespace Exr.Piz.Bits

/-- Numerical value of an MSB-first bit list. -/
def value : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 2^rest.length else 0) + value rest

theorem value_lt (bits : List Bool) : value bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons b rest ih =>
    have hp := Nat.two_pow_pos rest.length
    cases b <;> simp only [value, Bool.false_eq_true, ite_false, ite_true,
      Nat.zero_add, List.length_cons, Nat.pow_succ] <;> omega

theorem codeBits_length (n v : Nat) : (Huffman.codeBits n v).length = n := by
  simp [Huffman.codeBits]

theorem codeBits_succ (n v : Nat) :
    Huffman.codeBits (n+1) v = (v / 2^n % 2 == 1) :: Huffman.codeBits n v := by
  unfold Huffman.codeBits
  rw [List.range_succ_eq_map, List.map_cons]
  have head : n+1-0-1 = n := by omega
  rw [head]
  apply congrArg (List.cons (v / 2^n % 2 == 1))
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  have he : n+1-(i+1)-1 = n-i-1 := by omega
  exact congrArg (fun e => v / 2^e % 2 == 1) he

/-- Reading an emitted field yields its value modulo its declared width.
No fixed-width machine arithmetic or native-decide oracle is used. -/
theorem value_codeBits (n v : Nat) : value (Huffman.codeBits n v) = v % 2^n := by
  induction n with
  | zero => simp [Huffman.codeBits, value, Nat.mod_one]
  | succ n ih =>
    rw [codeBits_succ, value, codeBits_length, ih, Nat.pow_succ]
    have hm := Nat.mod_add_div (v % (2^n*2)) (2^n)
    rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at hm
    rcases Nat.mod_two_eq_zero_or_one (v / 2^n) with hz | ho
    · simp [hz] at hm ⊢; omega
    · simp [ho] at hm ⊢; omega

/-- A field read either consumes exactly its width or rejects truncation. -/
def read (width : Nat) (bits : List Bool) : Option (Nat × List Bool) :=
  if width ≤ bits.length then some (value (bits.take width), bits.drop width) else none

theorem read_append (field suffix : List Bool) :
    read field.length (field ++ suffix) = some (value field, suffix) := by
  simp [read]

theorem read_codeBits (width v : Nat) (suffix : List Bool) (hv : v < 2^width) :
    read width (Huffman.codeBits width v ++ suffix) = some (v, suffix) := by
  have hr := read_append (Huffman.codeBits width v) suffix
  simpa only [codeBits_length, value_codeBits, Nat.mod_eq_of_lt hv] using hr

theorem read_bounds (width : Nat) (bits : List Bool) (v : Nat) (rest : List Bool)
    (hr : read width bits = some (v,rest)) :
    width ≤ bits.length ∧ rest.length + width = bits.length ∧ v < 2^width := by
  unfold read at hr
  split at hr
  · rename_i hn
    have he := Option.some.inj hr
    have hv := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    change value (bits.take width) = v at hv
    change bits.drop width = rest at ht
    have hb := value_lt (bits.take width)
    rw [List.length_take, Nat.min_eq_left hn] at hb
    rw [hv] at hb
    rw [← ht, List.length_drop]
    exact ⟨hn, by omega, hb⟩
  · simp at hr

/-- MSB-first byte expansion; the field reader is independent of byte alignment. -/
def unpack (bytes : List UInt8) : List Bool :=
  bytes.flatMap (fun b => Huffman.codeBits 8 b.toNat)

theorem unpack_length (bytes : List UInt8) : (unpack bytes).length = 8*bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp [unpack, codeBits_length] at *; omega

theorem value_append (front tail : List Bool) :
    value (front ++ tail) = value front * 2^tail.length + value tail := by
  induction front with
  | nil => simp [value]
  | cons b rest ih =>
    simp only [List.cons_append, value, List.length_append, ih, Nat.pow_add]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

theorem fold_value (bits : List Bool) (seed : Nat) :
    bits.foldl (fun acc b => acc*2 + if b then 1 else 0) seed = seed*2^bits.length + value bits := by
  induction bits generalizing seed with
  | nil => simp [value]
  | cons b rest ih =>
    simp only [List.foldl_cons, ih, List.length_cons, value, Nat.pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

/-- An MSB-first value together with its bit width uniquely determines bits. -/
theorem value_injective (a b : List Bool) (hl : a.length = b.length) (hv : value a = value b) : a = b := by
  induction a generalizing b with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp hl.symm
    exact hb.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      have hlen : xs.length = ys.length := by simpa using hl
      have hx := value_lt xs
      have hy := value_lt ys
      rw [← hlen] at hy
      simp only [value, ← hlen] at hv
      cases x <;> cases y <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add] at hv
      · exact congrArg (false :: ·) (ih ys hlen hv)
      · omega
      · omega
      · have he : value xs = value ys := by omega
        exact congrArg (true :: ·) (ih ys hlen he)

theorem value_zeros (n : Nat) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [value, List.replicate_succ] using ih

/-- The wire byte for a final, possibly short chunk is left-aligned and
padded with zero bits, exactly as the C MSB-first bit writer does. -/
def packByte (bits : List Bool) : UInt8 := UInt8.ofNat (value bits * 2^(8-bits.length))

theorem packByte_bound (bits : List Bool) (hl : bits.length ≤ 8) :
    value bits * 2^(8-bits.length) < 256 := by
  have hm := Nat.mul_lt_mul_of_pos_right (value_lt bits) (Nat.two_pow_pos (8-bits.length))
  rw [← Nat.pow_add, Nat.add_sub_of_le hl] at hm
  exact hm

theorem codeBits_packByte (bits : List Bool) (hl : bits.length ≤ 8) :
    Huffman.codeBits 8 (packByte bits).toNat = bits ++ List.replicate (8-bits.length) false := by
  apply value_injective
  · simp only [codeBits_length, List.length_append, List.length_replicate]
    omega
  · rw [value_codeBits, value_append, value_zeros, Nat.add_zero, List.length_replicate]
    have hb := packByte_bound bits hl
    simp only [packByte, UInt8.toNat_ofNat']
    rw [Nat.mod_eq_of_lt hb]
    exact Nat.mod_eq_of_lt hb

theorem unpack_cons (byte : UInt8) (bytes : List UInt8) :
    unpack (byte :: bytes) = Huffman.codeBits 8 byte.toNat ++ unpack bytes := rfl

theorem packBitsGo_step (b : Bool) (rest : List Bool) (fuel : Nat) :
    Huffman.packBitsGo (fuel+1) (b::rest) =
      packByte ((b::rest).take 8) :: Huffman.packBitsGo fuel ((b::rest).drop 8) := by
  rw [Huffman.packBitsGo, fold_value]
  simp only [Nat.zero_mul, Nat.zero_add]
  rfl
  all_goals simp

/-- Exact byte-packing inverse, including the terminal zero padding. -/
theorem unpack_packBitsGo (bits : List Bool) (fuel : Nat) (hf : bits.length ≤ fuel) :
    unpack (Huffman.packBitsGo fuel bits) =
      bits ++ List.replicate ((8-bits.length%8)%8) false := by
  induction fuel generalizing bits with
  | zero =>
    have hb : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    rfl
  | succ fuel ih =>
    cases bits with
    | nil => rfl
    | cons b rest =>
      rw [packBitsGo_step, unpack_cons]
      rw [codeBits_packByte _ (by simp)]
      have ht : ((b::rest).drop 8).length ≤ fuel := by simp only [List.length_drop, List.length_cons] at *; omega
      rw [ih _ ht]
      by_cases hs : (b::rest).length ≤ 8
      · have hdrop : (b::rest).drop 8 = [] := List.drop_eq_nil_iff.mpr hs
        have htake : (b::rest).take 8 = b::rest := List.take_of_length_le hs
        rw [hdrop, htake]
        have hn : (8-(b::rest).length%8)%8 = 8-(b::rest).length := by
          have hp : 0 < (b::rest).length := by simp
          omega
        rw [hn]
        simp
      · have hlen : ((b::rest).take 8).length = 8 := by simp only [List.length_take]; omega
        have hmod : ((b::rest).drop 8).length % 8 = (b::rest).length % 8 := by
          simp only [List.length_drop]
          omega
        simp only [hlen, Nat.sub_self, List.replicate_zero, List.append_nil, hmod]
        rw [← List.append_assoc, List.take_append_drop]

theorem unpack_packBits (bits : List Bool) :
    unpack (Huffman.packBits bits) = bits ++ List.replicate ((8-bits.length%8)%8) false :=
  unpack_packBitsGo bits bits.length (Nat.le_refl _)

end Exr.Piz.Bits
