/-
  TinyEXR - executable PIZ source bitmap construction and coverage proofs.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizReconstruct

namespace Exr.Piz.Bitmap

def mark (bitmap : Array UInt8) (word : UInt16) : Array UInt8 :=
  let value := word.toNat
  if value = 0 then bitmap else
    bitmap.set! (value/8) (bitmap[value/8]! ||| (1 <<< UInt8.ofNat (value%8)))

def make (raw : List UInt16) : Array UInt8 := raw.foldl mark (Array.replicate 8192 0)

def Present (bitmap : Array UInt8) (word : UInt16) : Prop :=
  word.toNat = 0 ∨ ((bitmap[word.toNat/8]! >>> UInt8.ofNat (word.toNat%8)) &&& 1) = 1

theorem byte_set (byte offset : UInt8) (ho : offset < 8) :
    (((byte ||| (1 <<< offset)) >>> offset) &&& 1) = 1 := by bv_decide

theorem byte_preserve (byte writeOffset readOffset : UInt8)
    (hb : ((byte >>> readOffset) &&& 1) = 1) :
    (((byte ||| (1 <<< writeOffset)) >>> readOffset) &&& 1) = 1 := by bv_decide

theorem index_bounded (word : UInt16) : word.toNat/8 < 8192 := by
  have hb := UInt16.toNat_lt word
  omega

theorem offset_bounded (word : UInt16) : UInt8.ofNat (word.toNat%8) < 8 := by
  change (UInt8.ofNat (word.toNat%8)).toNat < 8
  rw [UInt8.toNat_ofNat']
  omega

@[simp] theorem mark_size (bitmap : Array UInt8) (word : UInt16) :
    (mark bitmap word).size = bitmap.size := by
  dsimp only [mark]
  split <;> simp

theorem mark_self (bitmap : Array UInt8) (word : UInt16) (hs : bitmap.size = 8192) :
    Present (mark bitmap word) word := by
  by_cases hz : word.toNat = 0
  · exact Or.inl hz
  · apply Or.inr
    simp only [mark,hz,ite_false]
    rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact index_bounded word)]
    exact byte_set _ _ (offset_bounded word)

theorem mark_preserves (bitmap : Array UInt8) (word old : UInt16) (hs : bitmap.size = 8192)
    (hp : Present bitmap old) : Present (mark bitmap word) old := by
  rcases hp with hp | hp
  · exact Or.inl hp
  · apply Or.inr
    by_cases hz : word.toNat = 0
    · simpa only [mark,hz,ite_true] using hp
    · simp only [mark,hz,ite_false]
      by_cases he : word.toNat/8 = old.toNat/8
      · rw [he,Array.getElem!_set!_self _ _ _ (by rw [hs]; exact index_bounded old)]
        exact byte_preserve _ _ _ hp
      · rw [Array.getElem!_set!_ne _ _ _ _ he]
        exact hp

theorem fold_size (raw : List UInt16) (bitmap : Array UInt8) :
    (raw.foldl mark bitmap).size = bitmap.size := by
  induction raw generalizing bitmap with
  | nil => rfl
  | cons word rest ih => simp only [List.foldl_cons,ih,mark_size]

@[simp] theorem make_size (raw : List UInt16) : (make raw).size = 8192 := by
  rw [make,fold_size,Array.size_replicate]

theorem fold_preserves (raw : List UInt16) (bitmap : Array UInt8) (word : UInt16)
    (hs : bitmap.size = 8192) (hp : Present bitmap word) : Present (raw.foldl mark bitmap) word := by
  induction raw generalizing bitmap with
  | nil => exact hp
  | cons next rest ih =>
    exact ih (mark bitmap next) (by rw [mark_size,hs]) (mark_preserves bitmap next word hs hp)

theorem fold_covers (raw : List UInt16) (bitmap : Array UInt8) (hs : bitmap.size = 8192) :
    ∀ word ∈ raw, Present (raw.foldl mark bitmap) word := by
  induction raw generalizing bitmap with
  | nil => simp
  | cons next rest ih =>
    intro word hw
    rcases List.mem_cons.mp hw with hw | hw
    · subst word
      exact fold_preserves rest (mark bitmap next) next (by rw [mark_size,hs]) (mark_self bitmap next hs)
    · exact ih (mark bitmap next) (by rw [mark_size,hs]) word hw

theorem make_covers (raw : List UInt16) (word : UInt16) (hw : word ∈ raw) : Present (make raw) word :=
  fold_covers raw _ (Array.size_replicate ..) word hw

theorem list_getD (bitmap : Array UInt8) (i : Nat) (hi : i < bitmap.size) :
    bitmap.toList.getD i 0 = bitmap[i]! := by
  have hl : i < bitmap.toList.length := by simpa using hi
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some,
    Array.getElem_toList,getElem!_pos bitmap i hi]

/-- The exact bitmap builder used by the encoder contains every source word
in the decoder's alphabet, with zero handled by its implicit leading entry. -/
theorem make_alphabet (raw : List UInt16) :
    ∀ word ∈ raw, word.toNat ∈ alphabet (make raw).toList := by
  intro word hw
  by_cases hz : word.toNat = 0
  · rw [hz]
    exact List.mem_cons_self
  · have hp := make_covers raw word hw
    have hbit := hp.resolve_left hz
    apply List.mem_cons_of_mem
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_map.mpr
      refine ⟨word.toNat-1,List.mem_range.mpr ?_,?_⟩
      · have hn := UInt16.toNat_lt word
        omega
      · omega
    · have hi : word.toNat/8 < (make raw).size := by rw [make_size]; exact index_bounded word
      rw [list_getD _ _ hi]
      simp only [hbit,beq_self_eq_true]

/-- Numerical reconstruction now derives bitmap coverage from the actual
encoder bitmap, rather than accepting it as an external source hypothesis. -/
theorem reconstruct_make (ctx : Layout.Context) (raw : List UInt16)
    (hs : raw.length = Layout.wordCount ctx.planes) :
    Block.reconstruct ctx (make raw).toList
      ((Block.coefficients ctx (make raw).toList raw).toList.map UInt16.toNat) = raw :=
  Block.reconstruct_coefficients ctx _ raw hs (make_alphabet raw)

end Exr.Piz.Bitmap
