/-
  TinyEXR - canonical PIZ trimmed-bitmap span and omitted-zero bounds.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizBitmap

namespace Exr.Piz.Bitmap

structure Span where
  first : Nat
  last : Nat
  deriving Repr, DecidableEq

def Span.extend (span : Span) (index : Nat) : Span := ⟨min span.first index,max span.last index⟩

def Span.Valid (span : Span) : Prop := span.first ≤ 8191 ∧ span.last < 8192 ∧
  (span.first ≤ span.last ∨ (span.first = 8191 ∧ span.last = 0))

def Span.Contains (span : Span) (index : Nat) : Prop := span.first ≤ index ∧ index ≤ span.last

def Span.count (span : Span) : Nat := if span.first ≤ span.last then span.last-span.first+1 else 0

def active (bitmap : Array UInt8) : List Nat :=
  (List.range bitmap.size).filter (fun i => bitmap[i]! != 0)

def span (bitmap : Array UInt8) : Span := (active bitmap).foldl Span.extend ⟨8191,0⟩

theorem Span.extend_valid (s : Span) (i : Nat) (hs : s.Valid) (hi : i < 8192) : (s.extend i).Valid := by
  have hfirst := Nat.min_le_left s.first i
  have hlast := Nat.max_lt.mpr ⟨hs.2.1,hi⟩
  have hbelow := Nat.min_le_right s.first i
  have habove := Nat.le_max_right s.last i
  exact ⟨by dsimp [Span.extend]; omega,hlast,Or.inl (by dsimp [Span.extend]; omega)⟩

theorem Span.extend_contains (s : Span) (i : Nat) : (s.extend i).Contains i :=
  ⟨Nat.min_le_right _ _,Nat.le_max_right _ _⟩

theorem Span.extend_preserves (s : Span) (i old : Nat) (hs : s.Contains old) : (s.extend i).Contains old :=
  ⟨Nat.le_trans (Nat.min_le_left _ _) hs.1,Nat.le_trans hs.2 (Nat.le_max_left _ _)⟩

theorem span_fold_valid (indices : List Nat) (s : Span) (hs : s.Valid)
    (hi : ∀ i ∈ indices, i < 8192) : (indices.foldl Span.extend s).Valid := by
  induction indices generalizing s with
  | nil => exact hs
  | cons i rest ih =>
    exact ih (s.extend i) (s.extend_valid i hs (hi i List.mem_cons_self))
      (fun j hj => hi j (List.mem_cons_of_mem _ hj))

theorem span_fold_preserves (indices : List Nat) (s : Span) (i : Nat) (hs : s.Contains i) :
    (indices.foldl Span.extend s).Contains i := by
  induction indices generalizing s with
  | nil => exact hs
  | cons j rest ih => exact ih (s.extend j) (s.extend_preserves j i hs)

theorem span_fold_covers (indices : List Nat) (s : Span) :
    ∀ i ∈ indices, (indices.foldl Span.extend s).Contains i := by
  induction indices generalizing s with
  | nil => simp
  | cons j rest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact span_fold_preserves rest (s.extend j) j (s.extend_contains j)
    · exact ih (s.extend j) i hi

theorem span_valid (bitmap : Array UInt8) (hs : bitmap.size = 8192) : (span bitmap).Valid := by
  apply span_fold_valid
  · exact ⟨by decide,by decide,Or.inr ⟨rfl,rfl⟩⟩
  · intro i hi
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    omega

theorem span_covers (bitmap : Array UInt8) (i : Nat) (hi : i < bitmap.size) (hn : bitmap[i]! ≠ 0) :
    (span bitmap).Contains i := by
  apply span_fold_covers
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr hi,by simpa using hn⟩

/-- Every byte omitted before/after the canonical extent is zero. This also
covers the empty-bitmap sentinel, whose extent contains no index. -/
theorem span_outside_zero (bitmap : Array UInt8) (i : Nat) (hi : i < bitmap.size)
    (ho : i < (span bitmap).first ∨ (span bitmap).last < i) : bitmap[i]! = 0 := by
  by_contra hn
  have hc := span_covers bitmap i hi hn
  unfold Span.Contains at hc
  omega

theorem Span.count_bound (s : Span) (hs : s.Valid) : s.first+s.count ≤ 8192 := by
  unfold Span.count
  split <;> have := hs.1 <;> have := hs.2.1 <;> omega

theorem Span.end_after_last (s : Span) (hs : s.Valid) : s.last < s.first+s.count := by
  unfold Span.count
  split
  · omega
  · have hv := hs.2.2
    omega

/-- Reinsert exactly the zeros omitted by canonical bitmap trimming. -/
theorem restore_span (bitmap : Array UInt8) (hs : bitmap.size = 8192) :
    List.replicate (span bitmap).first 0 ++
      (bitmap.toList.drop (span bitmap).first).take (span bitmap).count ++
      List.replicate (8192-(span bitmap).first-(span bitmap).count) 0 = bitmap.toList := by
  let s := span bitmap
  have hv := span_valid bitmap hs
  have hb := s.count_bound hv
  have he := s.end_after_last hv
  have hl : bitmap.toList.length = 8192 := by simpa using hs
  have hbefore : bitmap.toList.take s.first = List.replicate s.first 0 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp only [List.length_take,hl,Nat.min_eq_left (by omega : s.first ≤ 8192)]
    · intro byte hm
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hm
      have hif : i < s.first := by simp only [List.length_take,hl] at hi; omega
      have hib : i < bitmap.size := by omega
      have hz := span_outside_zero bitmap i hib (Or.inl hif)
      simpa only [List.getElem_take,Array.getElem_toList,getElem!_pos bitmap i hib] using hz
  have hafter : bitmap.toList.drop (s.first+s.count) = List.replicate (8192-s.first-s.count) 0 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp only [List.length_drop,hl,Nat.sub_add_eq]
    · intro byte hm
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hm
      have hib : s.first+s.count+i < bitmap.size := by simp only [List.length_drop,hl] at hi; omega
      have hlast : s.last < s.first+s.count+i := by omega
      have hz := span_outside_zero bitmap (s.first+s.count+i) hib (Or.inr hlast)
      simpa only [List.getElem_drop,Array.getElem_toList,getElem!_pos bitmap (s.first+s.count+i) hib] using hz
  change List.replicate s.first 0 ++ (bitmap.toList.drop s.first).take s.count ++
    List.replicate (8192-s.first-s.count) 0 = bitmap.toList
  rw [← hbefore,← hafter,List.append_assoc,← List.drop_drop,List.take_append_drop,List.take_append_drop]

end Exr.Piz.Bitmap
