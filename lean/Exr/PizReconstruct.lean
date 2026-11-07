/-
  TinyEXR - composed PIZ planar/LUT/wavelet reconstruction inverse.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizComposition
import Exr.PizBlock

namespace Exr.Piz.Block

/-- An absent value maps to rank zero; the alphabet always contains zero. -/
theorem forward_alphabet_lt (bitmap : List UInt8) (value : Nat) :
    forward (alphabet bitmap) value < (alphabet bitmap).length := by
  by_cases hv : value ∈ alphabet bitmap
  · simp only [forward,hv,ite_true]
    exact List.idxOf_lt_length_iff.mpr hv
  · rw [forward,ite_eq_right hv]
    simp only [alphabet,List.length_cons]
    omega

theorem rank_small (bitmap : List UInt8) (data : Array UInt16)
    (hs : decide ((alphabet bitmap).length-1 < 16384) = true) :
    ∀ i, i < (rank bitmap data).size → (rank bitmap data)[i]! < 16384 := by
  have hm : (alphabet bitmap).length-1 < 16384 := of_decide_eq_true hs
  have hl : (alphabet bitmap).length ≤ 16384 := by omega
  have hvalues : ∀ word ∈ rank bitmap data, word < 16384 := by
    intro word hw
    obtain ⟨source,_,rfl⟩ := Array.mem_map.mp hw
    have hb := forward_alphabet_lt bitmap source.toNat
    have hn := forward_lt bitmap source.toNat
    change (UInt16.ofNat (forward (alphabet bitmap) source.toNat)).toNat < 16384
    rw [UInt16.toNat_ofNat',Nat.mod_eq_of_lt hn]
    omega
  intro i hi
  rw [getElem!_pos (rank bitmap data) i hi]
  exact hvalues _ (Array.mem_iff_getElem.mpr ⟨i,hi,rfl⟩)

theorem scatter_preserves {α : Type} (entries : List α) (address : α → Nat) (value : α → UInt16)
    (data : Array UInt16) (predicate : UInt16 → Prop)
    (ha : ∀ word ∈ data, predicate word) (hv : ∀ entry ∈ entries, predicate (value entry)) :
    ∀ word ∈ entries.foldl (fun a entry => a.set! (address entry) (value entry)) data, predicate word := by
  induction entries generalizing data with
  | nil => exact ha
  | cons entry rest ih =>
    apply ih (data.set! (address entry) (value entry))
    · intro word hw
      rcases Array.mem_or_eq_of_mem_setIfInBounds hw with hw | hw
      · exact ha word hw
      · rw [hw]; exact hv entry List.mem_cons_self
    · exact fun entry he => hv entry (List.mem_cons_of_mem _ he)

theorem planar_alphabet (planes : List Layout.Plane) (bitmap : List UInt8) (raw : List UInt16)
    (hv : ∀ word ∈ raw, word.toNat ∈ alphabet bitmap) :
    ∀ word ∈ Layout.planar planes raw, word.toNat ∈ alphabet bitmap := by
  unfold Layout.planar
  apply scatter_preserves
  · intro word hw
    rw [Array.eq_of_mem_replicate hw]
    exact List.mem_cons_self
  · intro entry _
    by_cases hi : entry.2 < raw.length
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      exact hv _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : raw.length ≤ entry.2),Option.getD_none]
      exact List.mem_cons_self

/-- Shared executable coefficient preparation used before Huffman emission. -/
def coefficients (ctx : Layout.Context) (bitmap : List UInt8) (raw : List UInt16) : Array UInt16 :=
  Layout.waveletGo false ((alphabet bitmap).length-1 < 16384) 0 ctx.planes
    (rank bitmap (Layout.planar ctx.planes raw))

theorem coefficients_size (ctx : Layout.Context) (bitmap : List UInt8) (raw : List UInt16) :
    (coefficients ctx bitmap raw).size = Layout.wordCount ctx.planes := by
  simp only [coefficients,Layout.waveletGo_size,rank,Array.size_map,Layout.planar_size]

theorem sample_words (data : Array UInt16) :
    (data.toList.map UInt16.toNat).toArray.map UInt16.ofNat = data := by
  simp [Function.comp_def]

/-- Complete numerical reconstruction after Huffman decoding: channel
scatter, bounded LUT ranks, every wavelet level/lane, LUT restoration and
canonical gather compose to the original words. Bitmap coverage is the only
source-value precondition; wavelet mode bounds are derived from that bitmap. -/
theorem reconstruct_coefficients (ctx : Layout.Context) (bitmap : List UInt8) (raw : List UInt16)
    (hs : raw.length = Layout.wordCount ctx.planes)
    (hv : ∀ word ∈ raw, word.toNat ∈ alphabet bitmap) :
    reconstruct ctx bitmap ((coefficients ctx bitmap raw).toList.map UInt16.toNat) = raw := by
  have ha : 0+Layout.wordCount ctx.planes ≤ (rank bitmap (Layout.planar ctx.planes raw)).size := by
    simp only [rank,Array.size_map,Layout.planar_size,Nat.zero_add,Nat.le_refl]
  have hi := Composition.waveletGo_inverse
    (decide ((alphabet bitmap).length-1 < 16384)) 0 ctx.planes
    (rank bitmap (Layout.planar ctx.planes raw)) ha (rank_small bitmap _)
  unfold reconstruct
  rw [sample_words]
  change Layout.canonical ctx.planes
    (restore bitmap (Layout.waveletGo true (decide ((alphabet bitmap).length-1 < 16384)) 0 ctx.planes
      (coefficients ctx bitmap raw))) = raw
  unfold coefficients
  rw [hi,restore_rank bitmap _ (planar_alphabet ctx.planes bitmap raw hv)]
  exact Layout.canonical_planar ctx.planes raw hs

end Exr.Piz.Block
