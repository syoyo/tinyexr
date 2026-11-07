/-
  TinyEXR - source/marker validity derived from emitted frequency tables.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizLengthTable
import Exr.PizEntropy

namespace Exr.Piz.Frequency

/-- Active source frequencies and the run marker provide all entropy-reader
source conditions; callers need no tree/path or per-symbol depth witnesses. -/
theorem lengths_source_valid (frequencies result samples : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (hs : ∀ symbol ∈ samples, symbol < frequencies.length ∧ frequencies.getD symbol 0 ≠ 0) :
    Entropy.SourceValid result frequencies.length samples := by
  constructor
  · exact ⟨by rw [lengths_size frequencies result he]; omega,
      lengths_marker_active frequencies result he hlast⟩
  · intro symbol hm
    have hi := hs symbol hm
    exact ⟨hi.1,by rw [lengths_size frequencies result he]; omega,
      lengths_frequency_active frequencies result he hlast symbol hi.1 hi.2⟩

/-- Omitted leading symbols have exactly the zero lengths reconstructed by
the Huffman packet parser before its sliced canonical table. -/
theorem lengths_zero_prefix (frequencies result : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (first : Nat) (hf : first ≤ frequencies.length)
    (hz : ∀ i, i < first → frequencies.getD i 0 = 0) :
    result.take first = List.replicate first 0 := by
  apply List.eq_replicate_iff.mpr
  constructor
  · rw [List.length_take,lengths_size frequencies result he,Nat.min_eq_left (by omega)]
  · intro depth hd
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hd
    have hif : i < first := by simp only [List.length_take] at hi; omega
    have hir : i < result.length := by simp only [List.length_take] at hi; omega
    have hzero := lengths_frequency_zero frequencies result he hlast i (by omega) (hz i hif)
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hir,Option.getD_some] at hzero
    simpa only [List.getElem_take] using hzero

theorem lengths_restore_prefix (frequencies result : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (first : Nat) (hf : first ≤ frequencies.length)
    (hz : ∀ i, i < first → frequencies.getD i 0 = 0) :
    List.replicate first 0 ++ result.drop first = result := by
  rw [← lengths_zero_prefix frequencies result he hlast first hf hz,List.take_append_drop]

theorem lengths_sliced_source_valid (frequencies result samples : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (hs : ∀ symbol ∈ samples, symbol < frequencies.length ∧ frequencies.getD symbol 0 ≠ 0)
    (first : Nat) (hf : first ≤ frequencies.length)
    (hz : ∀ i, i < first → frequencies.getD i 0 = 0) :
    Entropy.SourceValid (List.replicate first 0 ++ result.drop first) frequencies.length samples := by
  rw [lengths_restore_prefix frequencies result he hlast first hf hz]
  exact lengths_source_valid frequencies result samples he hlast hs

theorem lengths_sliced_size (frequencies result : List Nat)
    (he : lengths frequencies = some result) (first : Nat) (hf : first ≤ frequencies.length) :
    (result.drop first).length = frequencies.length-first+1 := by
  rw [List.length_drop,lengths_size frequencies result he]
  omega

end Exr.Piz.Frequency
