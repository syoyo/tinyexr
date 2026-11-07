/-
  TinyEXR - full PIZ round trip with derived histogram and wire conditions.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizRoundtrip
import Exr.PizHistogram
import Exr.PizWireBounds
import Exr.PizCanonicalWords

namespace Exr.Piz.Block

theorem decode_emitWithTable_bounded (ctx : Layout.Context) (raw : List UInt16)
    (first marker : Nat) (table : List Nat) (trie : Codebook.Trie)
    (hctx : ctx.Valid) (hs : raw.length = Layout.wordCount ctx.planes)
    (hsize : raw.length ≤ 33554431) (hf : first ≤ marker) (hm : marker ≤ 65536)
    (hl : table.length = marker-first+1) (ht : ∀ depth ∈ table, depth < 59)
    (hb : Codebook.build (List.replicate first 0 ++ table) = some trie)
    (hsource : Entropy.SourceValid (List.replicate first 0 ++ table) marker
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat)) :
    decode ctx (emitWithTable ctx raw first marker table) = some (Packet.listBytes (wordsBytes raw)) := by
  have hcount : ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).length = raw.length := by
    simp only [List.length_map,Array.length_toList,coefficients_size,hs]
  have hsamples : ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).length ≤ 33554431 := by
    rw [hcount]; exact hsize
  apply decode_emitWithTable ctx raw first marker table trie hctx hs hf hm hl ht hb hsource
  · exact Huffman.payloadBits_signed_budget _ _ _ hsamples
  · exact Packet.emit_size_bound first marker table _ (by omega) hsamples

/-- With the exact generator histogram/minimum/maximum computation, all
full-block source, marker, slicing and size conditions follow internally.
The checked canonical constructor is an explicit premise in this intermediate
lemma; `decode_encode` below derives it from the accepted frequency profile. -/
theorem decode_emitFrequencyTable (ctx : Layout.Context) (raw : List UInt16) (result : List Nat)
    (trie : Codebook.Trie) (hn : raw ≠ []) (hctx : ctx.Valid)
    (hs : raw.length = Layout.wordCount ctx.planes) (hsize : raw.length ≤ 33554431)
    (he : Frequency.lengths (Frequency.countSymbols
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat)
      (((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).foldl max 0+1)).toList = some result)
    (hb : Codebook.build result = some trie) :
    decode ctx (emitWithTable ctx raw
      (((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).foldl min 65536)
      (((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).foldl max 0+1)
      (result.drop (((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).foldl min 65536))) =
      some (Packet.listBytes (wordsBytes raw)) := by
  let symbols := (coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat
  let largest := symbols.foldl max 0
  let first := symbols.foldl min 65536
  let frequencies := (Frequency.countSymbols symbols (largest+1)).toList
  have hcount : symbols.length = raw.length := by
    simp only [symbols,List.length_map,Array.length_toList,coefficients_size,hs]
  have hnonempty : symbols ≠ [] := by
    intro hz
    have hl := congrArg List.length hz
    have hr : raw.length ≠ 0 := fun h => hn (List.length_eq_zero_iff.mp h)
    simp only [List.length_nil,hcount] at hl
    exact hr hl
  have hmax := Frequency.foldMax_zero_mem symbols hnonempty
  have hfirst := (Frequency.foldMin_bounds symbols 65536).2
  have hf : first ≤ largest+1 := by have h := hfirst _ hmax; omega
  have hm : largest+1 ≤ 65536 := by
    obtain ⟨word,_,heq⟩ := List.mem_map.mp hmax
    have hb := UInt16.toNat_lt word
    change word.toNat = largest at heq
    omega
  have hfreqsize : frequencies.length = largest+1 := by
    simp only [frequencies,Array.length_toList,Frequency.countSymbols_size]
  have hlast : frequencies.reverse.head? ≠ some 0 :=
    Frequency.countSymbols_last_nonzero symbols largest (Frequency.foldMax_spec symbols 0).2.1 hmax
  have hzero : ∀ i, i < first → frequencies.getD i 0 = 0 :=
    Frequency.countSymbols_below_zero symbols (largest+1) first hf hfirst
  have hrestore : List.replicate first 0 ++ result.drop first = result :=
    Frequency.lengths_restore_prefix frequencies result he hlast first (by omega) hzero
  have hslice : (result.drop first).length = (largest+1)-first+1 := by
    have hl := Frequency.lengths_sliced_size frequencies result he first (by omega)
    simpa only [hfreqsize] using hl
  have htable : ∀ depth ∈ result.drop first, depth < 59 := by
    intro depth hd
    have hcap := Frequency.lengths_bound frequencies result he depth (List.mem_of_mem_drop hd)
    omega
  have hsource := Frequency.generated_source_valid symbols result hnonempty he
  apply decode_emitWithTable_bounded ctx raw first (largest+1) (result.drop first) trie hctx hs hsize hf hm hslice htable
  · rw [hrestore]; exact hb
  · exact hsource

/-- Full encoder factory: derive the histogram, frequency tree and actual
canonical table before applying the compressed/raw choice. -/
def encode (ctx : Layout.Context) (raw : List UInt16) : Option Bytes :=
  if raw = [] then some ByteArray.empty else do
    let symbols := (coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat
    let first := symbols.foldl min 65536
    let marker := symbols.foldl max 0+1
    let result ← Frequency.lengths (Frequency.countSymbols symbols marker).toList
    pure (emitWithTable ctx raw first marker (result.drop first))

/-- Successful complete encoding is inverted by the actual full block decoder.
Canonical acceptance, bitmap coverage, entropy source validity, traversal
inverses and wire budgets are all derived rather than caller hypotheses. -/
theorem decode_encode (ctx : Layout.Context) (raw : List UInt16) (encoded : Bytes)
    (hctx : ctx.Valid) (hs : raw.length = Layout.wordCount ctx.planes)
    (hsize : raw.length ≤ 33554431) (he : encode ctx raw = some encoded) :
    decode ctx encoded = some (Packet.listBytes (wordsBytes raw)) := by
  by_cases hn : raw = []
  · subst raw
    simp only [encode,ite_true,Option.some.injEq] at he
    subst encoded
    have hz : Layout.wordCount ctx.planes = 0 := by simpa using hs.symm
    simp [decode,hctx,hz,Packet.listBytes,wordsBytes]
    rfl
  · simp only [encode,hn,ite_false] at he
    cases hf : Frequency.lengths (Frequency.countSymbols
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat)
      (((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat).foldl max 0+1)).toList with
    | none => simp [hf] at he
    | some result =>
      simp [hf] at he
      subst encoded
      obtain ⟨trie,hb⟩ := Canonical.frequency_build_exists _ result hf
      exact decode_emitFrequencyTable ctx raw result trie hn hctx hs hsize hf hb

end Exr.Piz.Block
