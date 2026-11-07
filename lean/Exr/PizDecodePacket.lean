/-
  TinyEXR - composed Huffman packet parsing and PIZ word reconstruction.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizReconstruct
import Exr.PizPacketEmit

namespace Exr.Piz.Block

/-- The actual Huffman packet parser and complete numerical reconstruction
compose to the source words. Canonical-table validity is explicit until the
frequency-tree-to-canonical constructor theorem discharges that obligation. -/
theorem parse_reconstruct_emit (ctx : Layout.Context) (bitmap : List UInt8) (raw : List UInt16)
    (first marker : Nat) (table : List Nat) (trie : Codebook.Trie)
    (hn : raw ≠ []) (hs : raw.length = Layout.wordCount ctx.planes)
    (hv : ∀ word ∈ raw, word.toNat ∈ alphabet bitmap)
    (hf : first ≤ marker) (hm : marker ≤ 65536)
    (hl : table.length = marker-first+1) (ht : ∀ depth ∈ table, depth < 59)
    (hb : Codebook.build (List.replicate first 0 ++ table) = some trie)
    (hsource : Entropy.SourceValid (List.replicate first 0 ++ table) marker
      ((coefficients ctx bitmap raw).toList.map UInt16.toNat))
    (hbudget : (Huffman.payloadBits (List.replicate first 0 ++ table)
      ((coefficients ctx bitmap raw).toList.map UInt16.toNat) marker).length < 2147483648) :
    (Packet.parse (Packet.emit first marker table ((coefficients ctx bitmap raw).toList.map UInt16.toNat))
      (Layout.wordCount ctx.planes)).map (fun packet => reconstruct ctx bitmap packet.samples) = some raw := by
  let symbols := (coefficients ctx bitmap raw).toList.map UInt16.toNat
  have hcount : symbols.length = Layout.wordCount ctx.planes := by
    simp only [symbols,List.length_map,Array.length_toList,coefficients_size]
  have hnonempty : symbols ≠ [] := by
    intro he
    have hz := congrArg List.length he
    have hr : raw.length ≠ 0 := fun h => hn (List.length_eq_zero_iff.mp h)
    simp only [List.length_nil] at hz
    omega
  have hp := Packet.parse_emit_nonempty first marker table symbols trie hnonempty hf hm hl ht hb hsource hbudget
  rw [hcount] at hp
  rw [hp]
  simp only [Option.map_some]
  rw [reconstruct_coefficients ctx bitmap raw hs hv]

end Exr.Piz.Block
