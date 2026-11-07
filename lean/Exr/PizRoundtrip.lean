/-
  TinyEXR - full PIZ block parser/emitter composition with raw fallback.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizFrameEmit
import Exr.PizDecodePacket

namespace Exr.Piz.Block

/-- Complete block emission for a selected frequency-derived length table.
The C encoder stores canonical words raw whenever compression does not help. -/
def emitWithTable (ctx : Layout.Context) (raw : List UInt16) (first marker : Nat) (table : List Nat) : Bytes :=
  let bitmap := Bitmap.make raw
  let samples := (coefficients ctx bitmap.toList raw).toList.map UInt16.toNat
  let packet := Packet.emit first marker table samples
  let compressed := emitFraming bitmap packet
  let original := Packet.listBytes (wordsBytes raw)
  if compressed.size < original.size then compressed else original

theorem emitWithTable_empty (ctx : Layout.Context) (first marker : Nat) (table : List Nat) :
    emitWithTable ctx [] first marker table = ByteArray.empty := by
  unfold emitWithTable
  simp only [Packet.listBytes_size,wordsBytes_size,List.length_nil,Nat.mul_zero,Nat.not_lt_zero,ite_false]
  rfl

/-- Full PIZ framing/Huffman/wavelet/LUT/reorder parser composition, including
raw fallback. All bitmap and wavelet obligations are derived from the source;
representability, source activity and successful canonical construction remain
explicit frequency-table preconditions. -/
theorem decode_emitWithTable (ctx : Layout.Context) (raw : List UInt16)
    (first marker : Nat) (table : List Nat) (trie : Codebook.Trie)
    (hctx : ctx.Valid) (hs : raw.length = Layout.wordCount ctx.planes)
    (hf : first ≤ marker) (hm : marker ≤ 65536)
    (hl : table.length = marker-first+1) (ht : ∀ depth ∈ table, depth < 59)
    (hb : Codebook.build (List.replicate first 0 ++ table) = some trie)
    (hsource : Entropy.SourceValid (List.replicate first 0 ++ table) marker
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat))
    (hbudget : (Huffman.payloadBits (List.replicate first 0 ++ table)
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat) marker).length < 2147483648)
    (hpacket : (Packet.emit first marker table
      ((coefficients ctx (Bitmap.make raw).toList raw).toList.map UInt16.toNat)).size < 4294967296) :
    decode ctx (emitWithTable ctx raw first marker table) = some (Packet.listBytes (wordsBytes raw)) := by
  let bitmap := Bitmap.make raw
  let packet := Packet.emit first marker table ((coefficients ctx bitmap.toList raw).toList.map UInt16.toNat)
  let compressed := emitFraming bitmap packet
  let original := Packet.listBytes (wordsBytes raw)
  have ho : original.size = 2*Layout.wordCount ctx.planes := by
    rw [Packet.listBytes_size,wordsBytes_size,hs]
  change decode ctx (if compressed.size < original.size then compressed else original) = some original
  by_cases hc : compressed.size < original.size
  · rw [ite_eq_left hc]
    have hn : raw ≠ [] := by
      intro he
      have hz : original.size = 0 := by simp only [original,he,Packet.listBytes_size,wordsBytes_size,List.length_nil,Nat.mul_zero]
      omega
    have hp := parse_reconstruct_emit ctx bitmap.toList raw first marker table trie hn hs
      (Bitmap.make_alphabet raw) hf hm hl ht hb hsource hbudget
    change (Packet.parse packet (Layout.wordCount ctx.planes)).map
      (fun parsed => reconstruct ctx bitmap.toList parsed.samples) = some raw at hp
    have hframe := framing_emitFraming bitmap packet (Bitmap.make_size raw) hpacket
    have hne : compressed.size ≠ 2*Layout.wordCount ctx.planes := by omega
    have hpositive : 0 < compressed.size := by
      dsimp only [compressed,emitFraming]
      rw [frameBytes_size]
      omega
    have hguard : ¬(compressed.size = 0 ∨ 2*Layout.wordCount ctx.planes = 0 ∨
        2*Layout.wordCount ctx.planes < compressed.size) := by omega
    have hcount : 0 < Layout.wordCount ctx.planes := by omega
    dsimp only [decode]
    rw [ite_eq_left hctx,ite_eq_right hne,ite_eq_right hguard]
    dsimp only [decodeCompressed]
    rw [ite_eq_left ⟨hctx,hcount⟩,hframe]
    change (do
      let parsed ← Packet.parse packet (Layout.wordCount ctx.planes)
      pure (Packet.listBytes (wordsBytes (reconstruct ctx bitmap.toList parsed.samples)))) = some original
    cases hparse : Packet.parse packet (Layout.wordCount ctx.planes) with
    | none => simp [hparse] at hp
    | some parsed =>
      have hr : reconstruct ctx bitmap.toList parsed.samples = raw := by
        simpa only [hparse,Option.map_some,Option.some.injEq] using hp
      change some (Packet.listBytes (wordsBytes (reconstruct ctx bitmap.toList parsed.samples))) = some original
      rw [hr]
  · rw [ite_eq_right hc]
    dsimp only [decode]
    rw [ite_eq_left hctx]
    rw [ite_eq_left ho]

end Exr.Piz.Block
