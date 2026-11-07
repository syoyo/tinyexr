/-
  TinyEXR - PIZ bitmap, Huffman, wavelet and sampled-channel composition.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizLayout
import Exr.PizPacket

namespace Exr.Piz.Block

structure Framing where
  bitmap : List UInt8
  payload : Bytes
  deriving Repr

def expandBitmap (bytes : Bytes) (first count : Nat) : List UInt8 :=
  if count = 0 then List.replicate 8192 0 else
    List.replicate first 0 ++ (bytes.extract 4 (4+count)).data.toList ++
      List.replicate (8192-first-count) 0

/-- The empty bitmap has the unique sentinel (8191,0). The advertised
Huffman extent is checked before extracting it; trailing bytes are tolerated,
matching the C codec's framing policy. -/
def framing (bytes : Bytes) : Option Framing := do
  let lo ← getU16LE bytes 0
  let hi ← getU16LE bytes 2
  let first := lo.toNat
  let last := hi.toNat
  if last < 8192 ∧ (first ≤ last ∨ (first = 8191 ∧ last = 0)) then
    let count := if first ≤ last then last-first+1 else 0
    let size ← getU32LE bytes (4+count)
    let start := 8+count
    if start+size.toNat ≤ bytes.size then
      let bitmap := expandBitmap bytes first count
      pure ⟨bitmap,bytes.extract start (start+size.toNat)⟩
    else none
  else none

/-- Accepted outer framing reconstructs the complete bitmap allocation and
extracts a Huffman extent contained in the input. -/
theorem framing_sound (bytes : Bytes) (frame : Framing)
    (hf : framing bytes = some frame) :
    frame.bitmap.length = 8192 ∧ frame.payload.size ≤ bytes.size := by
  dsimp only [framing] at hf
  cases hlo : getU16LE bytes 0 with
  | none => simp [hlo] at hf
  | some lo =>
    cases hhi : getU16LE bytes 2 with
    | none => simp [hlo,hhi] at hf
    | some hi =>
      let first := lo.toNat
      let last := hi.toNat
      by_cases hv : last < 8192 ∧ (first ≤ last ∨ (first = 8191 ∧ last = 0))
      · let count := if first ≤ last then last-first+1 else 0
        cases hs : getU32LE bytes (4+count) with
        | none => simp [hlo,hhi,first,last,hv,count,hs] at hf
        | some size =>
          by_cases hb : 8+count+size.toNat ≤ bytes.size
          · let bitmap := expandBitmap bytes first count
            have he : (⟨bitmap,bytes.extract (8+count) (8+count+size.toNat)⟩ : Framing) = frame := by
              simpa [hlo,hhi,first,last,hv,count,hs,hb,bitmap] using hf
            rw [← he]
            constructor
            · dsimp only
              by_cases hz : count = 0
              · simp only [bitmap,expandBitmap,hz,ite_true,List.length_replicate]
              · have hc : first+count ≤ 8192 := by
                  dsimp only [count] at hz ⊢
                  split at hz <;> split <;> omega
                have hi : 4+count ≤ bytes.size := by omega
                simp only [bitmap, expandBitmap, hz, ite_false, List.length_append, List.length_replicate,
                  Array.length_toList, ByteArray.size_data, ByteArray.size_extract, Nat.min_eq_left hi]
                omega
            · simp only [ByteArray.size_extract]
              omega
          · simp [hlo,hhi,first,last,hv,count,hs,hb] at hf
      · simp [hlo,hhi,first,last,hv] at hf

/-- Range reduction uses the same bounded UInt16 ranks as the C LUT. -/
def rank (bitmap : List UInt8) (data : Array UInt16) : Array UInt16 :=
  let values := alphabet bitmap
  data.map (fun word => UInt16.ofNat (forward values word.toNat))

def restore (bitmap : List UInt8) (data : Array UInt16) : Array UInt16 :=
  let values := alphabet bitmap
  data.map (fun word => UInt16.ofNat (reverse values word.toNat))

/-- The executable word-array range transform loses no information when
the bitmap contains every source value. The rank narrowing is proved safe. -/
theorem restore_rank (bitmap : List UInt8) (data : Array UInt16)
    (hv : ∀ word ∈ data, word.toNat ∈ alphabet bitmap) :
    restore bitmap (rank bitmap data) = data := by
  unfold restore rank
  rw [Array.map_map]
  conv_rhs => rw [← Array.map_id data]
  apply Array.map_congr_left
  intro word hw
  have hb := forward_lt bitmap word.toNat
  simp only [Function.comp_def, UInt16.toNat_ofNat', Nat.mod_eq_of_lt hb]
  rw [reverse_forward (alphabet bitmap) word.toNat (hv word hw)]
  simp

/-- Reconstruction preserves allocation size through all channels and lanes.
The sorted layout accesses are bounded by `Layout.canonical_access`. -/
def reconstruct (ctx : Layout.Context) (bitmap : List UInt8) (samples : List Nat) : List UInt16 :=
  let values := alphabet bitmap
  let planar := samples.toArray.map UInt16.ofNat
  let transformed := Layout.waveletGo true (values.length-1 < 16384) 0 ctx.planes planar
  let restored := restore bitmap transformed
  Layout.canonical ctx.planes restored

def wordsBytes (words : List UInt16) : List UInt8 :=
  words.flatMap (fun (word : UInt16) => [UInt8.ofNat word.toNat, UInt8.ofNat (word.toNat / 256)])

/-- Direct codec semantics: an empty expected sample allocation is invalid
for a compressed PIZ frame, even if its Huffman packet is empty. -/
def decodeCompressed (ctx : Layout.Context) (bytes : Bytes) : Option Bytes := do
  if ctx.Valid ∧ 0 < Layout.wordCount ctx.planes then
    let frame ← framing bytes
    let packet ← Packet.parse frame.payload (Layout.wordCount ctx.planes)
    pure (ByteArray.mk (wordsBytes (reconstruct ctx frame.bitmap packet.samples)).toArray)
  else none

/-- Public dispatch semantics: equal sizes are raw fallback; unequal empty
or expanded representations are rejected before entering the PIZ codec. -/
def decode (ctx : Layout.Context) (bytes : Bytes) : Option Bytes :=
  if ctx.Valid then
    let expected := 2*Layout.wordCount ctx.planes
    if bytes.size = expected then some bytes else
      if bytes.size = 0 ∨ expected = 0 ∨ expected < bytes.size then none
      else decodeCompressed ctx bytes
  else none

theorem reconstruct_size (ctx : Layout.Context) (bitmap : List UInt8) (samples : List Nat) :
    (reconstruct ctx bitmap samples).length = Layout.wordCount ctx.planes :=
  Layout.canonical_size _ _

theorem wordsBytes_size (words : List UInt16) : (wordsBytes words).length = 2*words.length := by
  simp [wordsBytes, List.length_flatMap, Nat.mul_comm]


theorem decodeCompressed_size (ctx : Layout.Context) (bytes output : Bytes)
    (hd : decodeCompressed ctx bytes = some output) : output.size = 2*Layout.wordCount ctx.planes := by
  dsimp only [decodeCompressed] at hd
  split at hd
  · cases hf : framing bytes with
    | none => simp [hf] at hd
    | some frame =>
      cases hp : Packet.parse frame.payload (Layout.wordCount ctx.planes) with
      | none => simp [hf,hp] at hd
      | some packet =>
        have he : ByteArray.mk (wordsBytes (reconstruct ctx frame.bitmap packet.samples)).toArray = output := by
          simpa [hf,hp] using hd
        rw [← he]
        simp only [ByteArray.size,List.size_toArray,wordsBytes_size,reconstruct_size]
  · simp at hd

/-- Every accepted raw or compressed block has exactly the allocation size
computed from sampled channel geometry, including zero-sample channels. -/
theorem decode_size (ctx : Layout.Context) (bytes output : Bytes)
    (hd : decode ctx bytes = some output) : output.size = 2*Layout.wordCount ctx.planes := by
  dsimp only [decode] at hd
  split at hd
  · split at hd
    · cases Option.some.inj hd
      assumption
    · split at hd
      · simp at hd
      · exact decodeCompressed_size ctx bytes output hd
  · simp at hd

/-- The Huffman output allocation suffices for every subsequent intermediate
array and the final reorder; wavelet execution never changes its size. -/
theorem reconstructed_access (ctx : Layout.Context) (frame : Framing) (packet : Packet.Parsed)
    (hp : Packet.parse frame.payload (Layout.wordCount ctx.planes) = some packet)
    (token : Layout.Token) (ht : token ∈ Layout.tokens ctx.planes) :
    token.address < (Layout.waveletGo true ((alphabet frame.bitmap).length-1 < 16384)
      0 ctx.planes (packet.samples.toArray.map UInt16.ofNat)).size := by
  rw [Layout.waveletGo_size, Array.size_map, List.size_toArray, Packet.parse_size _ _ _ hp]
  exact Layout.tokens_bounds ctx.planes token ht

end Exr.Piz.Block
