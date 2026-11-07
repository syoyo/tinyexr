/-
  TinyEXR - canonical PIZ bitmap framing serialization and round trip.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizBitmapSpan
import Exr.PizPacketEmit

namespace Exr.Piz.Block

def word16 (value : Nat) : Bytes := putU16LE (UInt16.ofNat value) ByteArray.empty

@[simp] theorem word16_size (value : Nat) : (word16 value).size = 2 := by simp [word16,putU16LE]

def frameBytes (first last : Nat) (segment : List UInt8) (payload : Bytes) : Bytes :=
  (word16 first ++ word16 last) ++ (Packet.listBytes segment ++ (Packet.word payload.size ++ payload))

def emitFraming (bitmap : Array UInt8) (payload : Bytes) : Bytes :=
  let s := Bitmap.span bitmap
  frameBytes s.first s.last ((bitmap.toList.drop s.first).take s.count) payload

theorem read16_append_left (a b : Bytes) (i : Nat) (hi : i+2 ≤ a.size) :
    getU16LE (a ++ b) i = getU16LE a i := by
  unfold getU16LE
  simp only [getU8]
  rw [getU8?_append_left (by omega : i < a.size),getU8?_append_left (by omega : i+1 < a.size)]

theorem read16_append_right (a b : Bytes) (i : Nat) :
    getU16LE (a ++ b) (a.size+i) = getU16LE b i := by
  unfold getU16LE
  simp only [getU8]
  rw [getU8?_append_right (by omega : a.size ≤ a.size+i),
    getU8?_append_right (by omega : a.size ≤ a.size+i+1)]
  rw [show a.size+i-a.size = i by omega,
    show a.size+i+1-a.size = i+1 by omega]

theorem read16_word (value : Nat) (tail : Bytes) :
    getU16LE (word16 value ++ tail) 0 = some (UInt16.ofNat value) := by
  rw [read16_append_left _ _ 0 (by simp)]
  exact getU16LE_putU16LE ByteArray.empty _

theorem frameBytes_size (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    (frameBytes first last segment payload).size = 8+segment.length+payload.size := by
  simp [frameBytes,Nat.add_comm,Nat.add_left_comm]

theorem frameBytes_first (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    getU16LE (frameBytes first last segment payload) 0 = some (UInt16.ofNat first) := by
  rw [frameBytes,ByteArray.append_assoc,read16_word]

theorem frameBytes_last (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    getU16LE (frameBytes first last segment payload) 2 = some (UInt16.ofNat last) := by
  rw [frameBytes,ByteArray.append_assoc]
  have he := read16_append_right (word16 first)
    (word16 last ++ (Packet.listBytes segment ++ (Packet.word payload.size ++ payload))) 0
  simp only [word16_size,Nat.add_zero] at he
  rw [he,read16_word]

theorem frameBytes_length (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    getU32LE (frameBytes first last segment payload) (4+segment.length) = some (UInt32.ofNat payload.size) := by
  have he := getU32LE_append_right
    (a := (word16 first ++ word16 last) ++ Packet.listBytes segment)
    (b := Packet.word payload.size ++ payload)
  simp only [ByteArray.size_append,word16_size,Packet.listBytes_size] at he
  change getU32LE (((word16 first ++ word16 last) ++ Packet.listBytes segment) ++
    (Packet.word payload.size ++ payload)) (4+segment.length) = _
  rw [he,Packet.read_word]

theorem frameBytes_segment (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    (frameBytes first last segment payload).extract 4 (4+segment.length) = Packet.listBytes segment := by
  have he := extract_append_size_head
    (a := word16 first ++ word16 last)
    (b := Packet.listBytes segment ++ (Packet.word payload.size ++ payload))
    (k := segment.length) (by simp)
  simp only [ByteArray.size_append,word16_size] at he
  rw [frameBytes,he]
  exact ByteArray.extract_append_eq_left (by simp)

theorem frameBytes_payload (first last : Nat) (segment : List UInt8) (payload : Bytes) :
    (frameBytes first last segment payload).extract (8+segment.length)
      (frameBytes first last segment payload).size = payload := by
  have he := extract_append_right_eq
    (a := ((word16 first ++ word16 last) ++ Packet.listBytes segment) ++ Packet.word payload.size)
    (b := payload)
  simpa only [frameBytes,ByteArray.append_assoc,ByteArray.size_append,word16_size,
    Packet.listBytes_size,Packet.word_size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

def paddedBitmap (first count : Nat) (segment : List UInt8) : List UInt8 :=
  if count = 0 then List.replicate 8192 0 else
    List.replicate first 0 ++ segment ++ List.replicate (8192-first-count) 0

theorem framing_frameBytes (first last : Nat) (segment : List UInt8) (payload : Bytes)
    (hv : (⟨first,last⟩ : Bitmap.Span).Valid)
    (hl : segment.length = (⟨first,last⟩ : Bitmap.Span).count)
    (hp : payload.size < 4294967296) :
    framing (frameBytes first last segment payload) =
      some ⟨paddedBitmap first (⟨first,last⟩ : Bitmap.Span).count segment,payload⟩ := by
  change first ≤ 8191 ∧ last < 8192 ∧ (first ≤ last ∨ first = 8191 ∧ last = 0) at hv
  let bytes := frameBytes first last segment payload
  let count := (⟨first,last⟩ : Bitmap.Span).count
  have hcount : segment.length = count := hl
  have hc : (if first ≤ last then last-first+1 else 0) = count := rfl
  have hf : (UInt16.ofNat first).toNat = first := by
    rw [UInt16.toNat_ofNat',Nat.mod_eq_of_lt (by have := hv.1; omega : first < 65536)]
  have hh : (UInt16.ofNat last).toNat = last := by
    rw [UInt16.toNat_ofNat',Nat.mod_eq_of_lt (by have := hv.2.1; omega : last < 65536)]
  have hpn : (UInt32.ofNat payload.size).toNat = payload.size := by
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt hp]
  have hcond : last < 8192 ∧ (first ≤ last ∨ first = 8191 ∧ last = 0) := ⟨hv.2.1,hv.2.2⟩
  have hlen : getU32LE bytes (4+count) = some (UInt32.ofNat payload.size) := by
    rw [← hcount]
    exact frameBytes_length first last segment payload
  have hsize : bytes.size = 8+count+payload.size := by rw [frameBytes_size,hcount]
  have hbudget : 8+count+payload.size ≤ bytes.size := by omega
  have hslice : (bytes.extract 4 (4+count)).data.toList = segment := by
    rw [← hcount,frameBytes_segment,Packet.listBytes_list]
  have he : expandBitmap bytes first count = paddedBitmap first count segment := by
    simp only [expandBitmap,paddedBitmap,hslice]
  change framing bytes = _
  dsimp only [framing]
  rw [frameBytes_first,frameBytes_last]
  change (if (UInt16.ofNat last).toNat < 8192 ∧
    ((UInt16.ofNat first).toNat ≤ (UInt16.ofNat last).toNat ∨
      (UInt16.ofNat first).toNat = 8191 ∧ (UInt16.ofNat last).toNat = 0) then _ else none) = _
  rw [hf,hh,ite_eq_left hcond]
  rw [hc]
  simp only [hlen]
  change (if 8+count+(UInt32.ofNat payload.size).toNat ≤ bytes.size then _ else none) = _
  rw [hpn,ite_eq_left hbudget]
  change some (⟨expandBitmap bytes first count,bytes.extract (8+count) (8+count+payload.size)⟩ : Framing) = _
  have hpay : bytes.extract (8+count) (8+count+payload.size) = payload := by
    rw [← hsize,← hcount]
    exact frameBytes_payload first last segment payload
  rw [he,hpay]

theorem padded_span (bitmap : Array UInt8) (hs : bitmap.size = 8192) :
    paddedBitmap (Bitmap.span bitmap).first (Bitmap.span bitmap).count
      ((bitmap.toList.drop (Bitmap.span bitmap).first).take (Bitmap.span bitmap).count) = bitmap.toList := by
  let s := Bitmap.span bitmap
  have hv := Bitmap.span_valid bitmap hs
  have hb := s.count_bound hv
  have hr := Bitmap.restore_span bitmap hs
  change List.replicate s.first 0 ++ (bitmap.toList.drop s.first).take s.count ++
    List.replicate (8192-s.first-s.count) 0 = bitmap.toList at hr
  change paddedBitmap s.first s.count ((bitmap.toList.drop s.first).take s.count) = bitmap.toList
  by_cases hz : s.count = 0
  · simp only [paddedBitmap,hz,ite_true]
    simpa only [hz,List.take_zero,List.append_nil,Nat.sub_zero,List.replicate_append_replicate,
      Nat.add_sub_of_le (by omega : s.first ≤ 8192)] using hr
  · rw [paddedBitmap,ite_eq_right hz]
    exact hr

/-- The actual trimmed bitmap frame, including its empty-bitmap sentinel,
parses back to the complete source bitmap and exact Huffman packet bytes. -/
theorem framing_emitFraming (bitmap : Array UInt8) (payload : Bytes)
    (hs : bitmap.size = 8192) (hp : payload.size < 4294967296) :
    framing (emitFraming bitmap payload) = some ⟨bitmap.toList,payload⟩ := by
  let s := Bitmap.span bitmap
  have hv := Bitmap.span_valid bitmap hs
  have hb := s.count_bound hv
  have hl : ((bitmap.toList.drop s.first).take s.count).length = s.count := by
    simp only [List.length_take,List.length_drop,Array.length_toList,hs]
    exact Nat.min_eq_left (by omega)
  have hr := framing_frameBytes s.first s.last ((bitmap.toList.drop s.first).take s.count) payload hv hl hp
  change framing (frameBytes s.first s.last ((bitmap.toList.drop s.first).take s.count) payload) = _
  rw [hr]
  rw [padded_span bitmap hs]

end Exr.Piz.Block
