/-
  TinyEXR - PIZ Huffman packet header/table/payload parser composition.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizTable
import Exr.PizEntropy

namespace Exr.Piz.Packet

structure Header where
  first : Nat
  marker : Nat
  bitCount : Nat
  deriving Repr, DecidableEq

/-- The C reader ignores the advertised table byte count and reserved word;
its actual table parse determines the byte-aligned payload start. -/
def readHeader (bytes : Bytes) : Option Header := do
  let first ← getU32LE bytes 0
  let marker ← getU32LE bytes 4
  let bits ← getU32LE bytes 12
  pure ⟨first.toNat,marker.toNat,bits.toNat⟩

def Header.Valid (h : Header) : Prop :=
  h.first ≤ h.marker ∧ h.marker ≤ 65536 ∧ h.bitCount < 2147483648

instance (h : Header) : Decidable h.Valid := by
  unfold Header.Valid
  infer_instance

structure Parsed where
  header : Header
  lengths : List Nat
  payloadStart : Nat
  samples : List Nat
  deriving Repr, DecidableEq

def tableInput (bytes : Bytes) : List Bool := Bits.unpack ((bytes.extract 20 bytes.size).data.toList)

/-- Parse the nonempty Huffman stream used inside a compressed PIZ block.
All integer/header, output-count and bit-budget checks precede decoding. -/
def parseNonempty (bytes : Bytes) (count : Nat) : Option Parsed := do
  let header ← readHeader bytes
  if 20 ≤ bytes.size ∧ header.Valid then
    let input := tableInput bytes
    let (table,rest) ← Table.readTable (header.marker-header.first+1) input
    let consumed := input.length-rest.length
    let start := 20+(consumed+7)/8
    if start ≤ bytes.size ∧ header.bitCount ≤ 8*(bytes.size-start) then
      let lengths := List.replicate header.first 0 ++ table
      let payload := (Bits.unpack ((bytes.extract start bytes.size).data.toList)).take header.bitCount
      let samples ← Entropy.decode lengths header.marker count payload
      pure ⟨header,lengths,start,samples⟩
    else none
  else none

def empty : Parsed := ⟨⟨0,0,0⟩,[],0,[]⟩

/-- C handles the zero-output case before inspecting a header. -/
def parse (bytes : Bytes) (count : Nat) : Option Parsed :=
  if count = 0 then if bytes.size = 0 then some empty else none
  else parseNonempty bytes count

theorem payload_length (bytes : Bytes) (start bits : Nat)
    (hb : bits ≤ 8*(bytes.size-start)) :
    ((Bits.unpack ((bytes.extract start bytes.size).data.toList)).take bits).length = bits := by
  rw [List.length_take, Bits.unpack_length]
  have hl : ((bytes.extract start bytes.size).data.toList).length = bytes.size-start := by
    simp only [Array.length_toList, ByteArray.size_data, ByteArray.size_extract, Nat.min_self]
  rw [hl, Nat.min_eq_left hb]

/-- Successful composition establishes the output count, alphabet and input
bounds, rather than trusting metadata or the table parser's advertised size. -/
theorem parseNonempty_sound (bytes : Bytes) (count : Nat) (parsed : Parsed)
    (hp : parseNonempty bytes count = some parsed) :
    parsed.header.Valid ∧ parsed.payloadStart ≤ bytes.size ∧
      parsed.header.bitCount ≤ 8*(bytes.size-parsed.payloadStart) ∧
      parsed.lengths.length = parsed.header.marker+1 ∧
      parsed.samples.length = count ∧ (∀ sample ∈ parsed.samples, sample < parsed.header.marker) := by
  unfold parseNonempty at hp
  cases hh : readHeader bytes with
  | none => simp [hh] at hp
  | some header =>
    by_cases hv : 20 ≤ bytes.size ∧ header.Valid
    · cases ht : Table.readTable (header.marker-header.first+1) (tableInput bytes) with
      | none => simp [hh,hv,ht] at hp
      | some pair =>
        rcases pair with ⟨table,rest⟩
        let start := 20+((tableInput bytes).length-rest.length+7)/8
        by_cases hb : start ≤ bytes.size ∧ header.bitCount ≤ 8*(bytes.size-start)
        · let lengths := List.replicate header.first 0 ++ table
          let payload := (Bits.unpack ((bytes.extract start bytes.size).data.toList)).take header.bitCount
          cases hd : Entropy.decode lengths header.marker count payload with
          | none =>
            have hdn := hd
            simp [lengths,payload,start] at hdn
            simp [hh,hv,ht,hb,start,hdn] at hp
          | some samples =>
            have hdn := hd
            simp [lengths,payload,start] at hdn
            have he : (⟨header,lengths,start,samples⟩ : Parsed) = parsed := by
              simpa [hh,hv,ht,hb,start,hdn] using hp
            rw [← he]
            have hl := Table.readTableGo_size (header.marker-header.first+1) _ (tableInput bytes) table rest ht
            have hs := Entropy.decode_sound lengths header.marker count payload samples hd
            refine ⟨hv.2,hb.1,hb.2,?_,hs.1,hs.2⟩
            simp only [lengths, List.length_append, List.length_replicate]
            have hfirst := hv.2.1
            omega
        · simp [hh,hv,ht,hb, start] at hp
    · simp [hh,hv] at hp

theorem parse_size (bytes : Bytes) (count : Nat) (parsed : Parsed)
    (hp : parse bytes count = some parsed) : parsed.samples.length = count := by
  by_cases hz : count = 0
  · unfold parse at hp
    rw [ite_eq_left hz] at hp
    split at hp
    · cases Option.some.inj hp
      exact hz.symm
    · simp at hp
  · exact (parseNonempty_sound bytes count parsed (by simpa [parse,hz] using hp)).2.2.2.2.1

end Exr.Piz.Packet
