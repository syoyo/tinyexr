/-
  TinyEXR - PIZ Huffman packet serialization and parser round trip.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizPacket

namespace Exr.Piz.Packet

def word (n : Nat) : Bytes := putU32LE (UInt32.ofNat n) ByteArray.empty

@[simp] theorem word_size (n : Nat) : (word n).size = 4 := by
  simp [word, putU32LE]

def headerBytes (h : Header) (tableSize : Nat) : Bytes :=
  word h.first ++ (word h.marker ++ (word tableSize ++ (word h.bitCount ++ word 0)))

@[simp] theorem headerBytes_size (h : Header) (tableSize : Nat) :
    (headerBytes h tableSize).size = 20 := by simp [headerBytes]

def listBytes (xs : List UInt8) : Bytes := ByteArray.mk xs.toArray

@[simp] theorem listBytes_size (xs : List UInt8) : (listBytes xs).size = xs.length := by
  simp only [listBytes, ByteArray.size, List.size_toArray]

@[simp] theorem listBytes_list (xs : List UInt8) : (listBytes xs).data.toList = xs := by
  simp only [listBytes, List.toList_toArray]

def assemble (first marker : Nat) (table : List Nat) (bits : List Bool) : Bytes :=
  let tableBytes := Huffman.tableBytes table
  headerBytes ⟨first,marker,bits.length⟩ tableBytes.length ++
    (listBytes tableBytes ++ listBytes (Huffman.packBits bits))

def emitNonempty (first marker : Nat) (table samples : List Nat) : Bytes :=
  assemble first marker table (Huffman.payloadBits (List.replicate first 0 ++ table) samples marker)

def emit (first marker : Nat) (table samples : List Nat) : Bytes :=
  if samples.isEmpty then ByteArray.empty else emitNonempty first marker table samples

theorem read_word (n : Nat) (tail : Bytes) :
    getU32LE (word n ++ tail) 0 = some (UInt32.ofNat n) :=
  getU32LE_u32Bytes_append _ _

theorem read_after_word (n : Nat) (tail : Bytes) (j : Nat) :
    getU32LE (word n ++ tail) (4+j) = getU32LE tail j := by
  simpa only [word_size] using getU32LE_append_right' (a := word n) (b := tail) j

theorem readHeader_headerBytes (h : Header) (tableSize : Nat) (tail : Bytes)
    (hv : h.Valid) : readHeader (headerBytes h tableSize ++ tail) = some h := by
  have hf : h.first < 4294967296 := by have := hv.1; have := hv.2.1; omega
  have hm : h.marker < 4294967296 := by have := hv.2.1; omega
  have hb : h.bitCount < 4294967296 := by have := hv.2.2; omega
  unfold readHeader headerBytes
  simp only [ByteArray.append_assoc]
  rw [read_word, show 4 = 4+0 from rfl, read_after_word, read_word,
    show 12 = 4+8 from rfl, read_after_word,
    show 8 = 4+4 from rfl, read_after_word,
    show 4 = 4+0 from rfl, read_after_word, read_word]
  change some (⟨(UInt32.ofNat h.first).toNat,(UInt32.ofNat h.marker).toNat,
    (UInt32.ofNat h.bitCount).toNat⟩ : Header) = some h
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hb]

theorem unpack_append (a b : List UInt8) : Bits.unpack (a ++ b) = Bits.unpack a ++ Bits.unpack b := by
  simp only [Bits.unpack, List.flatMap_append]

theorem packed_size (bits : List Bool) : (Huffman.packBits bits).length = (bits.length+7)/8 := by
  have he := congrArg List.length (Bits.unpack_packBits bits)
  simp only [Bits.unpack_length, List.length_append, List.length_replicate] at he
  omega

theorem assemble_size (first marker : Nat) (table : List Nat) (bits : List Bool) :
    (assemble first marker table bits).size =
      20+(Huffman.tableBytes table).length+(Huffman.packBits bits).length := by
  simp [assemble, Nat.add_assoc]

theorem assemble_table_suffix (first marker : Nat) (table : List Nat) (bits : List Bool) :
    (assemble first marker table bits).extract 20 (assemble first marker table bits).size =
      listBytes (Huffman.tableBytes table) ++ listBytes (Huffman.packBits bits) := by
  exact (by simpa only [assemble, headerBytes_size, ByteArray.size_append] using
    (extract_append_right_eq (a := headerBytes ⟨first,marker,bits.length⟩ (Huffman.tableBytes table).length)
      (b := listBytes (Huffman.tableBytes table) ++ listBytes (Huffman.packBits bits))))

theorem assemble_payload_suffix (first marker : Nat) (table : List Nat) (bits : List Bool) :
    (assemble first marker table bits).extract (20+(Huffman.tableBytes table).length)
      (assemble first marker table bits).size = listBytes (Huffman.packBits bits) := by
  have he := extract_append_right_eq
    (a := headerBytes ⟨first,marker,bits.length⟩ (Huffman.tableBytes table).length ++
      listBytes (Huffman.tableBytes table))
    (b := listBytes (Huffman.packBits bits))
  simpa only [assemble, ByteArray.append_assoc, ByteArray.size_append, headerBytes_size,
    listBytes_size, Nat.add_assoc] using he

theorem tableInput_assemble (first marker : Nat) (table : List Nat) (bits : List Bool) :
    tableInput (assemble first marker table bits) =
      Huffman.tableBitsGo table.length table ++
        (List.replicate ((8-(Huffman.tableBitsGo table.length table).length%8)%8) false ++
          Bits.unpack (Huffman.packBits bits)) := by
  rw [tableInput, assemble_table_suffix]
  simp only [ByteArray.toList_data_append, listBytes_list, unpack_append,
    Huffman.tableBytes, Bits.unpack_packBits, List.append_assoc]

/-- Packet assembly preserves the actual table boundary and entropy budget.
The entropy premise is discharged by the greedy-writer inverse below. -/
theorem parseNonempty_assemble (first marker : Nat) (table : List Nat)
    (bits : List Bool) (samples : List Nat)
    (hv : (⟨first,marker,bits.length⟩ : Header).Valid)
    (hl : table.length = marker-first+1)
    (ht : ∀ depth ∈ table, depth < 59)
    (hd : Entropy.decode (List.replicate first 0 ++ table) marker samples.length bits = some samples) :
    parseNonempty (assemble first marker table bits) samples.length =
      some ⟨⟨first,marker,bits.length⟩,List.replicate first 0 ++ table,
        20+(Huffman.tableBytes table).length,samples⟩ := by
  let bytes := assemble first marker table bits
  let padding := List.replicate ((8-(Huffman.tableBitsGo table.length table).length%8)%8) false
  let suffix := padding ++ Bits.unpack (Huffman.packBits bits)
  have hh : readHeader bytes = some ⟨first,marker,bits.length⟩ :=
    readHeader_headerBytes _ _ _ hv
  have htable : Table.readTable (marker-first+1) (tableInput bytes) = some (table,suffix) := by
    rw [tableInput_assemble, ← hl]
    exact Table.readTable_tableBits table _ ht
  have hstart : 20+((tableInput bytes).length-suffix.length+7)/8 =
      20+(Huffman.tableBytes table).length := by
    rw [tableInput_assemble]
    dsimp only [suffix,padding]
    simp only [List.length_append, Nat.add_sub_cancel_right]
    rw [Huffman.tableBytes, packed_size]
  have hsize : bytes.size = 20+(Huffman.tableBytes table).length+(Huffman.packBits bits).length :=
    assemble_size first marker table bits
  have hpacked : bits.length ≤ 8*(Huffman.packBits bits).length := by
    have he := congrArg List.length (Bits.unpack_packBits bits)
    simp only [Bits.unpack_length,List.length_append,List.length_replicate] at he
    omega
  have hbudget : 20+(Huffman.tableBytes table).length ≤ bytes.size ∧
      bits.length ≤ 8*(bytes.size-(20+(Huffman.tableBytes table).length)) := by
    rw [hsize]
    omega
  have hpayload : (Bits.unpack ((bytes.extract (20+(Huffman.tableBytes table).length)
      bytes.size).data.toList)).take bits.length = bits := by
    rw [assemble_payload_suffix, listBytes_list, Bits.unpack_packBits]
    simp
  have hvalid : 20 ≤ bytes.size ∧ (⟨first,marker,bits.length⟩ : Header).Valid :=
    ⟨by omega,hv⟩
  change parseNonempty bytes samples.length = _
  simp only [parseNonempty, hh]
  change (if 20 ≤ bytes.size ∧ (⟨first,marker,bits.length⟩ : Header).Valid then _ else none) = _
  rw [ite_eq_left hvalid]
  simp only [htable]
  change (if 20+((tableInput bytes).length-suffix.length+7)/8 ≤ bytes.size ∧
      bits.length ≤ 8*(bytes.size-(20+((tableInput bytes).length-suffix.length+7)/8)) then _ else none) = _
  rw [hstart, ite_eq_left hbudget]
  simp only [hpayload, hd]
  rfl

/-- Complete packet emitter/parser round trip for a representable sliced
table and its checked canonical codebook. No external path/tree oracle is
required: the actual greedy entropy inverse supplies the decoding premise. -/
theorem parse_emit_nonempty (first marker : Nat) (table samples : List Nat)
    (trie : Codebook.Trie) (hn : samples ≠ [])
    (hf : first ≤ marker) (hm : marker ≤ 65536)
    (hl : table.length = marker-first+1) (ht : ∀ depth ∈ table, depth < 59)
    (hb : Codebook.build (List.replicate first 0 ++ table) = some trie)
    (hs : Entropy.SourceValid (List.replicate first 0 ++ table) marker samples)
    (hbudget : (Huffman.payloadBits (List.replicate first 0 ++ table) samples marker).length < 2147483648) :
    parse (emit first marker table samples) samples.length =
      some ⟨⟨first,marker,(Huffman.payloadBits (List.replicate first 0 ++ table) samples marker).length⟩,
        List.replicate first 0 ++ table,20+(Huffman.tableBytes table).length,samples⟩ := by
  have hz : samples.length ≠ 0 := fun hz => hn (List.length_eq_zero_iff.mp hz)
  have he : samples.isEmpty = false := by cases samples <;> simp_all
  have hd := Entropy.decode_payloadBits (List.replicate first 0 ++ table) marker samples trie hb hs
  have hr := parseNonempty_assemble first marker table
    (Huffman.payloadBits (List.replicate first 0 ++ table) samples marker) samples
    ⟨hf,hm,hbudget⟩ hl ht hd
  simpa only [emit,he,Bool.false_eq_true,ite_false,parse,hz,emitNonempty] using hr

theorem parse_emit_empty (first marker : Nat) (table : List Nat) : parse (emit first marker table []) 0 = some empty := by
  simp [emit,parse]

end Exr.Piz.Packet
