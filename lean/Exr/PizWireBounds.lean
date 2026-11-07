/-
  TinyEXR - PIZ table/payload wire budgets derived from source sizes.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizPacketEmit

namespace Exr.Piz.Huffman

theorem zeroRunBits_length_bound (count : Nat) (hc : 0 < count) :
    (zeroRunBits count).length ≤ 6*count := by
  unfold zeroRunBits
  split
  · simp only [List.length_append,Bits.codeBits_length]
    omega
  · split <;> simp only [Bits.codeBits_length] <;> omega

theorem tableBitsGo_length_bound (fuel : Nat) (lengths : List Nat) :
    (tableBitsGo fuel lengths).length ≤ 6*lengths.length := by
  induction fuel generalizing lengths with
  | zero => simp [tableBitsGo]
  | succ fuel ih =>
    cases lengths with
    | nil => simp [tableBitsGo]
    | cons depth rest =>
      dsimp only [tableBitsGo]
      split
      · let extra := min 260 (rest.takeWhile (· == 0)).length
        have he : extra ≤ rest.length := by
          have ht : (rest.takeWhile (· == 0)).length ≤ rest.length := (List.takeWhile_sublist (l := rest) _).length_le
          exact Nat.le_trans (Nat.min_le_right _ _) ht
        have hr := ih (rest.drop extra)
        have hb := zeroRunBits_length_bound (extra+1) (by omega)
        change (zeroRunBits (extra+1) ++ tableBitsGo fuel (rest.drop extra)).length ≤ _
        simp only [List.length_append,List.length_drop,List.length_cons] at *
        omega
      · have hr := ih rest
        simp only [List.length_append,Bits.codeBits_length,List.length_cons]
        omega

theorem runBits_length_bound (symbolCode runCode extra : Nat) :
    (runBits symbolCode runCode extra).length ≤ 63*(extra+1) := by
  have hd : symbolCode%64 ≤ 63 := by omega
  have hm := Nat.mul_le_mul_right (extra+1) hd
  dsimp only [runBits]
  split
  · simp only [List.length_append,Bits.codeBits_length]
    have he : symbolCode%64*(extra+1) = symbolCode%64*extra+symbolCode%64 := Nat.mul_succ _ _
    omega
  · simp only [List.length_flatten,List.map_replicate,Bits.codeBits_length,List.sum_replicate_nat]
    simpa only [Nat.mul_comm] using hm

theorem payloadBitsGo_length_bound (table : List Nat) (runCode fuel : Nat) (symbols : List Nat) :
    (payloadBitsGo table runCode fuel symbols).length ≤ 63*symbols.length := by
  induction fuel generalizing symbols with
  | zero => simp [payloadBitsGo]
  | succ fuel ih =>
    cases symbols with
    | nil => simp [payloadBitsGo]
    | cons symbol rest =>
      let extra := min 255 (rest.takeWhile (· == symbol)).length
      have he : extra ≤ rest.length := by
        have ht : (rest.takeWhile (· == symbol)).length ≤ rest.length := (List.takeWhile_sublist (l := rest) _).length_le
        exact Nat.le_trans (Nat.min_le_right _ _) ht
      have hr := ih (rest.drop extra)
      have hb := runBits_length_bound (table.getD symbol 0) runCode extra
      change (runBits (table.getD symbol 0) runCode extra ++ payloadBitsGo table runCode fuel (rest.drop extra)).length ≤ _
      simp only [List.length_append,List.length_drop,List.length_cons] at *
      omega

theorem payloadBits_length_bound (lengths symbols : List Nat) (marker : Nat) :
    (payloadBits lengths symbols marker).length ≤ 63*symbols.length :=
  payloadBitsGo_length_bound _ _ _ _

/-- C caps source words at INT_MAX/64 before Huffman emission. The greedy
writer consequently fits its signed 31-bit payload budget without truncation. -/
theorem payloadBits_signed_budget (lengths symbols : List Nat) (marker : Nat)
    (hs : symbols.length ≤ 33554431) : (payloadBits lengths symbols marker).length < 2147483648 := by
  have hb := payloadBits_length_bound lengths symbols marker
  omega

end Exr.Piz.Huffman

namespace Exr.Piz.Packet

/-- Source and alphabet limits imply the outer 32-bit Huffman byte extent;
no independent serialized-size assumption is needed by full block emission. -/
theorem emit_size_bound (first marker : Nat) (table symbols : List Nat)
    (ht : table.length ≤ 65537) (hs : symbols.length ≤ 33554431) :
    (emit first marker table symbols).size < 4294967296 := by
  by_cases hn : symbols.isEmpty = true
  · simp only [emit,hn,ite_true,ByteArray.size_empty]
    decide
  · have he : symbols.isEmpty = false := Bool.eq_false_iff.mpr hn
    simp only [emit,he,Bool.false_eq_true,ite_false,emitNonempty,assemble_size]
    have htable := Huffman.tableBitsGo_length_bound table.length table
    have htableBytes : (Huffman.tableBytes table).length ≤ 49153 := by
      rw [Huffman.tableBytes,packed_size]
      omega
    have hbits := Huffman.payloadBits_signed_budget (List.replicate first 0 ++ table) symbols marker hs
    have hbytes : (Huffman.packBits (Huffman.payloadBits (List.replicate first 0 ++ table) symbols marker)).length ≤ 268435456 := by
      rw [packed_size]
      omega
    omega

end Exr.Piz.Packet
