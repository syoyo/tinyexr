/-
  TinyEXR - PIZ Huffman length-table parser and token composition proofs.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizBits

namespace Exr.Piz.Table

inductive Token where
  | literal (length : Nat)
  | zeros (count : Nat)
  deriving Repr, DecidableEq

def Token.Valid : Token → Prop
  | .literal n => n < 59
  | .zeros n => 2 ≤ n ∧ n ≤ 261

def Token.values : Token → List Nat
  | .literal n => [n]
  | .zeros n => List.replicate n 0

def Token.bits : Token → List Bool
  | .literal n => Huffman.codeBits 6 n
  | .zeros n => Huffman.zeroRunBits n

def readToken (bits : List Bool) : Option (Token × List Bool) := do
  let (field, rest) ← Bits.read 6 bits
  if field = 63 then
    let (extra, tail) ← Bits.read 8 rest
    pure (.zeros (extra+6), tail)
  else if 59 ≤ field then pure (.zeros (field-57), rest)
  else pure (.literal field, rest)

theorem readToken_literal (n : Nat) (suffix : List Bool) (hn : n < 59) :
    readToken (Token.bits (.literal n) ++ suffix) = some (.literal n, suffix) := by
  have hr := Bits.read_codeBits 6 n suffix (by omega)
  simp [readToken, Token.bits, hr, show n ≠ 63 by omega, show ¬ 59 ≤ n by omega]

theorem readToken_zeros (n : Nat) (suffix : List Bool) (hn : 2 ≤ n) (hm : n ≤ 261) :
    readToken (Token.bits (.zeros n) ++ suffix) = some (.zeros n, suffix) := by
  by_cases hl : 6 ≤ n
  · have h63 := Bits.read_codeBits 6 63 (Huffman.codeBits 8 (n-6) ++ suffix) (by decide)
    have h8 := Bits.read_codeBits 8 (n-6) suffix (by omega)
    simp only [Token.bits, Huffman.zeroRunBits, ite_eq_left hl, List.append_assoc]
    simp [readToken, h63, h8, show n-6+6=n by omega]
  · have hs := Bits.read_codeBits 6 (59+n-2) suffix (by omega)
    have hv : 59+n-2 ≠ 63 := by omega
    have hb : 59 ≤ 59+n-2 := by omega
    simp only [Token.bits, Huffman.zeroRunBits, ite_eq_right hl, ite_eq_left hn]
    simp [readToken, hs, hv, hb, show 59+n-2-57=n by omega]

theorem readToken_bits (token : Token) (suffix : List Bool) (hv : token.Valid) :
    readToken (token.bits ++ suffix) = some (token,suffix) := by
  cases token with
  | literal n => exact readToken_literal n suffix hv
  | zeros n => exact readToken_zeros n suffix hv.1 hv.2

theorem Token.values_pos (token : Token) (hv : token.Valid) : 0 < token.values.length := by
  cases token <;> simp only [Token.values, List.length_cons, List.length_nil,
    List.length_replicate, Token.Valid] at * <;> omega

theorem readToken_sound (bits : List Bool) (token : Token) (suffix : List Bool)
    (hr : readToken bits = some (token,suffix)) :
    token.Valid ∧ ∃ consumed, 6 ≤ consumed ∧ suffix.length + consumed = bits.length := by
  cases h6 : Bits.read 6 bits with
  | none => simp [readToken, h6] at hr
  | some pair =>
    rcases pair with ⟨field,tail⟩
    have hb6 := Bits.read_bounds 6 bits field tail h6
    by_cases h63 : field = 63
    · cases h8 : Bits.read 8 tail with
      | none => simp [readToken, h6, h63, h8] at hr
      | some pair =>
        rcases pair with ⟨extra,rest⟩
        have he : (Token.zeros (extra+6),rest) = (token,suffix) := by
          simpa [readToken, h6, h63, h8] using hr
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        have hb8 := Bits.read_bounds 8 tail extra rest h8
        refine ⟨⟨by omega, by omega⟩, 14, by omega, by omega⟩
    · by_cases h59 : 59 ≤ field
      · have he : (Token.zeros (field-57),tail) = (token,suffix) := by
          simpa [readToken, h6, h63, h59] using hr
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        exact ⟨⟨by omega, by omega⟩, 6, by omega, by omega⟩
      · have he : (Token.literal field,tail) = (token,suffix) := by
          simpa [readToken, h6, h63, h59] using hr
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        exact ⟨by dsimp [Token.Valid]; omega, 6, by omega, by omega⟩

theorem Token.values_bound (token : Token) (hv : token.Valid) :
    ∀ value ∈ token.values, value ≤ 58 := by
  cases token with
  | literal n =>
    intro value hm
    have he : value = n := List.mem_singleton.mp hm
    rw [he]
    dsimp [Token.Valid] at hv
    omega
  | zeros n =>
    intro value hm
    have he : value = 0 := (List.mem_replicate.mp hm).2
    omega

/-- Remaining output slots bound both work and zero-run expansion. The
reader rejects a zero run that would cross iM rather than clamping it. -/
def readTableGo : Nat → Nat → List Bool → Option (List Nat × List Bool)
  | _, 0, bits => some ([], bits)
  | 0, _+1, _ => none
  | fuel+1, remaining+1, bits => do
    let (token, tail) ← readToken bits
    let values := token.values
    if 0 < values.length ∧ values.length ≤ remaining+1 then
      let (rest, suffix) ← readTableGo fuel (remaining+1-values.length) tail
      pure (values ++ rest, suffix)
    else none

def readTable (count : Nat) (bits : List Bool) : Option (List Nat × List Bool) :=
  readTableGo count count bits

theorem readTableGo_size (fuel remaining : Nat) (bits : List Bool)
    (values : List Nat) (suffix : List Bool)
    (hr : readTableGo fuel remaining bits = some (values,suffix)) : values.length = remaining := by
  induction fuel generalizing remaining bits values suffix with
  | zero =>
    cases remaining with
    | zero =>
      have hv : ([] : List Nat) = values := congrArg Prod.fst (Option.some.inj hr)
      rw [← hv]
      rfl
    | succ n => simp [readTableGo] at hr
  | succ fuel ih =>
    cases remaining with
    | zero =>
      have hv : ([] : List Nat) = values := congrArg Prod.fst (Option.some.inj hr)
      rw [← hv]
      rfl
    | succ n =>
      cases ht : readToken bits with
      | none => simp [readTableGo, ht] at hr
      | some pair =>
        rcases pair with ⟨token,tail⟩
        by_cases hn : 0 < token.values.length ∧ token.values.length ≤ n+1
        · cases hs : readTableGo fuel (n+1-token.values.length) tail with
          | none => simp [readTableGo, ht, hn, hs] at hr
          | some pair =>
            rcases pair with ⟨rest,last⟩
            have he : (token.values ++ rest,last) = (values,suffix) := by
              simpa [readTableGo, ht, hn, hs] using hr
            have hlen := ih _ _ rest last hs
            have hv := congrArg (fun p => p.1.length) he
            simp only [List.length_append] at hv
            omega
        · simp [readTableGo, ht, hn] at hr

theorem readTableGo_bounds (fuel remaining : Nat) (bits : List Bool)
    (values : List Nat) (suffix : List Bool)
    (hr : readTableGo fuel remaining bits = some (values,suffix)) :
    suffix.length ≤ bits.length ∧ ∀ v ∈ values, v ≤ 58 := by
  induction fuel generalizing remaining bits values suffix with
  | zero =>
    cases remaining with
    | zero =>
      have he : ([],bits) = (values,suffix) := Option.some.inj hr
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp
    | succ n => simp [readTableGo] at hr
  | succ fuel ih =>
    cases remaining with
    | zero =>
      have he : ([],bits) = (values,suffix) := Option.some.inj hr
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      simp
    | succ n =>
      cases ht : readToken bits with
      | none => simp [readTableGo, ht] at hr
      | some pair =>
        rcases pair with ⟨token,tail⟩
        have htoken := readToken_sound bits token tail ht
        by_cases hn : 0 < token.values.length ∧ token.values.length ≤ n+1
        · cases hs : readTableGo fuel (n+1-token.values.length) tail with
          | none => simp [readTableGo, ht, hn, hs] at hr
          | some pair =>
            rcases pair with ⟨rest,last⟩
            have he : (token.values ++ rest,last) = (values,suffix) := by
              simpa [readTableGo, ht, hn, hs] using hr
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
            have hb := ih _ _ rest last hs
            obtain ⟨consumed, _, hconsumed⟩ := htoken.2
            refine ⟨by omega, ?_⟩
            intro v hm
            rcases List.mem_append.mp hm with hm | hm
            · exact Token.values_bound token htoken.1 v hm
            · exact hb.2 v hm
        · simp [readTableGo, ht, hn] at hr

/-- Composition of arbitrary valid length tokens, preserving any suffix.
This covers literal lengths, short zero runs and long zero runs uniformly. -/
theorem readTableGo_tokens (tokens : List Token) (suffix : List Bool)
    (hv : ∀ t ∈ tokens, t.Valid) (fuel : Nat) (hf : tokens.length ≤ fuel) :
    readTableGo fuel (tokens.flatMap Token.values).length
      (tokens.flatMap Token.bits ++ suffix) = some (tokens.flatMap Token.values, suffix) := by
  induction tokens generalizing fuel with
  | nil => simp [readTableGo]
  | cons token rest ih =>
    have ht := hv token List.mem_cons_self
    have hp := Token.values_pos token ht
    have hr : ∀ t ∈ rest, t.Valid := fun t hm => hv t (List.mem_cons_of_mem token hm)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1, by simp only [List.length_cons] at hf; omega⟩
    have hfr : rest.length ≤ f := by simp only [List.length_cons] at hf; omega
    simp only [List.flatMap_cons, List.length_append, List.append_assoc]
    have hcount : token.values.length + (rest.flatMap Token.values).length =
        (token.values.length + (rest.flatMap Token.values).length - 1)+1 := by omega
    rw [hcount, readTableGo, readToken_bits token _ ht]
    have hfit : 0 < token.values.length ∧ token.values.length ≤
        token.values.length + (rest.flatMap Token.values).length - 1 + 1 := by omega
    change (if 0 < token.values.length ∧ token.values.length ≤
        token.values.length + (rest.flatMap Token.values).length - 1 + 1 then
      (do
        let result ← readTableGo f
          (token.values.length + (rest.flatMap Token.values).length - 1 + 1 - token.values.length)
          (rest.flatMap Token.bits ++ suffix)
        pure (token.values ++ result.1,result.2)) else none) = _
    rw [ite_eq_left hfit]
    have hsub : token.values.length + (rest.flatMap Token.values).length - 1 + 1 - token.values.length =
        (rest.flatMap Token.values).length := by omega
    rw [hsub]
    have hi := ih hr f hfr
    change (do
      let result ← readTableGo f (rest.flatMap Token.values).length (rest.flatMap Token.bits ++ suffix)
      pure (token.values ++ result.1,result.2)) = _
    rw [hi]
    rfl

/-- A run of one zero is represented by the literal zero field. -/
def zeroToken (count : Nat) : Token := if count = 1 then .literal 0 else .zeros count

theorem zeroToken_valid (count : Nat) (hp : 0 < count) (hb : count ≤ 261) :
    (zeroToken count).Valid := by
  by_cases h : count = 1
  · simp [zeroToken, h, Token.Valid]
  · simp only [zeroToken, ite_eq_right h, Token.Valid]
    omega

theorem zeroToken_values (count : Nat) :
    (zeroToken count).values = List.replicate count 0 := by
  by_cases h : count = 1
  · simp [zeroToken, h, Token.values]
  · simp [zeroToken, h, Token.values]

theorem zeroToken_bits (count : Nat) :
    (zeroToken count).bits = Huffman.zeroRunBits count := by
  by_cases h : count = 1
  · simp [zeroToken, h, Token.bits, Huffman.zeroRunBits]
  · simp [zeroToken, h, Token.bits]

def tokensGo : Nat → List Nat → List Token
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, depth :: rest =>
    if depth = 0 then
      let extra := min 260 (rest.takeWhile (· == 0)).length
      zeroToken (extra+1) :: tokensGo fuel (rest.drop extra)
    else .literal depth :: tokensGo fuel rest

theorem tokensGo_bits (fuel : Nat) (lengths : List Nat) :
    (tokensGo fuel lengths).flatMap Token.bits = Huffman.tableBitsGo fuel lengths := by
  induction fuel generalizing lengths with
  | zero => rfl
  | succ fuel ih =>
    cases lengths with
    | nil => rfl
    | cons depth rest =>
      by_cases hz : depth = 0
      · simp [tokensGo, Huffman.tableBitsGo, hz, ih, zeroToken_bits]
      · simp [tokensGo, Huffman.tableBitsGo, hz, ih, Token.bits]

theorem tokensGo_valid (fuel : Nat) (lengths : List Nat) (hv : ∀ n ∈ lengths, n < 59) :
    ∀ token ∈ tokensGo fuel lengths, token.Valid := by
  induction fuel generalizing lengths with
  | zero => simp [tokensGo]
  | succ fuel ih =>
    cases lengths with
    | nil => simp [tokensGo]
    | cons depth rest =>
      have ht : ∀ n ∈ rest, n < 59 := fun n hn => hv n (List.mem_cons_of_mem depth hn)
      by_cases hz : depth = 0
      · rw [tokensGo, ite_eq_left hz]
        intro token hm
        rcases List.mem_cons.mp hm with he | hm
        · subst token
          apply zeroToken_valid
          · omega
          · have hb := Nat.min_le_left 260 (rest.takeWhile (· == 0)).length
            omega
        · apply ih (rest.drop (min 260 (rest.takeWhile (· == 0)).length))
            (fun n hn => ht n (List.mem_of_mem_drop hn)) token hm
      · rw [tokensGo, ite_eq_right hz]
        intro token hm
        rcases List.mem_cons.mp hm with he | hm
        · subst token
          exact hv depth List.mem_cons_self
        · exact ih rest ht token hm

private theorem takeWhile_zeros (values : List Nat) :
    values.takeWhile (· == 0) = List.replicate (values.takeWhile (· == 0)).length 0 := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    by_cases hz : n = 0
    · subst n
      simpa [List.takeWhile_cons, List.replicate_succ] using congrArg (0 :: ·) ih
    · simp [hz]

private theorem take_zero_prefix (values : List Nat) (count : Nat)
    (hc : count ≤ (values.takeWhile (· == 0)).length) :
    values.take count = List.replicate count 0 := by
  have hp : values = values.takeWhile (· == 0) ++ values.dropWhile (· == 0) :=
    List.takeWhile_append_dropWhile.symm
  calc
    values.take count = (values.takeWhile (· == 0) ++ values.dropWhile (· == 0)).take count :=
      congrArg (List.take count) hp
    _ = (values.takeWhile (· == 0)).take count := List.take_append_of_le_length hc
    _ = List.replicate count 0 := by
      rw [takeWhile_zeros, List.take_replicate, Nat.min_eq_left hc]

/-- The greedy tokenization consumes every length, including zero runs split
at the maximum 261-symbol run. Fuel is bounded by input length. -/
theorem tokensGo_values (fuel : Nat) (lengths : List Nat) (hf : lengths.length ≤ fuel) :
    (tokensGo fuel lengths).flatMap Token.values = lengths := by
  induction fuel generalizing lengths with
  | zero =>
    have hl : lengths = [] := List.length_eq_zero_iff.mp (by omega)
    subst lengths
    rfl
  | succ fuel ih =>
    cases lengths with
    | nil => rfl
    | cons depth rest =>
      have hf' : rest.length ≤ fuel := by simp only [List.length_cons] at hf; omega
      by_cases hz : depth = 0
      · subst depth
        let extra := min 260 (rest.takeWhile (· == 0)).length
        have hd : (rest.drop extra).length ≤ fuel := by rw [List.length_drop]; omega
        have hp : rest.take extra = List.replicate extra 0 :=
          take_zero_prefix rest extra (Nat.min_le_right _ _)
        simp only [tokensGo, ite_true, List.flatMap_cons, zeroToken_values]
        change List.replicate (extra+1) 0 ++ (tokensGo fuel (rest.drop extra)).flatMap Token.values = _
        rw [ih _ hd, List.replicate_succ, List.cons_append, ← hp, List.take_append_drop]
      · simp [tokensGo, hz, Token.values, ih rest hf']

theorem tokensGo_length_le (fuel : Nat) (lengths : List Nat) :
    (tokensGo fuel lengths).length ≤ fuel := by
  induction fuel generalizing lengths with
  | zero => simp [tokensGo]
  | succ fuel ih =>
    cases lengths with
    | nil => simp [tokensGo]
    | cons depth rest =>
      by_cases hz : depth = 0 <;> simp only [tokensGo, hz, ite_true, ite_false, List.length_cons]
      · have h := ih (rest.drop (min 260 (rest.takeWhile (· == 0)).length))
        omega
      · have h := ih rest
        omega

/-- The actual greedy table-bit emitter and parser are inverse, for arbitrary
representable length tables and arbitrary following payload bits. -/
theorem readTable_tableBits (lengths : List Nat) (suffix : List Bool)
    (hv : ∀ n ∈ lengths, n < 59) :
    readTable lengths.length (Huffman.tableBitsGo lengths.length lengths ++ suffix) =
      some (lengths,suffix) := by
  have hr := readTableGo_tokens (tokensGo lengths.length lengths) suffix
    (tokensGo_valid lengths.length lengths hv) lengths.length (tokensGo_length_le _ _)
  rw [tokensGo_bits, tokensGo_values _ _ (Nat.le_refl _)] at hr
  exact hr

/-- Byte serialization preserves the table, leaving only the explicit
terminal bit padding. The enclosing Huffman parser starts payload at the
next byte, as the C reader does. -/
theorem readTable_tableBytes (lengths : List Nat) (hv : ∀ n ∈ lengths, n < 59) :
    readTable lengths.length (Bits.unpack (Huffman.tableBytes lengths)) =
      some (lengths, List.replicate
        ((8-(Huffman.tableBitsGo lengths.length lengths).length%8)%8) false) := by
  rw [Huffman.tableBytes, Bits.unpack_packBits]
  exact readTable_tableBits lengths _ hv

end Exr.Piz.Table
