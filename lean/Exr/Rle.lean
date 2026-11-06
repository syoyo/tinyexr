/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  RLE codec model (`exr_rle.c`): the byte-run compressor shared by the RLE
  and ZIP code paths, together with the predictor and even/odd interleave
  reconstruction passes.  The model is validated byte-exactly against the C
  implementation by the differential harness (`test/v3/codec_diff.c`).

  Wire format (signed count byte):
  * count < 0 (byte >= 128): the next `-count` bytes are literals;
  * count >= 0 (byte < 128): the next byte is repeated `count + 1` times.

  After run expansion the ZIP/RLE reconstruction passes apply:
  * predictor: each byte holds (delta + 128) vs the previous byte;
  * interleave: source is the even-byte half followed by the odd-byte half.

  The compressor is greedy (runs of length >= 3 and <= 128; literal runs
  that stop before a 3-run and cap at 127) and falls back to storing the
  raw block when the encoded stream would not shrink it, which the C
  reader's size fast-path relies on.  This module models the greedy encoder
  bit-exactly, proves the run-level round trip, and accounts for the
  fallback's size cap.  Decompression of a *foreign* RLE stream whose
  encoded length coincides with the uncompressed size would take the C
  reader's memcpy fast path instead of run-decoding; that size-based
  dispatch is modelled as a separate decode branch and documented as a
  tinyexr behaviour quirk (OpenEXR always run-decodes).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Size

namespace Exr

namespace Rle

/-! ## Even/odd interleave -/

/-- Even/odd split of a byte stream (EXR interleave, encode direction). -/
def interleaveEncode (xs : List UInt8) : List UInt8 :=
  (List.range ((xs.length + 1) / 2)).map (fun i => xs.getD (2 * i) 0)
    ++ (List.range (xs.length / 2)).map (fun i => xs.getD (2 * i + 1) 0)

/-- Rebuild the interleaved stream from the even/odd halves. -/
def interleaveDecode (ys : List UInt8) : List UInt8 :=
  (List.range ys.length).map (fun i =>
    if i % 2 = 0 then ys.getD (i / 2) 0
    else ys.getD ((ys.length + 1) / 2 + i / 2) 0)

theorem interleaveEncode_length (xs : List UInt8) :
    (interleaveEncode xs).length = xs.length := by
  unfold interleaveEncode
  rw [List.length_append, List.length_map, List.length_map, List.length_range,
    List.length_range]
  omega

theorem interleaveDecode_length (ys : List UInt8) :
    (interleaveDecode ys).length = ys.length := by
  unfold interleaveDecode
  rw [List.length_map, List.length_range]

/-- The get? of a range-map at an in-range index. -/
theorem getElem?_range_map {f : Nat → UInt8} {m i : Nat} (h : i < m) :
    ((List.range m).map f)[i]? = some (f i) := by
  rw [List.getElem?_map, List.getElem?_range h, Option.map_some]

/-- getD of an interleave-encoded stream at a left-half index. -/
theorem getD_encode_left {xs : List UInt8} {j : Nat}
    (h : j < (xs.length + 1) / 2) :
    (interleaveEncode xs).getD j 0 = xs.getD (2 * j) 0 := by
  rw [List.getD_eq_getElem?_getD]
  unfold interleaveEncode
  rw [List.getElem?_append]
  have hleftlen : ((List.range ((xs.length + 1) / 2)).map fun i => xs.getD (2 * i) 0).length
      = (xs.length + 1) / 2 := by
    rw [List.length_map, List.length_range]
  rw [ite_eq_left (by rw [hleftlen]; exact h), getElem?_range_map h, Option.getD_some]

/-- getD of an interleave-encoded stream at a right-half index. -/
theorem getD_encode_right {xs : List UInt8} {j : Nat}
    (h : (xs.length + 1) / 2 ≤ j) (h2 : j < xs.length) :
    (interleaveEncode xs).getD j 0
      = xs.getD (2 * (j - (xs.length + 1) / 2) + 1) 0 := by
  rw [List.getD_eq_getElem?_getD]
  unfold interleaveEncode
  rw [List.getElem?_append]
  have hleftlen : ((List.range ((xs.length + 1) / 2)).map fun i => xs.getD (2 * i) 0).length
      = (xs.length + 1) / 2 := by
    rw [List.length_map, List.length_range]
  rw [ite_eq_right (by rw [hleftlen]; omega), hleftlen]
  have h3 : j - (xs.length + 1) / 2 < xs.length / 2 := by
    have hlen := interleaveEncode_length xs
    omega
  rw [getElem?_range_map h3, Option.getD_some]

theorem interleaveDecode_encode (xs : List UInt8) :
    interleaveDecode (interleaveEncode xs) = xs := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < xs.length
  · have hlen : (interleaveEncode xs).length = xs.length := interleaveEncode_length xs
    have h1 : ((List.range xs.length).map (fun i =>
          if i % 2 = 0 then (interleaveEncode xs).getD (i / 2) 0
          else (interleaveEncode xs).getD ((xs.length + 1) / 2 + i / 2) 0))[i]?
        = some (if i % 2 = 0 then (interleaveEncode xs).getD (i / 2) 0
            else (interleaveEncode xs).getD ((xs.length + 1) / 2 + i / 2) 0) :=
      getElem?_range_map hi
    unfold interleaveDecode
    rw [hlen, h1, List.getElem?_eq_getElem hi]
    by_cases he : i % 2 = 0
    · rw [ite_eq_left he]
      have hlt : i / 2 < (xs.length + 1) / 2 := by omega
      rw [getD_encode_left hlt]
      congr 1
      rw [show 2 * (i / 2) = i from by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, Option.getD_some]
    · rw [ite_eq_right he]
      have hge : (xs.length + 1) / 2 ≤ (xs.length + 1) / 2 + i / 2 := by omega
      have hlt : (xs.length + 1) / 2 + i / 2 < xs.length := by omega
      rw [getD_encode_right hge hlt]
      congr 1
      rw [show 2 * ((xs.length + 1) / 2 + i / 2 - (xs.length + 1) / 2) + 1 = i from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · have hlen : (interleaveEncode xs).length = xs.length := interleaveEncode_length xs
    unfold interleaveDecode
    rw [hlen, List.getElem?_eq_none (by
        rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt hi),
      List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- getD of an interleaved decode at an even index. -/
theorem getD_decode_even {ys : List UInt8} {k : Nat}
    (h : k < (ys.length + 1) / 2) :
    (interleaveDecode ys).getD (2 * k) 0 = ys.getD k 0 := by
  rw [List.getD_eq_getElem?_getD]
  unfold interleaveDecode
  rw [getElem?_range_map (by omega)]
  simp only [show (2 * k) % 2 = 0 from by omega, ite_true, Option.getD_some]
  rw [show 2 * k / 2 = k from by omega]

/-- getD of an interleaved decode at an odd index. -/
theorem getD_decode_odd {ys : List UInt8} {k : Nat}
    (h : k < ys.length / 2) :
    (interleaveDecode ys).getD (2 * k + 1) 0 = ys.getD ((ys.length + 1) / 2 + k) 0 := by
  rw [List.getD_eq_getElem?_getD]
  unfold interleaveDecode
  rw [getElem?_range_map (by omega)]
  simp only [show ¬ (2 * k + 1) % 2 = 0 from by omega, ite_false, Option.getD_some]
  congr 1
  omega

theorem interleaveEncode_decode (ys : List UInt8) :
    interleaveEncode (interleaveDecode ys) = ys := by
  apply List.ext_getElem?
  intro j
  have hleftlen : ((List.range ((ys.length + 1) / 2)).map
      fun i => (interleaveDecode ys).getD (2 * i) 0).length
      = (ys.length + 1) / 2 := by
    rw [List.length_map, List.length_range]
  by_cases hj : j < ys.length
  · rw [List.getElem?_eq_getElem hj]
    unfold interleaveEncode
    rw [interleaveDecode_length]
    rw [List.getElem?_append]
    by_cases hje : j < (ys.length + 1) / 2
    · rw [ite_eq_left (by rw [hleftlen]; omega)]
      rw [getElem?_range_map hje]
      congr 1
      rw [getD_decode_even hje]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    · rw [ite_eq_right (by rw [hleftlen]; omega)]
      have h3 : j - (ys.length + 1) / 2 < ys.length / 2 := by omega
      rw [hleftlen, getElem?_range_map h3]
      congr 1
      rw [getD_decode_odd h3]
      rw [show (ys.length + 1) / 2 + (j - (ys.length + 1) / 2) = j from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  · unfold interleaveEncode
    rw [interleaveDecode_length]
    rw [List.getElem?_eq_none (by
        rw [List.length_append, List.length_map, List.length_map, List.length_range,
          List.length_range]
        omega),
      List.getElem?_eq_none (Nat.le_of_not_lt hj)]

/-! ## Delta predictor -/

/-- Delta predictor (encode direction): store (cur - prev + 128) per byte. -/
def predictorEncodeGo (prev : UInt8) : List UInt8 → List UInt8
  | [] => []
  | c :: cs => (c - prev + 128) :: predictorEncodeGo c cs

def predictorEncode : List UInt8 → List UInt8
  | [] => []
  | x :: rest => x :: predictorEncodeGo x rest

/-- Reconstruction: each byte holds (delta + 128) vs the previous byte. -/
def predictorDecodeGo (prev : UInt8) : List UInt8 → List UInt8
  | [] => []
  | c :: cs => (prev + c - 128) :: predictorDecodeGo (prev + c - 128) cs

def predictorDecode : List UInt8 → List UInt8
  | [] => []
  | x :: rest => x :: predictorDecodeGo x rest

theorem predictorDecodeGo_encodeGo (prev : UInt8) (cs : List UInt8) :
    predictorDecodeGo prev (predictorEncodeGo prev cs) = cs := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih =>
    show (prev + (c - prev + 128) - 128) :: predictorDecodeGo (prev + (c - prev + 128) - 128)
        (predictorEncodeGo c cs) = c :: cs
    rw [show prev + (c - prev + 128) - 128 = c by bv_decide]
    exact congrArg (List.cons c) (ih (prev := c))

theorem predictorDecode_encode (xs : List UInt8) :
    predictorDecode (predictorEncode xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x rest =>
    show x :: predictorDecodeGo x (predictorEncodeGo x rest) = x :: rest
    rw [predictorDecodeGo_encodeGo]

theorem predictorEncodeGo_decodeGo (prev : UInt8) (cs : List UInt8) :
    predictorEncodeGo prev (predictorDecodeGo prev cs) = cs := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih =>
    show ((prev + c - 128) - prev + 128) :: predictorEncodeGo (prev + c - 128)
        (predictorDecodeGo (prev + c - 128) cs) = c :: cs
    rw [show (prev + c - 128) - prev + 128 = c by bv_decide]
    exact congrArg (List.cons c) (ih (prev := prev + c - 128))

theorem predictorEncode_decode (xs : List UInt8) :
    predictorEncode (predictorDecode xs) = xs := by
  cases xs with
  | nil => rfl
  | cons x rest =>
    show x :: predictorEncodeGo x (predictorDecodeGo x rest) = x :: rest
    rw [predictorEncodeGo_decodeGo]

/-! ## Run-length expansion -/

/-- Run-length decode: a signed count byte; bytes >= 128 denote a literal
    run of (256 - count) bytes; otherwise the next byte is repeated
    count + 1 times. -/
def rleExpand : List UInt8 → Option (List UInt8)
  | [] => some []
  | [_] => none
  | b :: v :: tl =>
    if 128 ≤ b.toNat then
      let len := 256 - b.toNat
      match (v :: tl).take len with
      | buf => if buf.length = len then
          Option.map (fun x => buf ++ x) (rleExpand ((v :: tl).drop len))
        else none
    else
      Option.map (fun x => (List.replicate (b.toNat + 1) v) ++ x) (rleExpand tl)
termination_by src => src.length
decreasing_by
  all_goals
    (simp only [List.length_drop, List.length_cons]
     omega)

/-! ## Greedy run-length encoding -/

/-- Maximal constant run at the head. -/
def runPrefix (v : UInt8) : List UInt8 → Nat
  | [] => 0
  | x :: xs => if x = v then runPrefix v xs + 1 else 0

/-- Literal scan: advance until just before the first 3-run (or 127 bytes). -/
def litLenGo : Nat → List UInt8 → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, x :: rest =>
    match rest with
    | y :: z :: _ => if x = y ∧ y = z then 0 else litLenGo n rest + 1
    | _ => 1

def litLen (xs : List UInt8) : Nat := litLenGo 127 xs

theorem litLen_pos_of_not_run {v : UInt8} {rest : List UInt8}
    (h : ¬ 3 ≤ runPrefix v (v :: rest)) : 1 ≤ litLen (v :: rest) := by
  unfold litLen
  cases rest with
  | nil => simp [litLenGo]
  | cons y rest =>
    cases rest with
    | nil => simp [litLenGo]
    | cons z tl =>
      simp only [litLenGo]
      by_cases htri : v = y ∧ y = z
      · obtain ⟨rfl, rfl⟩ := htri
        exfalso
        apply h
        simp only [runPrefix]
        simp
      · simp [htri]

theorem litLenGo_le (n : Nat) (xs : List UInt8) : litLenGo n xs ≤ n := by
  induction n generalizing xs with
  | zero => simp [litLenGo]
  | succ n ih =>
    cases xs with
    | nil => simp [litLenGo]
    | cons x rest =>
      simp only [litLenGo]
      cases rest with
      | nil => simp
      | cons y rest2 =>
        cases rest2 with
        | nil => simp
        | cons z tl =>
          by_cases htri : x = y ∧ y = z
          · simp [htri]
          · simp [htri]
            have := ih (xs := y :: z :: tl)
            omega

theorem litLen_le (xs : List UInt8) : litLen xs ≤ 127 :=
  litLenGo_le 127 xs

theorem litLenGo_le_length (n : Nat) (xs : List UInt8) : litLenGo n xs ≤ xs.length := by
  induction n generalizing xs with
  | zero => simp [litLenGo]
  | succ n ih =>
    cases xs with
    | nil => simp [litLenGo]
    | cons x rest =>
      simp only [litLenGo]
      cases rest with
      | nil => simp
      | cons y rest2 =>
        cases rest2 with
        | nil => simp
        | cons z tl =>
          by_cases htri : x = y ∧ y = z
          · simp [htri]
          · simp [htri]
            have := ih (xs := y :: z :: tl)
            omega

theorem litLen_le_length (xs : List UInt8) : litLen xs ≤ xs.length := by
  unfold litLen
  have := litLenGo_le_length 127 xs
  exact this

/-- Greedy run-length encode (bit-exact with the C `rle_encode`). -/
def rleEncode : List UInt8 → List UInt8
  | [] => []
  | v :: rest =>
    let r := runPrefix v (v :: rest)
    if 3 ≤ r then
      let len := min r 128
      ([UInt8.ofNat (len - 1), v] : List UInt8) ++ rleEncode ((v :: rest).drop len)
    else
      let len := litLen (v :: rest)
      (UInt8.ofNat (256 - len) :: (v :: rest).take len) ++ rleEncode ((v :: rest).drop (max 1 len))
termination_by xs => xs.length
decreasing_by
  all_goals
    (simp only [List.length_drop, List.length_cons]
     omega)


-- probe: round trip pieces
theorem take_replicate {v : UInt8} : ∀ (len : Nat) (xs : List UInt8),
    len ≤ runPrefix v xs → xs.take len = List.replicate len v := by
  intro len
  induction len with
  | zero => intro xs _; rfl
  | succ len ih =>
    intro xs h
    cases xs with
    | nil => simp [runPrefix] at h
    | cons x rest =>
      by_cases hx : x = v
      · rw [hx, List.take_succ_cons]
        congr 1
        apply ih
        simp only [runPrefix] at h
        rw [ite_eq_left hx] at h
        omega
      · simp only [runPrefix, ite_eq_right hx] at h
        exact absurd h (Nat.not_succ_le_zero _)

theorem UInt8_ofNat_toNat_small {n : Nat} (h : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  simpa using Nat.mod_eq_of_lt h

theorem rleExpand_rleEncode (xs : List UInt8) :
    rleExpand (rleEncode xs) = some xs := by
  have aux : ∀ (n : Nat) (ys : List UInt8), ys.length ≤ n →
      rleExpand (rleEncode ys) = some ys := by
    intro n
    induction n with
    | zero =>
      intro ys h
      cases ys with
      | nil => simp only [rleEncode, rleExpand]
      | cons v rest => exfalso; simp at h
    | succ n ih =>
      intro ys h
      cases ys with
      | nil => simp only [rleEncode, rleExpand]
      | cons v rest =>
        simp only [rleEncode]
        by_cases hrun : 3 ≤ runPrefix v (v :: rest)
        · rw [ite_eq_left hrun]
          -- RUN branch
          simp only [List.cons_append, List.nil_append, rleExpand]
          rw [ite_eq_right (show ¬ 128 ≤ (UInt8.ofNat (min (runPrefix v (v :: rest)) 128 - 1)).toNat from by
            rw [UInt8_ofNat_toNat_small (by omega)]
            omega)]
          rw [UInt8_ofNat_toNat_small (by omega),
            show min (runPrefix v (v :: rest)) 128 - 1 + 1 = min (runPrefix v (v :: rest)) 128 from by omega,
            ih ((v :: rest).drop (min (runPrefix v (v :: rest)) 128)) (by
              rw [List.length_drop]
              have hlen1 : 1 ≤ min (runPrefix v (v :: rest)) 128 := by omega
              have hll : (v :: rest).length ≤ n + 1 := h
              omega)]
          rw [Option.map_some]
          congr 1
          rw [← take_replicate (min (runPrefix v (v :: rest)) 128) (v :: rest) (Nat.min_le_left _ _)]
          exact List.take_append_drop _ _
        · rw [ite_eq_right hrun]
          -- LIT branch
          obtain ⟨ll, hll⟩ : ∃ ll, litLen (v :: rest) = ll + 1 :=
            ⟨litLen (v :: rest) - 1, by obtain hpos := litLen_pos_of_not_run hrun; omega⟩
          rw [hll]
          have hle127 : ll + 1 ≤ 127 := by
            have h1 := litLen_le (v :: rest)
            omega
          have hlelen : ll + 1 ≤ (v :: rest).length := by
            have h1 := litLen_le_length (v :: rest)
            omega
          have hlen_rest : ll ≤ rest.length := by
            have h1 : (v :: rest).length = rest.length + 1 := List.length_cons ..
            omega
          simp only [List.take_succ_cons, List.cons_append]
          simp only [rleExpand]
          rw [UInt8_ofNat_toNat_small (by omega)]
          rw [ite_eq_left (show 128 ≤ 256 - (ll + 1) from by omega)]
          rw [show 256 - (256 - (ll + 1)) = ll + 1 from by omega]
          rw [List.take_succ_cons, List.take_left' (by
            rw [List.length_take, Nat.min_eq_left hlen_rest])]
          rw [ite_eq_left (by
            rw [List.length_cons, List.length_take, Nat.min_eq_left hlen_rest])]
          rw [List.drop_succ_cons]
          rw [List.drop_append_of_le_length (by
            rw [List.length_take, Nat.min_eq_left hlen_rest])]
          rw [show (rest.take ll).drop ll = [] from List.drop_of_length_le (by
            rw [List.length_take, Nat.min_eq_left hlen_rest])]
          simp only [List.nil_append]
          rw [ih ((v :: rest).drop (max 1 (ll + 1))) (by
            rw [List.length_drop]
            have hll2 : (v :: rest).length ≤ n + 1 := h
            have hmax : 1 ≤ max 1 (ll + 1) := by omega
            omega)]
          rw [Option.map_some]
          congr 1
          rw [Nat.max_eq_right (by omega), ← List.take_succ_cons]
          exact List.take_append_drop _ _
  exact aux xs.length xs le_rfl

-- probe: encode size bound
theorem rleEncode_length_le (xs : List UInt8) :
    (rleEncode xs).length ≤ 2 * xs.length := by
  have aux : ∀ (n : Nat) (ys : List UInt8), ys.length ≤ n →
      (rleEncode ys).length ≤ 2 * ys.length := by
    intro n
    induction n with
    | zero =>
      intro ys h
      cases ys with
      | nil => simp [rleEncode]
      | cons v rest => exfalso; simp at h
    | succ n ih =>
      intro ys h
      cases ys with
      | nil => simp [rleEncode]
      | cons v rest =>
        simp only [rleEncode]
        by_cases hrun : 3 ≤ runPrefix v (v :: rest)
        · rw [ite_eq_left hrun]
          rw [List.length_append]
          have h2 : ([UInt8.ofNat (min (runPrefix v (v :: rest)) 128 - 1), v] : List UInt8).length = 2 := by
            simp
          have hih := ih ((v :: rest).drop (min (runPrefix v (v :: rest)) 128)) (by
            rw [List.length_drop]
            have hlen1 : 1 ≤ min (runPrefix v (v :: rest)) 128 := by omega
            have hll : (v :: rest).length ≤ n + 1 := h
            omega)
          have hdrop : (List.drop (min (runPrefix v (v :: rest)) 128) (v :: rest)).length
              = (v :: rest).length - min (runPrefix v (v :: rest)) 128 := by
            rw [List.length_drop]
          have hlen1 : 1 ≤ min (runPrefix v (v :: rest)) 128 := by omega
          have hll : (v :: rest).length ≤ n + 1 := h
          have hpos : 0 < (v :: rest).length := by
            rw [List.length_cons]
            omega
          omega
        · rw [ite_eq_right hrun]
          rw [List.length_append, List.length_cons]
          have hpos : 1 ≤ litLen (v :: rest) := litLen_pos_of_not_run hrun
          have hle : litLen (v :: rest) ≤ (v :: rest).length := litLen_le_length _
          have hih := ih ((v :: rest).drop (max 1 (litLen (v :: rest)))) (by
            rw [List.length_drop]
            have hll : (v :: rest).length ≤ n + 1 := h
            have hmax : 1 ≤ max 1 (litLen (v :: rest)) := by omega
            omega)
          have hdrop : (List.drop (max 1 (litLen (v :: rest))) (v :: rest)).length
              = (v :: rest).length - max 1 (litLen (v :: rest)) := by
            rw [List.length_drop]
          have htake : ((v :: rest).take (litLen (v :: rest))).length
              = litLen (v :: rest) := by
            rw [List.length_take, Nat.min_eq_left hle]
          have hpos : 0 < (v :: rest).length := by
            rw [List.length_cons]
            omega
          omega
  exact aux xs.length xs le_rfl

/-- Full compressor: greedy RLE with the C fallback to storing the raw block
    when the run encoding would not shrink it (the size fast-path on the
    reader relies on the stored size for this). -/
def rleCompress (xs : List UInt8) : List UInt8 :=
  let enc := rleEncode (predictorEncode (interleaveEncode xs))
  if enc.length < xs.length then enc else xs

theorem rleCompress_length_le (xs : List UInt8) :
    (rleCompress xs).length ≤ xs.length := by
  unfold rleCompress
  by_cases henc : (rleEncode (predictorEncode (interleaveEncode xs))).length < xs.length
  · rw [ite_eq_left henc]
    exact le_of_lt henc
  · rw [ite_eq_right henc]

/-- Full decompressor: the C size fast-path (equal sizes merge) followed by
    run expansion, predictor and interleave reconstruction. -/
def rleDecodeFull (stored : List UInt8) (n : Nat) : Option (List UInt8) :=
  if stored.length = n then some stored
  else (rleExpand stored).map (fun p => interleaveDecode (predictorDecode p))

theorem rleRoundTrip (xs : List UInt8) :
    rleDecodeFull (rleCompress xs) xs.length = some xs := by
  unfold rleCompress
  by_cases henc : (rleEncode (predictorEncode (interleaveEncode xs))).length < xs.length
  · rw [ite_eq_left henc]
    unfold rleDecodeFull
    rw [ite_eq_right (by omega)]
    rw [rleExpand_rleEncode]
    rw [Option.map_some]
    rw [predictorDecode_encode]
    rw [interleaveDecode_encode]
  · rw [ite_eq_right henc]
    unfold rleDecodeFull
    rw [ite_eq_left rfl]
end Rle

end Exr
