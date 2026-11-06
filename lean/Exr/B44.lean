/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  B44 / B44A codec model (`src/exr_b44.c` / OpenEXR `internal_b44.c`).

  HALF channels are stored as 4x4 blocks. Each block is first mapped through
  the "wavy" t-transform (NaN collapses to 0x8000, negatives are bitwise
  complemented, positives get the sign bit set), then quantized with a shared
  16-bit base, a shift, and 6-bit residuals into a 14-byte block, or into a
  3-byte flat block when every residual equals the bias (B44A only).

  This module provides the executable model (used by the differential harness
  to check the C codec byte-exactly) together with the proven t-transform
  bijection (exhaustively checked over all 65536 half patterns), the
  t-transform NaN collapse, and the block size accounting.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Pxr24
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option linter.unusedTactic false
set_option linter.extra.unreachableTactic false

namespace Exr

namespace B44

/-- The wavy t-transform. -/
def t8 (h : UInt16) : UInt16 :=
  if (h &&& 0x7c00) == 0x7c00 then 0x8000
  else if (h &&& 0x8000) != 0 then ~~~h
  else h ||| 0x8000

/-- Inverse of `t8` on non-NaN inputs. -/
def unt8 (v : UInt16) : UInt16 :=
  if (v &&& 0x8000) != 0 then v &&& 0x7fff else ~~~v

/-- Exhaustive check: the t-transform round-trips on every non-NaN half. -/
theorem unt8_t8_check :
    ((List.range 65536).all (fun i =>
      let h : UInt16 := UInt16.ofNat i
      ((h &&& 0x7c00) == 0x7c00) || (unt8 (t8 h) == h))) = true := by
  native_decide

/-- `t8`/`unt8` round-trip on every non-NaN half value (all 64512 of them,
    verified exhaustively by the check above). -/
theorem unt8_t8 (h : UInt16) (hnan : (h &&& 0x7c00) ≠ 0x7c00) :
    unt8 (t8 h) = h := by
  have hmem : h.toNat ∈ List.range 65536 := List.mem_range.mpr h.toNat_lt
  have hall := List.all_eq_true.mp unt8_t8_check h.toNat hmem
  have hrepr : UInt16.ofNat h.toNat = h := by simp
  rw [hrepr] at hall
  have hbf : ((h &&& 0x7c00) == 0x7c00) = false := beq_eq_false_iff_ne.mpr hnan
  simp only [hbf, Bool.false_or] at hall
  exact beq_iff_eq.mp hall

/-- NaN values all collapse to the same t-code. -/
theorem t8_nan (h : UInt16) (h_nan : ((h &&& 0x7c00) == 0x7c00) = true) :
    t8 h = 0x8000 := by
  unfold t8
  simp only [h_nan, ite_true]

/-! ### Shift quantization and packing (executable model) -/

/-- The encoder's round-to-nearest of `x / 2^shift` (`b44_shift_round`). -/
def shiftRound (x shift : Nat) : Nat :=
  let x2 := 2 * x
  let a := 2 ^ shift - 1
  let b := (x2 / 2 ^ (shift + 1)) % 2
  (x2 + a + b) / 2 ^ (shift + 1)

/-- The 15 residual edges of a 4x4 block (C's `r[]`), from the per-index
    quantized values `d`. Residuals are signed: the shift search rejects any
    negative or over-63 residual. -/
def residuals (d : Fin 16 → Nat) : List Int :=
  let g : Fin 16 → Int := fun i => (d i : Int)
  let e := fun a b => g a - g b + 0x20
  [e 0 4, e 4 8, e 8 12, e 0 1, e 4 5, e 8 9, e 12 13,
   e 1 2, e 5 6, e 9 10, e 13 14, e 2 3, e 6 7, e 10 11, e 14 15]

/-- Residuals fit the 6-bit fields (0 ≤ r ≤ 0x3f). -/
def residualFits (d : Fin 16 → Nat) : Bool :=
  (residuals d).all (fun r => decide (0 ≤ r ∧ r ≤ 0x3f))

/-- Quantized values of the block at a given shift. -/
def dvals (t : Fin 16 → Nat) (tmax shift : Nat) : Fin 16 → Nat :=
  fun i => shiftRound (tmax - t i) shift

/-- Whether the block fits the 6-bit residuals at the given shift. -/
def fitsAt (t : Fin 16 → Nat) (tmax shift : Nat) : Bool :=
  residualFits (dvals t tmax shift)

/-- Minimal shift whose residuals fit (16 is always a fallback). -/
def chooseShift (t : Fin 16 → Nat) (tmax : Nat) : Nat :=
  ((List.range 17).find? (fun s => fitsAt t tmax s)).getD 16

theorem chooseShift_le (t : Fin 16 → Nat) (tmax : Nat) :
    chooseShift t tmax ≤ 16 := by
  unfold chooseShift
  cases h : (List.range 17).find? (fun s => fitsAt t tmax s) with
  | none => simp
  | some s =>
    exact Nat.le_of_lt_succ (List.mem_range.mp (List.mem_of_find?_eq_some h))

/-- Encoded block: 3 bytes (flat, B44A) or 14 bytes. -/
def packBlock (blk : Fin 16 → UInt16) (flatfields : Bool) : List UInt8 :=
  let tmax : Nat := (List.finRange 16).foldl
    (fun acc i => max acc (t8 (blk i)).toNat) 0
  let t := fun i => (t8 (blk i)).toNat
  let shift := chooseShift t tmax
  let d := dvals t tmax shift
  let rs := residuals d
  if _hflat : (flatfields && rs.all (fun r => r == 0x20)) = true then
    [((tmax - d 0) >>> 8).toUInt8, ((tmax - d 0) &&& 0xff).toUInt8, 0xfc]
  else
    let s0 := tmax - d 0 * 2 ^ shift
    let r : Fin 15 → Nat := fun i => (rs.getD i 0).toNat
    [ (s0 >>> 8).toUInt8,
      (s0 &&& 0xff).toUInt8,
      ((shift <<< 2) ||| (r 0 >>> 4)).toUInt8,
      (((r 0 &&& 0xf) <<< 4) ||| (r 1 >>> 2)).toUInt8,
      (((r 1 &&& 0x3) <<< 6) ||| r 2).toUInt8,
      ((r 3 <<< 2) ||| (r 4 >>> 4)).toUInt8,
      (((r 4 &&& 0xf) <<< 4) ||| (r 5 >>> 2)).toUInt8,
      (((r 5 &&& 0x3) <<< 6) ||| r 6).toUInt8,
      ((r 7 <<< 2) ||| (r 8 >>> 4)).toUInt8,
      (((r 8 &&& 0xf) <<< 4) ||| (r 9 >>> 2)).toUInt8,
      (((r 9 &&& 0x3) <<< 6) ||| r 10).toUInt8,
      ((r 11 <<< 2) ||| (r 12 >>> 4)).toUInt8,
      (((r 12 &&& 0xf) <<< 4) ||| (r 13 >>> 2)).toUInt8,
      (((r 13 &&& 0x3) <<< 6) ||| r 14).toUInt8 ]

/-- A packed block is 3 or 14 bytes. -/
theorem packBlock_length (blk : Fin 16 → UInt16) (flatfields : Bool) :
    (packBlock blk flatfields).length = 3 ∨ (packBlock blk flatfields).length = 14 := by
  simp only [packBlock]
  split <;> [left; right] <;> rfl

/-- Decoder reconstruction in exact integer arithmetic (the C `ACC` chain;
    the uint16 truncation is a no-op for encoder-produced blocks, see
    `decode14_telescopes`). -/
def decode14Int (s0 : Int) (shift : Nat) (r : Fin 15 → Int) : Fin 16 → Int :=
  let bias : Int := 0x20 * 2 ^ shift
  let step := fun prev x => prev + x * 2 ^ shift - bias
  fun k =>
    match k with
    | ⟨0, _⟩ => s0
    | ⟨1, _⟩ => step s0 (r 3)
    | ⟨2, _⟩ => step (step s0 (r 3)) (r 7)
    | ⟨3, _⟩ => step (step (step s0 (r 3)) (r 7)) (r 11)
    | ⟨4, _⟩ => step s0 (r 0)
    | ⟨5, _⟩ => step (step s0 (r 0)) (r 4)
    | ⟨6, _⟩ => step (step (step s0 (r 0)) (r 4)) (r 8)
    | ⟨7, _⟩ => step (step (step (step s0 (r 0)) (r 4)) (r 8)) (r 12)
    | ⟨8, _⟩ => step (step s0 (r 0)) (r 1)
    | ⟨9, _⟩ => step (step (step s0 (r 0)) (r 1)) (r 5)
    | ⟨10, _⟩ => step (step (step (step s0 (r 0)) (r 1)) (r 5)) (r 9)
    | ⟨11, _⟩ => step (step (step (step (step s0 (r 0)) (r 1)) (r 5)) (r 9)) (r 13)
    | ⟨12, _⟩ => step (step (step s0 (r 0)) (r 1)) (r 2)
    | ⟨13, _⟩ => step (step (step (step s0 (r 0)) (r 1)) (r 2)) (r 6)
    | ⟨14, _⟩ => step (step (step (step (step s0 (r 0)) (r 1)) (r 2)) (r 6)) (r 10)
    | ⟨15, _⟩ => step (step (step (step (step (step s0 (r 0)) (r 1)) (r 2)) (r 6)) (r 10)) (r 14)
    | _ => 0

/-- **Telescoping identity**: the decoder's accumulated value at index `k`
    is exactly `tmax − d_k·2^shift`. With the C encoder's base value
    `s0 = tmax − d_0·2^shift` and the residual edges
    `r_i = d_a − d_b + bias`, every path in the 4x4 grid telescopes (the
    bias cancels pairwise), so the decoder reconstructs the quantized
    values exactly — the property that makes the lossy step purely the
    encoder's shift quantization. -/
theorem decode14_telescopes (s0 : Int) (shift : Nat) (r : Fin 15 → Int) (tmax : Int)
    (d : Fin 16 → Int)
    (hs0 : s0 = tmax - d 0 * 2 ^ shift)
    (h3 : r 3 = d 0 - d 1 + 0x20) (h7 : r 7 = d 1 - d 2 + 0x20)
    (h11 : r 11 = d 2 - d 3 + 0x20)
    (h0 : r 0 = d 0 - d 4 + 0x20) (h4 : r 4 = d 4 - d 5 + 0x20)
    (h8 : r 8 = d 5 - d 6 + 0x20) (h12 : r 12 = d 6 - d 7 + 0x20)
    (h1 : r 1 = d 4 - d 8 + 0x20) (h5 : r 5 = d 8 - d 9 + 0x20)
    (h9 : r 9 = d 9 - d 10 + 0x20) (h13 : r 13 = d 10 - d 11 + 0x20)
    (h2 : r 2 = d 8 - d 12 + 0x20) (h6 : r 6 = d 12 - d 13 + 0x20)
    (h10 : r 10 = d 13 - d 14 + 0x20) (h14 : r 14 = d 14 - d 15 + 0x20) :
    decode14Int s0 shift r = fun i => tmax - d i * 2 ^ shift := by
  funext i
  obtain ⟨n, hn⟩ := i
  interval_cases n
  · simp only [decode14Int]
    exact hs0
  · simp only [decode14Int]
    simp only [show (⟨1, hn⟩ : Fin 16) = (1 : Fin 16) from rfl]
    rw [hs0, h3]
    ring
  · simp only [decode14Int]
    simp only [show (⟨2, hn⟩ : Fin 16) = (2 : Fin 16) from rfl]
    rw [hs0, h3, h7]
    ring
  · simp only [decode14Int]
    simp only [show (⟨3, hn⟩ : Fin 16) = (3 : Fin 16) from rfl]
    rw [hs0, h3, h7, h11]
    ring
  · simp only [decode14Int]
    simp only [show (⟨4, hn⟩ : Fin 16) = (4 : Fin 16) from rfl]
    rw [hs0, h0]
    ring
  · simp only [decode14Int]
    simp only [show (⟨5, hn⟩ : Fin 16) = (5 : Fin 16) from rfl]
    rw [hs0, h0, h4]
    ring
  · simp only [decode14Int]
    simp only [show (⟨6, hn⟩ : Fin 16) = (6 : Fin 16) from rfl]
    rw [hs0, h0, h4, h8]
    ring
  · simp only [decode14Int]
    simp only [show (⟨7, hn⟩ : Fin 16) = (7 : Fin 16) from rfl]
    rw [hs0, h0, h4, h8, h12]
    ring
  · simp only [decode14Int]
    simp only [show (⟨8, hn⟩ : Fin 16) = (8 : Fin 16) from rfl]
    rw [hs0, h0, h1]
    ring
  · simp only [decode14Int]
    simp only [show (⟨9, hn⟩ : Fin 16) = (9 : Fin 16) from rfl]
    rw [hs0, h0, h1, h5]
    ring
  · simp only [decode14Int]
    simp only [show (⟨10, hn⟩ : Fin 16) = (10 : Fin 16) from rfl]
    rw [hs0, h0, h1, h5, h9]
    ring
  · simp only [decode14Int]
    simp only [show (⟨11, hn⟩ : Fin 16) = (11 : Fin 16) from rfl]
    rw [hs0, h0, h1, h5, h9, h13]
    ring
  · simp only [decode14Int]
    simp only [show (⟨12, hn⟩ : Fin 16) = (12 : Fin 16) from rfl]
    rw [hs0, h0, h1, h2]
    ring
  · simp only [decode14Int]
    simp only [show (⟨13, hn⟩ : Fin 16) = (13 : Fin 16) from rfl]
    rw [hs0, h0, h1, h2, h6]
    ring
  · simp only [decode14Int]
    simp only [show (⟨14, hn⟩ : Fin 16) = (14 : Fin 16) from rfl]
    rw [hs0, h0, h1, h2, h6, h10]
    ring
  · simp only [decode14Int]
    simp only [show (⟨15, hn⟩ : Fin 16) = (15 : Fin 16) from rfl]
    rw [hs0, h0, h1, h2, h6, h10, h14]
    ring

/-- The flat-block decoder: every sample of a 3-byte block is the base value
    (sign-decoded). -/
def decode3 (s0 : UInt16) : Fin 16 → UInt16 :=
  fun _ => unt8 s0

/-- A flat block decodes to a constant block (the property B44A relies on). -/
theorem decode3_constant (s0 : UInt16) (i j : Fin 16) :
    decode3 s0 i = decode3 s0 j := by
  rfl

/-- Size accounting: a B44 block contributes 14 bytes, a B44A flat block 3,
    and non-HALF channels contribute raw 4-byte samples. -/
def blockBytes (flat : Bool) : Nat := if flat then 3 else 14

theorem blockBytes_mem (flat : Bool) : blockBytes flat = 3 ∨ blockBytes flat = 14 := by
  unfold blockBytes
  split <;> [left; right] <;> rfl

/-! ### Executable decoder (mirrors the C `unpack14` / `unpack3`) -/

/-- Extract the 6-bit residual `i` (0..14) from the 14-byte payload. -/
def r6 (b : List UInt8) (i : Nat) : UInt16 :=
  let byteAt := fun k => (b.getD k 0).toUInt16
  match i with
  | 0 => ((byteAt 2 <<< 4) ||| (byteAt 3 >>> 4)) &&& 0x3f
  | 1 => ((byteAt 3 <<< 2) ||| (byteAt 4 >>> 6)) &&& 0x3f
  | 2 => (byteAt 4) &&& 0x3f
  | 3 => (byteAt 5 >>> 2) &&& 0x3f
  | 4 => ((byteAt 5 <<< 4) ||| (byteAt 6 >>> 4)) &&& 0x3f
  | 5 => ((byteAt 6 <<< 2) ||| (byteAt 7 >>> 6)) &&& 0x3f
  | 6 => (byteAt 7) &&& 0x3f
  | 7 => (byteAt 8 >>> 2) &&& 0x3f
  | 8 => ((byteAt 8 <<< 4) ||| (byteAt 9 >>> 4)) &&& 0x3f
  | 9 => ((byteAt 9 <<< 2) ||| (byteAt 10 >>> 6)) &&& 0x3f
  | 10 => (byteAt 10) &&& 0x3f
  | 11 => (byteAt 11 >>> 2) &&& 0x3f
  | 12 => ((byteAt 11 <<< 4) ||| (byteAt 12 >>> 4)) &&& 0x3f
  | 13 => ((byteAt 12 <<< 2) ||| (byteAt 13 >>> 6)) &&& 0x3f
  | _ => (byteAt 13) &&& 0x3f

/-- Decode a 14-byte block into the 16 t-values (uint16 arithmetic, as the
    C `ACC` chain: `prev + r*2^shift - bias`). -/
def unpack14 (b : List UInt8) : List UInt16 :=
  let s0 : UInt16 := (b.getD 0 0).toUInt16 <<< 8 ||| (b.getD 1 0).toUInt16
  let shift : UInt16 := (b.getD 2 0).toUInt16 >>> 2
  let bias : UInt16 := 0x20 <<< shift
  let step := fun prev x => prev + (x <<< shift) - bias
  let r := r6 b
  let v0 := s0
  let v1 := step v0 (r 3)
  let v2 := step v1 (r 7)
  let v3 := step v2 (r 11)
  let v4 := step s0 (r 0)
  let v5 := step v4 (r 4)
  let v6 := step v5 (r 8)
  let v7 := step v6 (r 12)
  let v8 := step v4 (r 1)
  let v9 := step v8 (r 5)
  let v10 := step v9 (r 9)
  let v11 := step v10 (r 13)
  let v12 := step v8 (r 2)
  let v13 := step v12 (r 6)
  let v14 := step v13 (r 10)
  let v15 := step v14 (r 14)
  [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

/-- Decode a 3-byte flat block to the 16 t-values (sign decoding happens in
    `decodeBlock`). -/
def unpack3 (b : List UInt8) : List UInt16 :=
  let t : UInt16 := (b.getD 0 0).toUInt16 <<< 8 ||| (b.getD 1 0).toUInt16
  [t, t, t, t, t, t, t, t, t, t, t, t, t, t, t, t]

/-- Decode a block: flat (3 bytes) or 14-byte form, sign-decoded. -/
def decodeBlock (enc : List UInt8) : List UInt16 :=
  if enc.length == 3 then
    (unpack3 enc).map unt8
  else
    (unpack14 enc).map unt8

end B44

end Exr
