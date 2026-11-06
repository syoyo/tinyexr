/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  ZIP container model (OpenEXR `ZIP`/`ZIPS` blocks: a zlib stream around the
  interleaved, delta-predicted byte stream).  The byte stream itself is
  modelled in `Exr/Rle.lean` (the predictor/interleave passes are shared by
  ZIP and RLE); this module covers the container layer: the zlib header and
  its validation, the ADLER32 trailer (mod-65521 checksum), and the
  scan-line block geometry for the ZIP compression (`linesPerBlock`).

  The DEFLATE payload itself is not modelled (documented boundary): the
  model here pins the wrapper's framing, the header checks and the trailer
  checksum against the C library, which is where the size/checksum
  invariants live.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Rle

namespace Exr

namespace Zip

/-- ADLER32 modulus: the largest prime below 2^16. -/
def modPrime : Nat := 65521

/-- Pure per-byte ADLER32 state update (the reference form: reduce every step). -/
def adler32Go : Nat → Nat → List UInt8 → Nat × Nat
  | s1, s2, [] => (s1, s2)
  | s1, s2, b :: rest =>
    let s1' := (s1 + b.toNat) % modPrime
    let s2' := (s2 + s1') % modPrime
    adler32Go s1' s2' rest

/-- Unbounded accumulation (the C defers the mod to block boundaries). -/
def adler32Acc : Nat → Nat → List UInt8 → Nat × Nat
  | s1, s2, [] => (s1, s2)
  | s1, s2, b :: rest => adler32Acc (s1 + b.toNat) (s2 + (s1 + b.toNat)) rest

/-- The deferred-modulo form equals the per-step form: modular addition
    commutes with the fold, so the C's block-boundary reductions compute the
    same value as the pure per-byte fold. -/
theorem adler32Acc_mod (s1 s2 : Nat) (xs : List UInt8) :
    ((adler32Acc s1 s2 xs).1 % modPrime
      = (adler32Go (s1 % modPrime) (s2 % modPrime) xs).1)
    ∧ ((adler32Acc s1 s2 xs).2 % modPrime
      = (adler32Go (s1 % modPrime) (s2 % modPrime) xs).2) := by
  induction xs generalizing s1 s2 with
  | nil => simp [adler32Acc, adler32Go]
  | cons b rest ih =>
    have hb : b.toNat < modPrime := by
      have h256 := UInt8.toNat_lt b
      simp only [modPrime]
      omega
    have e1 : (s1 % modPrime + b.toNat) % modPrime = (s1 + b.toNat) % modPrime :=
      calc (s1 % modPrime + b.toNat) % modPrime
          = (s1 % modPrime + b.toNat % modPrime) % modPrime := by rw [Nat.mod_eq_of_lt hb]
        _ = (s1 + b.toNat) % modPrime := (Nat.add_mod s1 b.toNat modPrime).symm
    have e2 : (s2 % modPrime + (s1 + b.toNat) % modPrime) % modPrime
        = (s2 + (s1 + b.toNat)) % modPrime :=
      (Nat.add_mod s2 (s1 + b.toNat) modPrime).symm
    have e1' := e1.symm
    have e2' := e2.symm
    have hIH := ih (s1 := s1 + b.toNat) (s2 := s2 + (s1 + b.toNat))
    constructor
    · show ((adler32Acc (s1 + b.toNat) (s2 + (s1 + b.toNat)) rest).1 % modPrime)
        = (adler32Go ((s1 % modPrime + b.toNat) % modPrime)
            ((s2 % modPrime + (s1 % modPrime + b.toNat) % modPrime) % modPrime) rest).1
      rw [← e1', ← e2']
      exact hIH.1
    · show ((adler32Acc (s1 + b.toNat) (s2 + (s1 + b.toNat)) rest).2 % modPrime)
        = (adler32Go ((s1 % modPrime + b.toNat) % modPrime)
            ((s2 % modPrime + (s1 % modPrime + b.toNat) % modPrime) % modPrime) rest).2
      rw [← e1', ← e2']
      exact hIH.2

/-- The ADLER32 value (both components bounded by `modPrime`). -/
def adler32 (xs : List UInt8) : UInt32 :=
  let p := adler32Go 1 0 xs
  ((p.2.toUInt32) <<< 16) + (p.1.toUInt32)

theorem adler32Go_lt {s1 s2 : Nat} (h1 : s1 < modPrime) (h2 : s2 < modPrime)
    (xs : List UInt8) :
    (adler32Go s1 s2 xs).1 < modPrime ∧ (adler32Go s1 s2 xs).2 < modPrime := by
  induction xs generalizing s1 s2 with
  | nil => exact ⟨h1, h2⟩
  | cons b rest ih =>
    simp only [adler32Go]
    exact ih (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

theorem adler32_empty : adler32 [] = 1 := rfl

/-- Header validation: CM = 8 (deflate), CINFO ≤ 7, no preset dictionary, and
    the (CMF*256 + FLG) % 31 == 0 check digits. -/
def zlibHeaderValid (hdr : UInt8 × UInt8) : Bool :=
  (hdr.1 % 16 == 8) && ((hdr.1 >>> 4) ≤ 7) && !((hdr.2 &&& 32) == 32)
    && (((hdr.1.toNat * 256 + hdr.2.toNat) % 31) == 0)

theorem zlibHeaderValid_78_01 : zlibHeaderValid (0x78, 0x01) = true := by decide
theorem zlibHeaderValid_78_9c : zlibHeaderValid (0x78, 0x9c) = true := by decide

/-- The 4-byte big-endian ADLER32 trailer of a zlib stream. -/
def adler32Trailer (xs : List UInt8) : List UInt8 :=
  let v := adler32 xs
  [(v >>> 24).toUInt8, (v >>> 16).toUInt8, ((v >>> 8)).toUInt8, v.toUInt8]

theorem adler32Trailer_length (xs : List UInt8) : (adler32Trailer xs).length = 4 := rfl

/-- A zlib stream over the uncompressed block `xs` validates when the header
    is valid and the trailer is the checksum of `xs`. -/
def validateZlibBlock (hdr : UInt8 × UInt8) (trailer : List UInt8) (xs : List UInt8) : Bool :=
  zlibHeaderValid hdr && (trailer == adler32Trailer xs)

theorem validateZlibBlock_of_valid {hdr : UInt8 × UInt8} {xs : List UInt8}
    (h : zlibHeaderValid hdr = true) :
    validateZlibBlock hdr (adler32Trailer xs) xs = true := by
  simp [validateZlibBlock, h]

/-- Scan lines per ZIP block: 16 (ZIPS is one line per block). -/
theorem zipLinesPerBlock : Compression.linesPerBlock Compression.zip = 16 := rfl
theorem zipsLinesPerBlock : Compression.linesPerBlock Compression.zips = 1 := rfl

end Zip

end Exr
