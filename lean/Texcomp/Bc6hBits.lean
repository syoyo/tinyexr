/-
  TinyEXR - Lean 4 formalization of BC6H bit reading.

  BC6H packs 128 bits (16 bytes) in little-endian order. Bits are read
  MSB-first within each byte (big-endian bit order). This module provides
  the bit reader and mode detection.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Read a UInt64 from 8 bytes (little-endian). -/
def rd64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
  (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
  (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- BC6H bit reader state: position in the 128-bit stream. -/
structure Bc6hReader where
  low : UInt64
  high : UInt64
  pos : Nat  -- current bit position (0..128)
  deriving Repr

/-- Initialize reader from 16 bytes. -/
def bc6hReaderInit (bytes : Fin 16 → UInt8) : Bc6hReader :=
  { low := rd64 (bytes 0) (bytes 1) (bytes 2) (bytes 3) (bytes 4) (bytes 5) (bytes 6) (bytes 7)
  , high := rd64 (bytes 8) (bytes 9) (bytes 10) (bytes 11) (bytes 12) (bytes 13) (bytes 14) (bytes 15)
  , pos := 0 }

/-- Read n bits (n ≤ 64) from the reader. Returns value and new reader. -/
def bc6hRead (r : Bc6hReader) (n : Nat) : (UInt64 × Bc6hReader) :=
  if n = 0 then ((0 : UInt64), r)
  else if r.pos + n ≤ 64 then
    let shift := 64 - r.pos - n
    let val := (r.low >>> (UInt64.ofNat shift)) &&& (((1 : UInt64) <<< (UInt64.ofNat n)) - 1)
    (val, { r with pos := r.pos + n })
  else
    -- Simplified: for reads crossing the 64-bit boundary, return 0.
    -- Full boundary handling is deferred to a later slice.
    ((0 : UInt64), { r with pos := r.pos + n })

/-- Detect BC6H mode from first bits. -/
def bc6hDetectMode (r : Bc6hReader) : (Nat × Bc6hReader) :=
  let (m, r1) := bc6hRead r 2
  if m > 1 then
    let (extra, r2) := bc6hRead r1 3
    let mode := m.toNat ||| (extra.toNat <<< 2)
    (mode, r2)
  else
    (m.toNat, r1)

-- Mode detection returns a value in 0..31 by construction.

end Texcomp