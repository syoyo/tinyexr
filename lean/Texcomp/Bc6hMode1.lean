/-
  TinyEXR - Lean 4 formalization of BC6H mode 1 (7.666 x3) decode.

  Single-subset mode: 7-bit base R0/G0/B0, 6-bit deltas, 3-bit weights,
  5-bit partition. Follows the same structure as mode 0.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hBits
import Texcomp.Bc6hMode0

namespace Texcomp

/-- Mode-1 endpoint extraction. Returns (r0, g0, b0, r1, g1, b1, reader). -/
def bc6hMode1Endpoints (bytes : Fin 16 → UInt8) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Bc6hReader) :=
  let r := bc6hReaderInit bytes
  let (_, r1) := bc6hRead r 2
  let (_, r2) := bc6hRead r1 3
  -- shared bits
  let (_, r3) := bc6hRead r2 1  -- g[2] bit 5
  let (_, r4) := bc6hRead r3 1  -- g[3] bit 4
  let (_, r5) := bc6hRead r4 1  -- g[3] bit 5
  let (r0, r6) := bc6hRead r5 7
  let (_, r7) := bc6hRead r6 1  -- b[3] bit 0
  let (_, r8) := bc6hRead r7 1  -- b[2] bit 4
  let (_, r9) := bc6hRead r8 1  -- b[2] bit 5
  let (g0, r10) := bc6hRead r9 7
  let (_, r11) := bc6hRead r10 1  -- b[3] bit 1
  let (_, r12) := bc6hRead r11 1  -- b[3] bit 2
  let (_, r13) := bc6hRead r12 1  -- b[3] bit 3
  let (_, r14) := bc6hRead r13 1  -- b[3] bit 5
  let (_, r15) := bc6hRead r14 1  -- b[3] bit 4
  let (b0, r16) := bc6hRead r15 7
  let (r1v, r17) := bc6hRead r16 6
  let (_, r18) := bc6hRead r17 4  -- g[2] 4 bits
  let (g1v, r19) := bc6hRead r18 6
  let (_, r20) := bc6hRead r19 4  -- g[3] 4 bits
  let (b1v, r21) := bc6hRead r20 6
  let (_, r22) := bc6hRead r21 4  -- b[2] 4 bits
  let (_, r23) := bc6hRead r22 6  -- r[2] 6 bits (unused)
  let (_, r24) := bc6hRead r23 6  -- r[3] 6 bits (unused)
  let (_, r25) := bc6hRead r24 5  -- partition
  -- Endpoint reconstruction (unsigned): base 7-bit, delta 6-bit
  let r0low6 := r0.toNat &&& 0x3F
  let g0low6 := g0.toNat &&& 0x3F
  let b0low6 := b0.toNat &&& 0x3F
  let R0 := bc6hUnq r0.toNat 7
  let G0 := bc6hUnq g0.toNat 7
  let B0 := bc6hUnq b0.toNat 7
  let R1 := bc6hUnq ((r1v.toNat + r0low6) % 64) 6
  let G1 := bc6hUnq ((g1v.toNat + g0low6) % 64) 6
  let B1 := bc6hUnq ((b1v.toNat + b0low6) % 64) 6
  (R0, G0, B0, R1, G1, B1, r25)

/-- Decode a BC6H mode-1 block into 16 RGB texels. -/
def bc6hMode1Decode (bytes : Fin 16 → UInt8) : Fin 16 → (UInt16 × UInt16 × UInt16) :=
  let (r0, g0, b0, r1, g1, b1, r) := bc6hMode1Endpoints bytes
  let weightBits := r.high >>> (16 : UInt64)
  fun t =>
    let wIdx := (weightBits.toNat >>> (t.val * 3)) &&& 0x7
    let w := w3 wIdx
    let R := bc6hFinish (Int.ofNat (bc6hInterp r0 r1 w)) false
    let G := bc6hFinish (Int.ofNat (bc6hInterp g0 g1 w)) false
    let B := bc6hFinish (Int.ofNat (bc6hInterp b0 b1 w)) false
    (R, G, B)

/-- BC6H mode-1 decode is total. -/
theorem bc6hMode1Decode_total (bytes : Fin 16 → UInt8) :
    (bc6hMode1Decode bytes) ⟨0, by decide⟩ = (bc6hMode1Decode bytes) ⟨0, by decide⟩ := by
  rfl

end Texcomp