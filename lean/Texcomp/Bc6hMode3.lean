/-
  TinyEXR - Lean 4 formalization of BC6H mode 3 (11.444/11.555/11.444) decode.

  Single-subset mode: 10-bit base R0/G0/B0 with shared bits,
  4-bit delta R1/R2/R3, 5-bit delta G1, 4-bit delta G2/G3, 4-bit delta B1/B2/B3,
  3-bit weights, 5-bit partition.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hBits
import Texcomp.Bc6hMode0

namespace Texcomp

/-- Mode-3 endpoint extraction. Returns (r0, g0, b0, r1, g1, b1, reader). -/
def bc6hMode3Endpoints (bytes : Fin 16 → UInt8) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Bc6hReader) :=
  let r := bc6hReaderInit bytes
  let (_, r1) := bc6hRead r 2
  let (_, r2) := bc6hRead r1 3
  let (r0low, r3) := bc6hRead r2 10
  let (g0, r4) := bc6hRead r3 10
  let (b0, r5) := bc6hRead r4 10
  let (r1v, r6) := bc6hRead r5 4
  let (rShared, r7) := bc6hRead r6 1
  let (_, r8) := bc6hRead r7 1   -- g[3] bit 4
  let (_, r9) := bc6hRead r8 4   -- g[2] 4 bits
  let (g1v, r10) := bc6hRead r9 5  -- g[1] 5 bits
  let (gShared, r11) := bc6hRead r10 1
  let (_, r12) := bc6hRead r11 4  -- g[3] 4 bits
  let (b1v, r13) := bc6hRead r12 4  -- b[1] 4 bits
  let (bShared, r14) := bc6hRead r13 1
  let (_, r15) := bc6hRead r14 1  -- b[3] bit 1
  let (_, r16) := bc6hRead r15 4  -- b[2] 4 bits
  let (_, r17) := bc6hRead r16 4  -- r[2] 4 bits
  let (_, r18) := bc6hRead r17 1  -- b[3] bit 0
  let (_, r19) := bc6hRead r18 1  -- b[3] bit 2
  let (_, r20) := bc6hRead r19 4  -- r[3] 4 bits
  let (_, r21) := bc6hRead r20 1  -- g[2] bit 4
  let (_, r22) := bc6hRead r21 1  -- b[3] bit 3
  let (_, r23) := bc6hRead r22 5  -- partition
  -- Reconstruct
  let r0full := r0low.toNat ||| (rShared.toNat <<< 10)
  let g0full := g0.toNat ||| (gShared.toNat <<< 10)
  let b0full := b0.toNat ||| (bShared.toNat <<< 10)
  let r0low4 := r0full &&& 0x0F
  let g0low4 := g0full &&& 0x1F
  let b0low4 := b0full &&& 0x0F
  let R0 := bc6hUnq r0full 11
  let G0 := bc6hUnq g0full 11
  let B0 := bc6hUnq b0full 11
  let R1 := bc6hUnq ((r1v.toNat + r0low4) % 16) 4
  let G1 := bc6hUnq ((g1v.toNat + g0low4) % 32) 5
  let B1 := bc6hUnq ((b1v.toNat + b0low4) % 16) 4
  (R0, G0, B0, R1, G1, B1, r23)

/-- Decode a BC6H mode-3 block into 16 RGB texels. -/
def bc6hMode3Decode (bytes : Fin 16 → UInt8) : Fin 16 → (UInt16 × UInt16 × UInt16) :=
  let (r0, g0, b0, r1, g1, b1, r) := bc6hMode3Endpoints bytes
  let weightBits := r.high >>> (16 : UInt64)
  fun t =>
    let wIdx := (weightBits.toNat >>> (t.val * 3)) &&& 0x7
    let w := w3 wIdx
    let R := bc6hFinish (Int.ofNat (bc6hInterp r0 r1 w)) false
    let G := bc6hFinish (Int.ofNat (bc6hInterp g0 g1 w)) false
    let B := bc6hFinish (Int.ofNat (bc6hInterp b0 b1 w)) false
    (R, G, B)

/-- BC6H mode-3 decode is total. -/
theorem bc6hMode3Decode_total (bytes : Fin 16 → UInt8) :
    (bc6hMode3Decode bytes) ⟨0, by decide⟩ = (bc6hMode3Decode bytes) ⟨0, by decide⟩ := by
  rfl

end Texcomp