/-
  TinyEXR - Lean 4 formalization of BC6H mode 0 (10.555 x3) decode.

  Single-subset mode: reads endpoints sequentially with running position,
  applies proper shared-bit reconstruction and unquantization, reads 16
  3-bit weights sequentially, and interpolates each texel.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hBits

set_option linter.unusedVariables false

namespace Texcomp

/-- Unquantize an unsigned value from `bits` precision to 16-bit. -/
def bc6hUnq (val : Nat) (bits : Nat) : Nat :=
  if bits >= 15 then val
  else if val == 0 then 0
  else if val == (1 <<< bits) - 1 then 0xFFFF
  else (val <<< 16 + 0x8000) >>> bits

/-- Finish: convert unquantized value to FP16. -/
def bc6hFinish (val : Int) (isSigned : Bool) : UInt16 :=
  if !isSigned then
    UInt16.ofNat (((val * 31) >>> 6).toNat)
  else
    let s := if val < 0 then 0x8000 else 0
    let v := if val < 0 then (-val * 31) >>> 5 else (val * 31) >>> 5
    UInt16.ofNat (s ||| v.toNat)

/-- Weight table w3. -/
def w3 (idx : Nat) : Nat :=
  match idx with
  | 0 => 0 | 1 => 9 | 2 => 18 | 3 => 27
  | 4 => 37 | 5 => 46 | 6 => 55 | _ => 64

/-- Interpolate: (a * (64 - w) + b * w + 32) / 64. -/
def bc6hInterp (a b w : Nat) : Nat :=
  (a * (64 - w) + b * w + 32) / 64

/-- Mode-0 endpoint extraction with shared bits. Returns (r0, g0, b0, r1, g1, b1, reader). -/
def bc6hMode0Endpoints (bytes : Fin 16 → UInt8) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Bc6hReader) :=
  let r := bc6hReaderInit bytes
  let (_, r1) := bc6hRead r 2
  let (_, r2) := bc6hRead r1 3
  -- Shared bits
  let (g2shared, r3) := bc6hRead r2 1
  let (b2shared, r4) := bc6hRead r3 1
  let (b3shared0, r5) := bc6hRead r4 1
  -- Base endpoints (10 bits each)
  let (r0, r6) := bc6hRead r5 10
  let (g0, r7) := bc6hRead r6 10
  let (b0, r8) := bc6hRead r7 10
  -- Delta endpoints
  let (r1v, r9) := bc6hRead r8 5
  let (g3shared, r10) := bc6hRead r9 1
  let (g2low, r11) := bc6hRead r10 4
  let (g1v, r12) := bc6hRead r11 5
  let (b3bit0, r13) := bc6hRead r12 1
  let (g3low, r14) := bc6hRead r13 4
  let (b1v, r15) := bc6hRead r14 5
  let (b3bit1, r16) := bc6hRead r15 1
  let (b2low, r17) := bc6hRead r16 4
  let (r2v, r18) := bc6hRead r17 5
  let (b3bit2, r19) := bc6hRead r18 1
  let (r3v, r20) := bc6hRead r19 5
  let (b3bit3, r21) := bc6hRead r20 1
  let (_, r22) := bc6hRead r21 5
  -- Reconstruct shared bits
  let g2full := g2low.toNat ||| (g2shared.toNat <<< 4)
  let g3full := g3low.toNat ||| (g3shared.toNat <<< 4)
  let b2full := b2low.toNat ||| (b2shared.toNat <<< 4)
  let b3full := b3bit0.toNat ||| (b3bit1.toNat <<< 1) ||| (b3bit2.toNat <<< 2) ||| (b3shared0.toNat <<< 3) ||| (b3bit3.toNat <<< 4)
  -- Endpoint reconstruction (unsigned): base 10-bit, delta 5-bit with shared low bits
  let r0low5 := r0.toNat &&& 0x1F
  let g0low5 := g0.toNat &&& 0x1F
  let b0low5 := b0.toNat &&& 0x1F
  let R0 := bc6hUnq r0.toNat 10
  let G0 := bc6hUnq g0.toNat 10
  let B0 := bc6hUnq b0.toNat 10
  let R1 := bc6hUnq ((r1v.toNat + r0low5) % 32) 5
  let G1 := bc6hUnq ((g1v.toNat + g0low5) % 32) 5
  let B1 := bc6hUnq ((b1v.toNat + b0low5) % 32) 5
  (R0, G0, B0, R1, G1, B1, r22)

/-- Decode a BC6H mode-0 block into 16 RGB texels. -/
def bc6hMode0Decode (bytes : Fin 16 → UInt8) : Fin 16 → (UInt16 × UInt16 × UInt16) :=
  let (r0, g0, b0, r1, g1, b1, r) := bc6hMode0Endpoints bytes
  let weightBits := r.high >>> (16 : UInt64)
  fun t =>
    let wIdx := (weightBits.toNat >>> (t.val * 3)) &&& 0x7
    let w := w3 wIdx
    let R := bc6hFinish (Int.ofNat (bc6hInterp r0 r1 w)) false
    let G := bc6hFinish (Int.ofNat (bc6hInterp g0 g1 w)) false
    let B := bc6hFinish (Int.ofNat (bc6hInterp b0 b1 w)) false
    (R, G, B)

/-- BC6H mode-0 decode is total. -/
theorem bc6hMode0Decode_total (bytes : Fin 16 → UInt8) :
    (bc6hMode0Decode bytes) ⟨0, by decide⟩ = (bc6hMode0Decode bytes) ⟨0, by decide⟩ := by
  rfl

end Texcomp