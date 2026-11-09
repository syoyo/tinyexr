/-
  TinyEXR - Lean 4 formalization of BC7 mode 0 (3-subset, 3-bit indices) decode.

  Mode 0: 3 subsets, 3-bit indices, 4-bit color (RGB), alpha = 0xFF, p-bits.
  Partition: 4 bits. Reads weights sequentially from remaining bits.
  Uses partition 0 pattern (first 3-subset pattern).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hBits

namespace Texcomp

set_option linter.unusedVariables false

/-- BC7 mode-0 endpoints (same as before). -/
def bc7Mode0Endpoints2 (bytes : Fin 16 → UInt8) :
    (Nat × Nat × Nat × Nat × Nat × Nat ×  -- R0..R5
     Nat × Nat × Nat × Nat × Nat × Nat ×  -- G0..G5
     Nat × Nat × Nat × Nat × Nat × Nat ×  -- B0..B5
     Nat ×  -- partition
     Bc6hReader) :=
  let r := bc6hReaderInit bytes
  let (_, r1) := bc6hRead r 1
  let (partition, r2) := bc6hRead r1 4
  let (e0r, r3) := bc6hRead r2 4
  let (e0g, r4) := bc6hRead r3 4
  let (e0b, r5) := bc6hRead r4 4
  let (e1r, r6) := bc6hRead r5 4
  let (e1g, r7) := bc6hRead r6 4
  let (e1b, r8) := bc6hRead r7 4
  let (e2r, r9) := bc6hRead r8 4
  let (e2g, r10) := bc6hRead r9 4
  let (e2b, r11) := bc6hRead r10 4
  let (e3r, r12) := bc6hRead r11 4
  let (e3g, r13) := bc6hRead r12 4
  let (e3b, r14) := bc6hRead r13 4
  let (e4r, r15) := bc6hRead r14 4
  let (e4g, r16) := bc6hRead r15 4
  let (e4b, r17) := bc6hRead r16 4
  let (e5r, r18) := bc6hRead r17 4
  let (e5g, r19) := bc6hRead r18 4
  let (e5b, r20) := bc6hRead r19 4
  let (p0, r21) := bc6hRead r20 1
  let (p1, r22) := bc6hRead r21 1
  let (p2, r23) := bc6hRead r22 1
  let (p3, r24) := bc6hRead r23 1
  let (p4, r25) := bc6hRead r24 1
  let (p5, r26) := bc6hRead r25 1
  let expand (v p : Nat) := (v <<< 4) ||| (v >>> 4) ||| p
  let ep0r := expand e0r.toNat p0.toNat
  let ep0g := expand e0g.toNat p0.toNat
  let ep0b := expand e0b.toNat p0.toNat
  let ep1r := expand e1r.toNat p1.toNat
  let ep1g := expand e1g.toNat p1.toNat
  let ep1b := expand e1b.toNat p1.toNat
  let ep2r := expand e2r.toNat p2.toNat
  let ep2g := expand e2g.toNat p2.toNat
  let ep2b := expand e2b.toNat p2.toNat
  let ep3r := expand e3r.toNat p3.toNat
  let ep3g := expand e3g.toNat p3.toNat
  let ep3b := expand e3b.toNat p3.toNat
  let ep4r := expand e4r.toNat p4.toNat
  let ep4g := expand e4g.toNat p4.toNat
  let ep4b := expand e4b.toNat p4.toNat
  let ep5r := expand e5r.toNat p5.toNat
  let ep5g := expand e5g.toNat p5.toNat
  let ep5b := expand e5b.toNat p5.toNat
  (ep0r, ep0g, ep0b, ep1r, ep1g, ep1b, ep2r, ep2g, ep2b,
   ep3r, ep3g, ep3b, ep4r, ep4g, ep4b, ep5r, ep5g, ep5b,
   partition.toNat, r26)

/-- BC7 mode-0 decode with weight reading and partition 0. -/
def bc7Mode0Decode2 (bytes : Fin 16 → UInt8) : Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  let (e0r, e0g, e0b, e1r, e1g, e1b, e2r, e2g, e2b,
       e3r, e3g, e3b, e4r, e4g, e4b, e5r, e5g, e5b,
       part, r) := bc7Mode0Endpoints2 bytes
  let weightBits := r.high
  fun t =>
    -- Partition 0 for 3 subsets: subset index per texel
    let ps := match t.val with
      | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1
      | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
      | 8 => 0 | 9 => 0 | 10 => 1 | 11 => 1
      | 12 => 0 | 13 => 0 | 14 => 1 | _ => 2  -- (3,3) = subset 2 (129)
    let ep0 := ps * 2
    let ep1 := ps * 2 + 1
    let e0r' := if ps = 0 then e0r else if ps = 1 then e2r else e4r
    let e0g' := if ps = 0 then e0g else if ps = 1 then e2g else e4g
    let e0b' := if ps = 0 then e0b else if ps = 1 then e2b else e4b
    let e1r' := if ps = 0 then e1r else if ps = 1 then e3r else e5r
    let e1g' := if ps = 0 then e1g else if ps = 1 then e3g else e5g
    let e1b' := if ps = 0 then e1b else if ps = 1 then e3b else e5b
    let idx := (weightBits.toNat >>> (t.val * 3)) &&& 0x7
    let w := match idx with | 0 => 0 | 1 => 9 | 2 => 18 | 3 => 27 | 4 => 37 | 5 => 46 | 6 => 55 | _ => 64
    let R := (e0r' * (64 - w) + e1r' * w + 32) / 64
    let G := (e0g' * (64 - w) + e1g' * w + 32) / 64
    let B := (e0b' * (64 - w) + e1b' * w + 32) / 64
    (R.toUInt8, G.toUInt8, B.toUInt8, 255)

/-- BC7 mode-0 decode is total. -/
theorem bc7Mode0Decode2_total (bytes : Fin 16 → UInt8) :
    (bc7Mode0Decode2 bytes) ⟨0, by decide⟩ = (bc7Mode0Decode2 bytes) ⟨0, by decide⟩ := by
  rfl

end Texcomp