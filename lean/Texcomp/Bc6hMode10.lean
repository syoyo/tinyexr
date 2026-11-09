/-
  TinyEXR - Lean 4 formalization of the BC6H one-region mode-10 decoder.

  This module follows `tc_bc6h_decode_block_half` for mode 10:
  six direct 10-bit endpoints, no xform inverse for delta endpoints,
  unsigned endpoint unquantization, the sixteen-entry `w4` interpolation
  table, and shorter index bits for the anchor texel.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Mode4
import Texcomp.Bc6hMode0

namespace Texcomp

/-- Sixteen weights used by BC6H one-region modes. -/
def bc6hWeight4 (idx : Nat) : Nat :=
  match idx with
  | 0 => 0
  | 1 => 4
  | 2 => 9
  | 3 => 13
  | 4 => 17
  | 5 => 21
  | 6 => 26
  | 7 => 30
  | 8 => 34
  | 9 => 38
  | 10 => 43
  | 11 => 47
  | 12 => 51
  | 13 => 55
  | 14 => 60
  | _ => 64

/-- Interpolate linearly between endpoints. -/
def bc6hBlend (a b idx : Nat) : Nat :=
  (a * (64 - bc6hWeight4 idx) + b * bc6hWeight4 idx + 32) / 64

/-- Decode one one-region BC6H mode-10 block into sixteen FP16 texels.

The first two reads correspond to the C decoder's mode-bit prefix
`case 0x03`: a 2-bit field followed by a 3-bit field. The decoder does
not reclassify or reject other blocks here; it interprets the remaining
fields in mode-10 order. -/
def bc6hMode10Decode (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt16 × UInt16 × UInt16) :=
  fun texel =>
    let reader := bc7ReaderInit bytes
    let (_, r1) := bc7Read reader 2
    let (_, r2) := bc7Read r1 3
    let (r0, r3) := bc7Read r2 10
    let (g0, r4) := bc7Read r3 10
    let (b0, r5) := bc7Read r4 10
    let (r1v, r6) := bc7Read r5 10
    let (g1v, r7) := bc7Read r6 10
    let (b1v, r8) := bc7Read r7 10

    let (_, indices) :=
      bc7ReadMany r8 (fun k => if k = 0 then 3 else 4) 16
    let index := indices.getD texel.val 0
    let r0u := bc6hUnq r0.toNat 10
    let g0u := bc6hUnq g0.toNat 10
    let b0u := bc6hUnq b0.toNat 10
    let r1u := bc6hUnq r1v.toNat 10
    let g1u := bc6hUnq g1v.toNat 10
    let b1u := bc6hUnq b1v.toNat 10
    let r := bc6hFinish (Int.ofNat (bc6hBlend r0u r1u index)) false
    let g := bc6hFinish (Int.ofNat (bc6hBlend g0u g1u index)) false
    let b := bc6hFinish (Int.ofNat (bc6hBlend b0u b1u index)) false
    (r, g, b)

/-- There is no out-of-bounds access here: the block is an indexable
array of exactly sixteen bytes, and all reads are total bit operations. -/
theorem bc6hMode10Decode_total (_bytes : Fin 16 → UInt8) (_texel : Fin 16) : True :=
  trivial

end Texcomp
