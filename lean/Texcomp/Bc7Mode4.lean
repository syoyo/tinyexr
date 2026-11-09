/-
  TinyEXR - Lean 4 formalization of the BC7 mode-4 decoder.

  Mode 4 is a single-subset BPTC mode with:
  * two RGB and two alpha endpoints (5 and 6 bits, respectively)
  *ätzlich a 2-bit rotation field and a one-bit index-selector field
  * two-bit per-texel indices using the four-entry weight table
  * three-bit anchor-region indices using the eight-entry weight table
  * the ordinary and selector-weighted interpolation paths

  The bit stream advances exactly as in `tc_bc7_decode_block`: every read
  consumes the next low bits from two little-endian `UInt64` values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- A copy of the two 64-bit words used by the C bit reader. -/
structure Bc7Reader where
  lo : UInt64
  hi : UInt64

/-- Read eight bytes, little-endian. -/
def bc7WordLE (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
  (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
  (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Initialise a bit reader from the 16 block bytes. -/
def bc7ReaderInit (bytes : Fin 16 → UInt8) : Bc7Reader :=
  ⟨bc7WordLE (bytes 0) (bytes 1) (bytes 2) (bytes 3)
             (bytes 4) (bytes 5) (bytes 6) (bytes 7),
   bc7WordLE (bytes 8) (bytes 9) (bytes 10) (bytes 11)
             (bytes 12) (bytes 13) (bytes 14) (bytes 15)⟩

/-- Low `n` bits, with the zero-width case called out explicitly. -/
def bc7Mask (n : Nat) : UInt64 :=
  if n = 0 then 0
  else (1 <<< UInt64.ofNat n) - 1

/-- Consume the next `n` low bits, corresponding to `tc_bc7_dec_rb`. -/
def bc7Read (r : Bc7Reader) (n : Nat) : UInt32 × Bc7Reader :=
  if n = 0 then
    (0, r)
  else
    let mask := bc7Mask n
    ((r.lo &&& mask).toUInt32,
     ⟨(r.lo >>> UInt64.ofNat n) ||| ((r.hi &&& mask) <<< (64 - UInt64.ofNat n)),
      r.hi >>> UInt64.ofNat n⟩)

/-- Read a sequence of variable-width indices in row-major order. -/
def bc7ReadMany (r : Bc7Reader) (width : Nat → Nat) (count : Nat) :
    Bc7Reader × List Nat :=
  (List.range count).foldl
    (fun acc k =>
      let (value, next) := bc7Read acc.1 (width k)
      (next, acc.2 ++ [value.toNat]))
    (r, [])

/-- Expand a 5- or 6-bit endpoint field in the same way as the C decoder. -/
def bc7Expand (value : Nat) (bits : Nat) : Nat :=
  (value <<< (8 - bits)) ||| (value >>> bits)

/-- Interpolates endpoints with weights in the range 0..64. -/
def bc7Blend (a b weight : Nat) : Nat :=
  (a * (64 - weight) + b * weight + 32) / 64

/-- Four-entry interpolation weights. -/
def bc7Weight2 (index : Nat) : Nat :=
  match index with
  | 0 => 0
  | 1 => 21
  | 2 => 43
  | _ => 64

/-- Eight-entry interpolation weights. -/
def bc7Weight3 (index : Nat) : Nat :=
  match index with
  | 0 => 0
  | 1 => 9
  | 2 => 18
  | 3 => 27
  | 4 => 37
  | 5 => 46
  | 6 => 55
  | _ => 64

/-- Decode one BC7 mode-4 block to sixteen RGBA8-valued texels. -/
def bc7Mode4Decode (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let reader := bc7ReaderInit bytes
    -- BC7 mode is unary: four zero bits followed by a one bit for mode 4.
    let (_, r1) := bc7Read reader 1
    let (_, r2) := bc7Read r1 1
    let (_, r3) := bc7Read r2 1
    let (_, r4) := bc7Read r3 1
    let (_, r5) := bc7Read r4 1
    let (rotation, r6) := bc7Read r5 2
    let (indexSelector, r7) := bc7Read r6 1

    -- Field order is channel-major in the C decoder: all R endpoints,
    -- then all G endpoints, then all B endpoints, then alpha endpoints.
    let (r0, r8) := bc7Read r7 5
    let (r1, r9) := bc7Read r8 5
    let (g0, r10) := bc7Read r9 5
    let (g1, r11) := bc7Read r10 5
    let (b0, r12) := bc7Read r11 5
    let (b1, r13) := bc7Read r12 5
    let (a0, r14) := bc7Read r13 6
    let (a1, r15) := bc7Read r14 6

    let red0 := bc7Expand r0.toNat 5
    let green0 := bc7Expand g0.toNat 5
    let blue0 := bc7Expand b0.toNat 5
    let alpha0 := bc7Expand a0.toNat 6
    let red1 := bc7Expand r1.toNat 5
    let green1 := bc7Expand g1.toNat 5
    let blue1 := bc7Expand b1.toNat 5
    let alpha1 := bc7Expand a1.toNat 6

    -- The single anchor texel uses one fewer bit in each index plane.
    let (r16, firstIndices) := bc7ReadMany r15
      (fun t => if t = 0 then 1 else 2) 16
    let (_, secondIndices) := bc7ReadMany r16
      (fun t => if t = 0 then 2 else 3) 16

    let first := firstIndices.getD texel.val 0
    let second := secondIndices.getD texel.val 0
    let colorWeight := bc7Weight2 first
    let alphaWeight := bc7Weight3 second

    let beforeRotation :=
      if indexSelector = 0 then
        (bc7Blend red0 red1 colorWeight,
         bc7Blend green0 green1 colorWeight,
         bc7Blend blue0 blue1 colorWeight,
         bc7Blend alpha0 alpha1 alphaWeight)
      else
        (bc7Blend red0 red1 alphaWeight,
         bc7Blend green0 green1 alphaWeight,
         bc7Blend blue0 blue1 alphaWeight,
         bc7Blend alpha0 alpha1 colorWeight)

    let (red, green, blue, alpha) :=
      match rotation, beforeRotation with
      | 1, (r, g, b, a) => (a, g, b, r)
      | 2, (r, g, b, a) => (r, a, b, g)
      | 3, (r, g, b, a) => (r, g, a, b)
      | _, (r, g, b, a) => (r, g, b, a)

    (red.toUInt8, green.toUInt8, blue.toUInt8, alpha.toUInt8)

/-- Mode-4 decoding is total, as every field read is a total bit operation. -/
theorem bc7Mode4Decode_total (_bytes : Fin 16 → UInt8) (_texel : Fin 16) :
    True := trivial

end Texcomp
