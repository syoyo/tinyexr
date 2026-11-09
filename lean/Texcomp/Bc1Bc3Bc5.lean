/-
  TinyEXR - Lean 4 formalization of the BC1/BC3/BC4/BC5 block decoders.

  Faithful ports of `tc_decode_bc1_color_block` (`texcomp_bc1.c`),
  `tc_decode_bc4_block` + `tc_decode_bc4_block_snorm` (`texcomp_bc5.c`)
  and the block compositions in `tc_bc3_decompress_rgba8` /
  `tc_bc5_decompress_rgba8`.

  Boundary: `tc_snorm8_to_unorm8` (the BC5 snorm→unorm8 re-expression)
  is float-based and is NOT modelled; `bc5SnormValues` exposes the exact
  integer step before it. This mirrors the B44 perceptual-table boundary
  (C-side numerical test is the agreed bar).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Std.Tactic.BVDecide

namespace Texcomp

set_option linter.unusedVariables false

/-- RGB565 unpack (`tc_rgb565_unpack`): bit-replication expansion. -/
def rgb565Unpack (c : UInt16) : Nat × Nat × Nat :=
  let r := ((c >>> 11) &&& 0x1f).toNat
  let g := ((c >>> 5) &&& 0x3f).toNat
  let b := (c &&& 0x1f).toNat
  ((r <<< 3) ||| (r >>> 2), (g <<< 2) ||| (g >>> 4), (b <<< 3) ||| (b >>> 2))

/-- Read two little-endian bytes. -/
def readU16LE (bytes : Fin 8 → UInt8) (i j : Fin 8) : UInt16 :=
  (bytes i).toUInt16 ||| ((bytes j).toUInt16 <<< 8)

/-- Signed interpretation of a stored byte (two's-complement int8). -/
def snormByte (b : UInt8) : Int :=
  let v := b.toNat
  if v >= 128 then (Int.ofNat v) - 256 else Int.ofNat v

/-- BC1 colour palette: 4 entries of RGBA8. -/
def bc1PaletteF (c0 c1 : UInt16) (dxt1 : Bool) : List (Nat × Nat × Nat × Nat) :=
  let (p0r, p0g, p0b) := rgb565Unpack c0
  let (p1r, p1g, p1b) := rgb565Unpack c1
  let three := dxt1 && c0 <= c1
  let mix := fun a b => if three then (a + b) / 2 else (2 * a + b + 1) / 3
  let mix2 := fun a b => if three then 0 else (a + 2 * b + 1) / 3
  [(p0r, p0g, p0b, 255),
   (p1r, p1g, p1b, 255),
   (mix p0r p1r, mix p0g p1g, mix p0b p1b, 255),
   (mix2 p0r p1r, mix2 p0g p1g, mix2 p0b p1b, if three then 0 else 255)]

/-- Decode one BC1 colour block (8 bytes) to 16 RGBA8 texels. -/
def bc1ColorDecode (bytes : Fin 8 → UInt8) (dxt1 : Bool) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let c0 := readU16LE bytes 0 1
    let c1 := readU16LE bytes 2 3
    let bits := (bytes 4).toUInt32
      ||| ((bytes 5).toUInt32 <<< 8)
      ||| ((bytes 6).toUInt32 <<< 16)
      ||| ((bytes 7).toUInt32 <<< 24)
    let idx := ((bits >>> (UInt32.ofNat (2 * texel.val))) &&& 3).toNat
    let (r, g, b, a) := (bc1PaletteF c0 c1 dxt1).getD idx (0, 0, 0, 255)
    (UInt8.ofNat r, UInt8.ofNat g, UInt8.ofNat b, UInt8.ofNat a)

/-- BC4 palette (unsigned): 8 values. -/
def bc4PaletteU (r0 r1 : Nat) : List Nat :=
  if r0 > r1 then
    [r0, r1,
     (6 * r0 + 1 * r1 + 3) / 7, (5 * r0 + 2 * r1 + 3) / 7,
     (4 * r0 + 3 * r1 + 3) / 7, (3 * r0 + 4 * r1 + 3) / 7,
     (2 * r0 + 5 * r1 + 3) / 7, (1 * r0 + 6 * r1 + 3) / 7]
  else
    [r0, r1,
     (4 * r0 + 1 * r1 + 2) / 5, (3 * r0 + 2 * r1 + 2) / 5,
     (2 * r0 + 3 * r1 + 2) / 5, (1 * r0 + 4 * r1 + 2) / 5,
     0, 255]

/-- Decode one BC4 block (8 bytes) to 16 values. -/
def bc4Decode (bytes : Fin 8 → UInt8) : Fin 16 → UInt8 :=
  fun texel =>
    let r0 := (bytes 0).toNat
    let r1 := (bytes 1).toNat
    let bits := (bytes 2).toUInt64
      ||| ((bytes 3).toUInt64 <<< 8)
      ||| ((bytes 4).toUInt64 <<< 16)
      ||| ((bytes 5).toUInt64 <<< 24)
      ||| ((bytes 6).toUInt64 <<< 32)
      ||| ((bytes 7).toUInt64 <<< 40)
    let idx := ((bits >>> (UInt64.ofNat (3 * texel.val))) &&& 7).toNat
    UInt8.ofNat ((bc4PaletteU r0 r1).getD idx 0)

/-- C-style truncating division (toward zero), for signed palettes. -/
def truncDiv (a b : Int) : Int :=
  if a >= 0 then a / b else -((-a) / b)

/-- BC4 signed palette (exact integer step of `tc_decode_bc4_block_snorm`). -/
def bc4SnormPalette (r0 r1 : Int) : List Int :=
  if r0 > r1 then
    [r0, r1,
     truncDiv (6 * r0 + 1 * r1) 7, truncDiv (5 * r0 + 2 * r1) 7,
     truncDiv (4 * r0 + 3 * r1) 7, truncDiv (3 * r0 + 4 * r1) 7,
     truncDiv (2 * r0 + 5 * r1) 7, truncDiv (1 * r0 + 6 * r1) 7]
  else
    [r0, r1,
     truncDiv (4 * r0 + 1 * r1) 5, truncDiv (3 * r0 + 2 * r1) 5,
     truncDiv (2 * r0 + 3 * r1) 5, truncDiv (1 * r0 + 4 * r1) 5,
     -127, 127]

/-- Decode one signed BC4 block to 16 signed values (with -128→-127 clamp). -/
def bc4SnormDecode (bytes : Fin 8 → UInt8) : Fin 16 → Int :=
  fun texel =>
    let r0 := snormByte (bytes 0)
    let r1 := snormByte (bytes 1)
    let bits := (bytes 2).toUInt64
      ||| ((bytes 3).toUInt64 <<< 8)
      ||| ((bytes 4).toUInt64 <<< 16)
      ||| ((bytes 5).toUInt64 <<< 24)
      ||| ((bytes 6).toUInt64 <<< 32)
      ||| ((bytes 7).toUInt64 <<< 40)
    let idx := ((bits >>> (UInt64.ofNat (3 * texel.val))) &&& 7).toNat
    let p := (bc4SnormPalette r0 r1).getD idx 0
    if p < -127 then -127 else p

/-- BC3 block (16 bytes): BC4 alpha + BC1 colour (always 4-colour). -/
def bc3Decode (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let alphaBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val, by omega⟩
    let colorBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val + 8, by omega⟩
    let (r, g, b, _) := bc1ColorDecode colorBlock false texel
    (r, g, b, bc4Decode alphaBlock texel)

/-- BC5 block (16 bytes), unsigned: RG + B=0, A=255. -/
def bc5Decode (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let rBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val, by omega⟩
    let gBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val + 8, by omega⟩
    (bc4Decode rBlock texel, bc4Decode gBlock texel, 0, 255)

/-- BC5 signed pre-float values: per-texel (r, g) pairs before
  `tc_snorm8_to_unorm8`. -/
def bc5SnormValues (bytes : Fin 16 → UInt8) :
    Fin 16 → (Int × Int) :=
  fun texel =>
    let rBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val, by omega⟩
    let gBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val + 8, by omega⟩
    (bc4SnormDecode rBlock texel, bc4SnormDecode gBlock texel)

/-- Totality by construction. -/
theorem bc1ColorDecode_total (_bytes : Fin 8 → UInt8) (_dxt1 : Bool)
    (_texel : Fin 16) : True :=
  trivial

/-- BC4 palette has 8 entries. -/
theorem bc4PaletteU_length (r0 r1 : Nat) : (bc4PaletteU r0 r1).length = 8 := by
  unfold bc4PaletteU
  split <;> rfl



end Texcomp
