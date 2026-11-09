/-
  TinyEXR - Lean 4 formalization of the BC1 block decoder (2/4-color modes).

  Models the single-block decode: parse two RGB565 endpoints + 16 2-bit
  indices, build the 4- (or 3-) color palette, and look up a texel.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc1

namespace Texcomp

def expand5 (v : UInt16) : UInt8 := (v.toUInt8 <<< 3) ||| (v.toUInt8 >>> 2)
def expand6 (v : UInt16) : UInt8 := (v.toUInt8 <<< 2) ||| (v.toUInt8 >>> 4)

def rgb565ToR (c : UInt16) : UInt8 := expand5 ((c >>> 11) &&& 0x1f)
def rgb565ToG (c : UInt16) : UInt8 := expand6 ((c >>> 5) &&& 0x3f)
def rgb565ToB (c : UInt16) : UInt8 := expand5 (c &&& 0x1f)

structure Color4 where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8

def u16le (lo hi : UInt8) : UInt16 :=
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

def avg2 (a b : Nat) : UInt8 := ((a + b) / 2).toUInt8

def palette4 (c0 c1 : UInt16) : Fin 4 → Color4 :=
  fun i => match i.val with
    | 0 => { r := rgb565ToR c0, g := rgb565ToG c0, b := rgb565ToB c0, a := 255 }
    | 1 => { r := rgb565ToR c1, g := rgb565ToG c1, b := rgb565ToB c1, a := 255 }
    | 2 => { r := ((rgb565ToR c0).toNat * 2 + (rgb565ToR c1).toNat) / 3 |>.toUInt8,
             g := ((rgb565ToG c0).toNat * 2 + (rgb565ToG c1).toNat) / 3 |>.toUInt8,
             b := ((rgb565ToB c0).toNat * 2 + (rgb565ToB c1).toNat) / 3 |>.toUInt8,
             a := 255 }
    | _ => { r := ((rgb565ToR c0).toNat + (rgb565ToR c1).toNat * 2) / 3 |>.toUInt8,
             g := ((rgb565ToG c0).toNat + (rgb565ToG c1).toNat * 2) / 3 |>.toUInt8,
             b := ((rgb565ToB c0).toNat + (rgb565ToB c1).toNat * 2) / 3 |>.toUInt8,
             a := 255 }

def palette3 (c0 c1 : UInt16) : Fin 4 → Color4 :=
  fun i => match i.val with
    | 0 => { r := rgb565ToR c0, g := rgb565ToG c0, b := rgb565ToB c0, a := 255 }
    | 1 => { r := rgb565ToR c1, g := rgb565ToG c1, b := rgb565ToB c1, a := 255 }
    | 2 => { r := avg2 (rgb565ToR c0).toNat (rgb565ToR c1).toNat,
             g := avg2 (rgb565ToG c0).toNat (rgb565ToG c1).toNat,
             b := avg2 (rgb565ToB c0).toNat (rgb565ToB c1).toNat,
             a := 255 }
    | _ => { r := 0, g := 0, b := 0, a := 0 }

def bc1Palette (c0 c1 : UInt16) : Fin 4 → Color4 :=
  if c0.toNat > c1.toNat then palette4 c0 c1 else palette3 c0 c1

def bc1Index (idxBytes : Fin 4 → UInt8) (texel : Fin 16) : Fin 4 :=
  let byteIdx := texel.val / 4
  let shift := (texel.val % 4) * 2
  let b := idxBytes ⟨byteIdx, by omega⟩
  ⟨(b.toNat >>> shift) % 4, by omega⟩

def bc1DecodeBlock (bytes : Fin 8 → UInt8) : Fin 16 → Color4 :=
  let c0 := u16le (bytes 0) (bytes 1)
  let c1 := u16le (bytes 2) (bytes 3)
  let idxBytes : Fin 4 → UInt8 := fun i => bytes ⟨4 + i.val, by omega⟩
  let pal := bc1Palette c0 c1
  fun t => pal (bc1Index idxBytes t)

theorem bc1BlockSize_decode : (8 : Nat) = 8 := rfl

/-- In 3-color mode, palette index 3 is transparent black. -/
theorem bc1_palette3_idx3 (c0 c1 : UInt16) (h : c0.toNat ≤ c1.toNat) :
    bc1Palette c0 c1 ⟨3, by decide⟩ =
      { r := 0, g := 0, b := 0, a := 0 } := by
  unfold bc1Palette
  have hcond : ¬ (c0.toNat > c1.toNat) := by omega
  simp [hcond]
  unfold palette3
  simp

/-- In 4-color mode, palette index 3 is opaque (alpha = 255). -/
theorem bc1_palette4_idx3_opaque (c0 c1 : UInt16) (h : c0.toNat > c1.toNat) :
    (bc1Palette c0 c1 ⟨3, by decide⟩).a = 255 := by
  unfold bc1Palette
  have hcond : c0.toNat > c1.toNat := h
  simp [hcond]
  unfold palette4
  simp

end Texcomp