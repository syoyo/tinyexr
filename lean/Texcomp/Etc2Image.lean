/-
  TinyEXR - Lean 4 formalization of the ETC2 / EAC full-image decoders.

  Mirrors `tc_etc2_decompress_rgba8` and `tc_eac_decompress_rgba8`:
  row-major RGBA8 output, partial blocks skipped, alpha forced to 255 for
  ETC2 RGB and EAC. Bit-exact via `make texcomp-etc2-img-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Etc2AllModes

namespace Texcomp

/-- Bytes per ETC2 RGB / EAC R11 block. -/
def etc2RgbBlockBytes : Nat := 8
/-- Bytes per ETC2 RGBA / EAC RG11 block. -/
def etc2RgbaBlockBytes : Nat := 16

def etc2RgbImageBytes (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 8
def etc2RgbaImageBytes (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 16
def eacR11ImageBytes (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 8
def eacRg11ImageBytes (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 16

def etc2Byte (data : List UInt8) (i : Nat) : UInt8 := data.getD i 0

def etc2Block8 (data : List UInt8) (bi : Nat) : Fin 8 → UInt8 :=
  fun i => etc2Byte data (bi * 8 + i.val)

def etc2Block16 (data : List UInt8) (bi : Nat) : Fin 16 → UInt8 :=
  fun i => etc2Byte data (bi * 16 + i.val)

/-- One output pixel of an ETC2 image (alpha selects RGBA blocks). -/
def etc2Pixel (data : List UInt8) (bx : Nat) (alpha : Bool) (k w : Nat) : List UInt8 :=
  let x := k % w
  let y := k / w
  let bi := (y / 4) * bx + x / 4
  let t := (y % 4) * 4 + x % 4
  let px : UInt8 × UInt8 × UInt8 × UInt8 :=
    if alpha then etc2RgbaDecode (etc2Block16 data bi) ⟨t, by omega⟩
    else
      let (r, g, b, _) := etc2RgbDecode (etc2Block8 data bi) ⟨t, by omega⟩
      (r, g, b, 255)
  [px.1, px.2.1, px.2.2.1, px.2.2.2]

theorem etc2Pixel_length (data : List UInt8) (bx k w : Nat) (alpha : Bool) :
    (etc2Pixel data bx alpha k w).length = 4 := by
  simp [etc2Pixel]

/-- Decode an ETC2 image. -/
def etc2DecodeImage (data : List UInt8) (w h : Nat) (alpha : Bool) : Option (List UInt8) :=
  let needed := if alpha then etc2RgbaImageBytes w h else etc2RgbImageBytes w h
  if data.length < needed then none
  else
    let bx := (w + 3) / 4
    if w == 0 || h == 0 then some []
    else
      some ((List.range (w * h)).foldr
        (fun k acc => etc2Pixel data bx alpha k w ++ acc) [])

theorem etc2DecodeImage_none_if_small_rgb (data : List UInt8) (w h : Nat)
    (hsmall : data.length < etc2RgbImageBytes w h) :
    etc2DecodeImage data w h false = none := by
  unfold etc2DecodeImage
  simp [hsmall]

theorem etc2DecodeImage_none_if_small_rgba (data : List UInt8) (w h : Nat)
    (hsmall : data.length < etc2RgbaImageBytes w h) :
    etc2DecodeImage data w h true = none := by
  unfold etc2DecodeImage
  simp [hsmall]

theorem etc2RgbBlockBytes_pos : etc2RgbBlockBytes > 0 := by decide
theorem etc2RgbaBlockBytes_pos : etc2RgbaBlockBytes > 0 := by decide

end Texcomp
