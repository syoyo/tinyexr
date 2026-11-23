/-
  TinyEXR - Lean 4 formalization of the EAC full-image decoder.

  Mirrors `tc_eac_decompress_rgba8`: row-major RGBA8 output, R11 or RG11,
  B=0 and A=255. Bit-exact via `make texcomp-etc2-img-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Etc2Image

namespace Texcomp

/-- Bytes per EAC R11 block. -/
def eacR11BlockBytes : Nat := 8
/-- Bytes per EAC RG11 block. -/
def eacRg11BlockBytes : Nat := 16


/-- One output pixel of an EAC image (R11 or RG11). -/
def eacPixel (data : List UInt8) (bx : Nat) (rg11 : Bool) (k w : Nat) : List UInt8 :=
  let x := k % w
  let y := k / w
  let bi := (y / 4) * bx + x / 4
  let t := (y % 4) * 4 + x % 4
  let r := eacR11Decode (etc2Block8 data (if rg11 then bi * 2 else bi)) ⟨t, by omega⟩
  let g := if rg11 then eacR11Decode (etc2Block8 data (bi * 2 + 1)) ⟨t, by omega⟩ else 0
  [r, g, 0, 255]

theorem eacPixel_length (data : List UInt8) (bx k w : Nat) (rg11 : Bool) :
    (eacPixel data bx rg11 k w).length = 4 := by
  simp [eacPixel]

/-- Decode an EAC R11 / RG11 image. -/
def eacDecodeImage (data : List UInt8) (w h : Nat) (rg11 : Bool) : Option (List UInt8) :=
  let needed := if rg11 then eacRg11ImageBytes w h else eacR11ImageBytes w h
  if data.length < needed then none
  else
    let bx := (w + 3) / 4
    if w == 0 || h == 0 then some []
    else
      some ((List.range (w * h)).foldr
        (fun k acc => eacPixel data bx rg11 k w ++ acc) [])

theorem eacDecodeImage_none_if_small_r11 (data : List UInt8) (w h : Nat)
    (hsmall : data.length < eacR11ImageBytes w h) :
    eacDecodeImage data w h false = none := by
  unfold eacDecodeImage
  simp [hsmall]

theorem eacDecodeImage_none_if_small_rg11 (data : List UInt8) (w h : Nat)
    (hsmall : data.length < eacRg11ImageBytes w h) :
    eacDecodeImage data w h true = none := by
  unfold eacDecodeImage
  simp [hsmall]

theorem eacR11BlockBytes_pos : eacR11BlockBytes > 0 := by decide
theorem eacRg11BlockBytes_pos : eacRg11BlockBytes > 0 := by decide

end Texcomp
