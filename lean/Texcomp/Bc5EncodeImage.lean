/-
  TinyEXR - Lean 4 model of the public BC5 image compressors.

  Ports `tc_bc5_compress_rg8` / `tc_bc5_compress_rgba8` (unorm and snorm
  variants): edge-clamped 4x4 block gather feeding the already byte-exact
  `encodeBc5Block` / `encodeBc5BlockSnorm` models.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc4Encode

namespace Texcomp

def bc5CompressedSize (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 16

/-- Gather one 4x4 RG plane from a row-major source image. -/
def bc5Gather (src : List Nat) (w h bpp : Nat) (bx bi chan : Nat) : List Nat :=
  (List.range 16).map (fun t =>
    let y0 := (bi / bx) * 4 + t / 4
    let x0 := (bi % bx) * 4 + t % 4
    let y := if y0 < h then y0 else h - 1
    let x := if x0 < w then x0 else w - 1
    src.getD ((y * w + x) * bpp + chan) 0)

/-- `tc_bc5_compress_*` for one image. `rgba = true` selects the 4-byte
  source layout; `snorm` selects the signed block encoder. -/
def bc5CompressImage (src : List Nat) (w h : Nat) (rgba snorm : Bool) : Option (List Nat) :=
  let bpp := if rgba then 4 else 2
  if w == 0 || h == 0 then none
  else if src.length < w * h * bpp then none
  else
    let bx := (w + 3) / 4
    some ((List.range (((w + 3) / 4) * ((h + 3) / 4))).foldr (fun bi acc =>
      let r := bc5Gather src w h bpp bx bi 0
      let g := bc5Gather src w h bpp bx bi 1
      let blk := if snorm then encodeBc5BlockSnorm r g else encodeBc5Block r g
      blk ++ acc) [])

theorem bc5CompressImage_none_small (src : List Nat) (w h : Nat) (rgba snorm : Bool)
    (hsmall : src.length < w * h * (if rgba then 4 else 2)) :
    bc5CompressImage src w h rgba snorm = none := by
  unfold bc5CompressImage
  by_cases hw : w == 0 || h == 0
  · simp [hw]
  · simp [hw, hsmall]

end Texcomp
