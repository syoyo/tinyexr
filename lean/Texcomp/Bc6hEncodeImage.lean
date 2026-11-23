/-
  TinyEXR - Lean 4 model of `tc_bc6h_compress_rgb32f`.

  Uses the already byte-exact `bc6hEncodeBlockUf16` / `bc6hEncodeBlockSf16`
  mode-selection drivers with edge-clamped 4x4 RGB (f32 bit patterns)
  gathering.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncodeBlock

namespace Texcomp

def bc6hCompressedSize2 (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 16

/-- Gather one 4x4 RGB tile as f32 bit patterns (row-major texels). -/
def bc6hGather (src : List UInt32) (w h : Nat) (bx bi : Nat) : List (List UInt32) :=
  (List.range 16).map (fun t =>
    let y0 := (bi / bx) * 4 + t / 4
    let x0 := (bi % bx) * 4 + t % 4
    let y := if y0 < h then y0 else h - 1
    let x := if x0 < w then x0 else w - 1
    let base := (y * w + x) * 3
    [src.getD base 0, src.getD (base + 1) 0, src.getD (base + 2) 0])

def bc6hCompressImage (src : List UInt32) (w h : Nat) (signedFloat : Bool) : Option (List Nat) :=
  if w == 0 || h == 0 then none
  else if src.length < w * h * 3 then none
  else
    let bx := (w + 3) / 4
    some ((List.range (((w + 3) / 4) * ((h + 3) / 4))).foldr (fun bi acc =>
      let px := bc6hGather src w h bx bi
      (if signedFloat then bc6hEncodeBlockSf16 px else bc6hEncodeBlockUf16 px) ++ acc) [])

theorem bc6hCompressImage_none_small (src : List UInt32) (w h : Nat) (sf : Bool)
    (hsmall : src.length < w * h * 3) :
    bc6hCompressImage src w h sf = none := by
  unfold bc6hCompressImage
  by_cases hw : w == 0 || h == 0
  · simp [hw]
  · simp [hw, hsmall]

end Texcomp
