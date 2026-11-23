/-
  TinyEXR - Lean 4 model of `tc_bc7_compress_rgba8` (default options).

  Uses the already byte-exact `bc7EncodeBlockDefault` block driver
  (`quick = 2`, `pca_endpoints = 0`, no RDO) with edge-clamped row-major
  4x4 gathering.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7EncodeAll

namespace Texcomp

def bc7CompressedSize2 (w h : Nat) : Nat := ((w + 3) / 4) * ((h + 3) / 4) * 16

def bc7Gather (src : List Nat) (w h : Nat) (bx bi : Nat) : List (List Nat) :=
  (List.range 16).map (fun t =>
    let y0 := (bi / bx) * 4 + t / 4
    let x0 := (bi % bx) * 4 + t % 4
    let y := if y0 < h then y0 else h - 1
    let x := if x0 < w then x0 else w - 1
    let base := (y * w + x) * 4
    [src.getD base 0, src.getD (base + 1) 0,
     src.getD (base + 2) 0, src.getD (base + 3) 0])

def bc7CompressImage (src : List Nat) (w h : Nat) : Option (List Nat) :=
  if w == 0 || h == 0 then none
  else if src.length < w * h * 4 then none
  else
    let bx := (w + 3) / 4
    some ((List.range (((w + 3) / 4) * ((h + 3) / 4))).foldr (fun bi acc =>
      bc7EncodeBlockDefault (bc7Gather src w h bx bi) ++ acc) [])

theorem bc7CompressImage_none_small (src : List Nat) (w h : Nat)
    (hsmall : src.length < w * h * 4) :
    bc7CompressImage src w h = none := by
  unfold bc7CompressImage
  by_cases hw : w == 0 || h == 0
  · simp [hw]
  · simp [hw, hsmall]

end Texcomp
