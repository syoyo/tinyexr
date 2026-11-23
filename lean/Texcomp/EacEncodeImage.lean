/-
  TinyEXR - Lean 4 model of `tc_eac_compress_rgba8`.

  EAC numbers texels column-major (`index = x*4 + y`) and serialises each
  encoded 64-bit block little-endian, matching `tc_wr_u64` in C.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Etc2Encode

namespace Texcomp

def eacCompressedSize (w h : Nat) (rg11 : Bool) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * (if rg11 then 16 else 8)

/-- Column-major 4x4 gather for one channel. -/
def eacGather (src : List Nat) (w h : Nat) (bx bi chan : Nat) : List Nat :=
  (List.range 16).map (fun t =>
    let yy := t % 4
    let xx := t / 4
    let y0 := (bi / bx) * 4 + yy
    let x0 := (bi % bx) * 4 + xx
    let y := if y0 < h then y0 else h - 1
    let x := if x0 < w then x0 else w - 1
    src.getD ((y * w + x) * 4 + chan) 0)

def eacCompressImage (src : List Nat) (w h : Nat) (rg11 : Bool) : Option (List Nat) :=
  if w == 0 || h == 0 then none
  else if src.length < w * h * 4 then none
  else
    let bx := (w + 3) / 4
    some ((List.range (((w + 3) / 4) * ((h + 3) / 4))).foldr (fun bi acc =>
      let r := eacGather src w h bx bi 0
      let b0 := le64 (eacAlphaEncode r)
      let b1 := if rg11 then le64 (eacAlphaEncode (eacGather src w h bx bi 1)) else []
      b0 ++ b1 ++ acc) [])

theorem eacCompressImage_none_small (src : List Nat) (w h : Nat) (rg11 : Bool)
    (hsmall : src.length < w * h * 4) :
    eacCompressImage src w h rg11 = none := by
  unfold eacCompressImage
  by_cases hw : w == 0 || h == 0
  · simp [hw]
  · simp [hw, hsmall]

end Texcomp
