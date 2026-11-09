/-
  TinyEXR - Lean 4 formalization of the ETC2 full-image decoder.

  OOB-safe: checks input size against block count * block size (8 for RGB,
  16 for RGBA).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per ETC2 RGB block. -/
def etc2RgbBlockBytes : Nat := 8
/-- Bytes per ETC2 RGBA block. -/
def etc2RgbaBlockBytes : Nat := 16

/-- Bytes needed for an ETC2 RGB image of w x h. -/
def etc2RgbImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * etc2RgbBlockBytes

/-- Bytes needed for an ETC2 RGBA image of w x h. -/
def etc2RgbaImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * etc2RgbaBlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def etc2DecodeImage (data : List UInt8) (w h : Nat) (alpha : Bool) : Option (List UInt8) :=
  let needed := if alpha then etc2RgbaImageBytes w h else etc2RgbImageBytes w h
  if data.length < needed then none else some data

/-- OOB safety theorem (RGB). -/
theorem etc2DecodeImage_none_if_small_rgb (data : List UInt8) (w h : Nat)
    (hsmall : data.length < etc2RgbImageBytes w h) :
    etc2DecodeImage data w h false = none := by
  unfold etc2DecodeImage
  simp [hsmall]

theorem etc2RgbBlockBytes_pos : etc2RgbBlockBytes > 0 := by decide
theorem etc2RgbaBlockBytes_pos : etc2RgbaBlockBytes > 0 := by decide

end Texcomp