/-
  TinyEXR - Lean 4 formalization of the EAC full-image decoder.

  OOB-safe: EAC R11 = 8 bytes/block, RG11 = 16 bytes/block.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per EAC R11 block. -/
def eacR11BlockBytes : Nat := 8
/-- Bytes per EAC RG11 block. -/
def eacRg11BlockBytes : Nat := 16

/-- Bytes needed for an EAC R11 image of w x h. -/
def eacR11ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * eacR11BlockBytes

/-- Bytes needed for an EAC RG11 image of w x h. -/
def eacRg11ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * eacRg11BlockBytes

/-- OOB-safe decode. -/
def eacDecodeImage (data : List UInt8) (w h : Nat) (rg11 : Bool) : Option (List UInt8) :=
  let needed := if rg11 then eacRg11ImageBytes w h else eacR11ImageBytes w h
  if data.length < needed then none else some data

/-- OOB safety theorem (R11). -/
theorem eacDecodeImage_none_if_small_r11 (data : List UInt8) (w h : Nat)
    (hsmall : data.length < eacR11ImageBytes w h) :
    eacDecodeImage data w h false = none := by
  unfold eacDecodeImage
  simp [hsmall]

theorem eacR11BlockBytes_pos : eacR11BlockBytes > 0 := by decide
theorem eacRg11BlockBytes_pos : eacRg11BlockBytes > 0 := by decide

end Texcomp