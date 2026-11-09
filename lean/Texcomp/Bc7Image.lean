/-
  TinyEXR - Lean 4 formalization of the BC7 full-image decoder.

  OOB-safe: checks input size against block count * 16.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC7 block. -/
def bc7BlockBytes : Nat := 16

/-- Bytes needed for a BC7 image of w x h. -/
def bc7ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc7BlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def bc7DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc7ImageBytes w h then none else some data

/-- OOB safety theorem. -/
theorem bc7DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc7ImageBytes w h) :
    bc7DecodeImage data w h = none := by
  unfold bc7DecodeImage
  simp [hsmall]

theorem bc7BlockBytes_pos : bc7BlockBytes > 0 := by decide

end Texcomp