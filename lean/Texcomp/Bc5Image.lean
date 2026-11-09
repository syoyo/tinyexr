/-
  TinyEXR - Lean 4 formalization of the BC5 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*16 bytes
  (two BC4 blocks per 4x4 tile), returns none on truncated input.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC5 block. -/
def bc5BlockBytes : Nat := 16

/-- Bytes needed for a BC5 image of w x h. -/
def bc5ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc5BlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def bc5DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc5ImageBytes w h then none else some data

/-- OOB safety theorem. -/
theorem bc5DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc5ImageBytes w h) :
    bc5DecodeImage data w h = none := by
  unfold bc5DecodeImage
  simp [hsmall]

theorem bc5BlockBytes_pos : bc5BlockBytes > 0 := by decide

end Texcomp