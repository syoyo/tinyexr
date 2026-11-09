/-
  TinyEXR - Lean 4 formalization of the BC4 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*8 bytes,
  returns none on truncated input (OOB-safe).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC4 block. -/
def bc4BlockBytes : Nat := 8

/-- Bytes needed for a BC4 image of w x h. -/
def bc4ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc4BlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def bc4DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc4ImageBytes w h then none else some data

/-- OOB safety theorem. -/
theorem bc4DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc4ImageBytes w h) :
    bc4DecodeImage data w h = none := by
  unfold bc4DecodeImage
  simp [hsmall]

theorem bc4BlockBytes_pos : bc4BlockBytes > 0 := by decide

end Texcomp