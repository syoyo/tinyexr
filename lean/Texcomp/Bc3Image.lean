/-
  TinyEXR - Lean 4 formalization of the BC3 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*24 bytes
  (8 alpha + 16 color per block), returns none on truncated input.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC3 block (8 alpha + 16 color). -/
def bc3BlockBytes : Nat := 24

/-- Bytes needed for a BC3 image of w x h. -/
def bc3ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc3BlockBytes

/-- OOB safety: truncated input returns none (placeholder decode). -/
def bc3DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc3ImageBytes w h then none else some data

/-- OOB safety theorem. -/
theorem bc3DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc3ImageBytes w h) :
    bc3DecodeImage data w h = none := by
  unfold bc3DecodeImage
  simp [hsmall]

theorem bc3BlockBytes_pos : bc3BlockBytes > 0 := by decide

end Texcomp