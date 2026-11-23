/-
  TinyEXR - Lean 4 formalization of the BC3 full-image decoder.

  Alias of `bc3DecodeImage2` (real per-block decode, 16 bytes per block:
  8 alpha + 8 colour). The old 24-byte placeholder was incorrect.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc3DecodeImage

namespace Texcomp

/-- Bytes per BC3 block (8 alpha + 8 colour). -/
def bc3BlockBytes : Nat := 16

/-- Bytes needed for a BC3 image of w x h. -/
def bc3ImageBytes (w h : Nat) : Nat := bc3ImageBytes2 w h

def bc3DecodeImage (data : List UInt8) (w h : Nat) : Option (List Color4) :=
  bc3DecodeImage2 data w h

theorem bc3DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc3ImageBytes w h) :
    bc3DecodeImage data w h = none := by
  unfold bc3DecodeImage
  apply bc3DecodeImage2_none_if_small
  simpa [bc3ImageBytes] using hsmall

theorem bc3BlockBytes_pos : bc3BlockBytes > 0 := by decide

end Texcomp
