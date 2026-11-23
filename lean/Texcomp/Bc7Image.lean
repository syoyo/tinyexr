/-
  TinyEXR - alias of the BC7 full-image decoder (see `Bc7DecodeImage.lean`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7DecodeImage

namespace Texcomp

/-- Bytes per BC7 block. -/
def bc7BlockBytes : Nat := 16

/-- Bytes needed for a BC7 image of w x h. -/
def bc7ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc7BlockBytes

def bc7DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  bc7DecodeImage2 data w h

theorem bc7DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc7ImageBytes w h) :
    bc7DecodeImage data w h = none := by
  unfold bc7DecodeImage
  have hs : data.length < bc7ImageBytes2 w h := by
    simpa [bc7ImageBytes, bc7ImageBytes2, bc7BlockBytes, bc7BlockBytes2] using hsmall
  exact bc7DecodeImage2_none_if_small data w h hs

theorem bc7BlockBytes_pos : bc7BlockBytes > 0 := by decide

end Texcomp
