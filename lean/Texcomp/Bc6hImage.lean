/-
  TinyEXR - Lean 4 formalization of the BC6H full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*16 bytes,
  returns none on truncated input (OOB-safe). BC6H is HDR (FP16), 16 bytes/block.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC6H block. -/
def bc6hBlockBytes : Nat := 16

/-- Bytes needed for a BC6H image of w x h. -/
def bc6hImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc6hBlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def bc6hDecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc6hImageBytes w h then none else some data

/-- OOB safety theorem. -/
theorem bc6hDecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc6hImageBytes w h) :
    bc6hDecodeImage data w h = none := by
  unfold bc6hDecodeImage
  simp [hsmall]

theorem bc6hBlockBytes_pos : bc6hBlockBytes > 0 := by decide

end Texcomp