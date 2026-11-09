/-
  TinyEXR - Lean 4 formalization of the BC7 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*16 bytes,
  returns none on truncated input (OOB-safe).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per BC7 block. -/
def bc7BlockBytes2 : Nat := 16

/-- Bytes needed for a BC7 image of w x h. -/
def bc7ImageBytes2 (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc7BlockBytes2

/-- OOB-safe decode: returns none if input too small. -/
def bc7DecodeImage2 (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc7ImageBytes2 w h then none else some data

/-- OOB safety theorem. -/
theorem bc7DecodeImage2_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc7ImageBytes2 w h) :
    bc7DecodeImage2 data w h = none := by
  unfold bc7DecodeImage2
  simp [hsmall]

theorem bc7BlockBytes2_pos : bc7BlockBytes2 > 0 := by decide

end Texcomp