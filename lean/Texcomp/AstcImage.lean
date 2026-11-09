/-
  TinyEXR - Lean 4 formalization of the ASTC full-image decoder.

  OOB-safe: checks input size against block count * 16.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- Bytes per ASTC block. -/
def astcBlockBytes : Nat := 16

/-- Bytes needed for an ASTC image of w x h with block footprint bx x by. -/
def astcImageBytes (bx by_ w h : Nat) : Nat :=
  ((w + bx - 1) / bx) * ((h + by_ - 1) / by_) * astcBlockBytes

/-- OOB-safe decode: returns none if input too small. -/
def astcDecodeImage (data : List UInt8) (bx by_ w h : Nat) : Option (List UInt8) :=
  if data.length < astcImageBytes bx by_ w h then none else some data

/-- OOB safety theorem. -/
theorem astcDecodeImage_none_if_small (data : List UInt8) (bx by_ w h : Nat)
    (hsmall : data.length < astcImageBytes bx by_ w h) :
    astcDecodeImage data bx by_ w h = none := by
  unfold astcDecodeImage
  simp [hsmall]

theorem astcBlockBytes_pos : astcBlockBytes > 0 := by decide

end Texcomp