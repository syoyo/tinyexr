/-
  TinyEXR - Lean 4 formalization of the ASTC block format.

  First slice: block size constant (16 bytes per block) and the set of
  valid block footprints from tc_astc_valid_block.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def astcBlockSize : Nat := 16

/-- Valid ASTC block footprints (bx, by). -/
def astcValidBlock (bx by_ : Nat) : Bool :=
  (bx == 4 && by_ == 4) || (bx == 5 && by_ == 4) ||
  (bx == 5 && by_ == 5) || (bx == 6 && by_ == 5) ||
  (bx == 6 && by_ == 6) || (bx == 8 && by_ == 5) ||
  (bx == 8 && by_ == 6) || (bx == 8 && by_ == 8) ||
  (bx == 10 && by_ == 5) || (bx == 10 && by_ == 6) ||
  (bx == 10 && by_ == 8) || (bx == 10 && by_ == 10) ||
  (bx == 12 && by_ == 10) || (bx == 12 && by_ == 12)

def astcPayloadSize2 (bx by_ w h : Nat) : Nat :=
  ((w + bx - 1) / bx) * ((h + by_ - 1) / by_) * astcBlockSize

theorem astcBlockSize_pos : astcBlockSize > 0 := by decide
theorem astcValid_4x4 : astcValidBlock 4 4 = true := by decide

end Texcomp