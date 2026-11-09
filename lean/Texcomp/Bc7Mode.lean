/-
  TinyEXR - Lean 4 formalization of BC7 mode detection.

  BC7 mode is determined by reading bits from the start of the block
  until a 1 is found (modes 0-6), or all 7 bits are 0 (mode 7).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- BC7 mode from the first byte. -/
def bc7Mode (b0 : UInt8) : Nat :=
  if b0 &&& 0x80 != 0 then 0
  else if b0 &&& 0x40 != 0 then 1
  else if b0 &&& 0x20 != 0 then 2
  else if b0 &&& 0x10 != 0 then 3
  else if b0 &&& 0x08 != 0 then 4
  else if b0 &&& 0x04 != 0 then 5
  else if b0 &&& 0x02 != 0 then 6
  else 7

/-- Mode is in valid range 0..7. -/
theorem bc7Mode_range (b0 : UInt8) : bc7Mode b0 ≤ 7 := by
  unfold bc7Mode
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

end Texcomp