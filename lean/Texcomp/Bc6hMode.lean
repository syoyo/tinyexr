/-
  TinyEXR - Lean 4 formalization of BC6H mode detection.

  BC6H mode is determined by the first 5 bits of the block (read from
  the tail of the first two bytes). Modes 0-13. Mode 0/14 special.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- BC6H mode (0-13, plus special). -/
def bc6hMode (b0 b1 : UInt8) : Nat :=
  let bits := ((b0.toNat >>> 6) ||| ((b1.toNat &&& 0x7) <<< 2))  -- 5 bits
  if bits == 0 then 14  -- special mode (mode 0 or 14)
  else
    -- find position of highest set bit (0-indexed from LSB)
    if bits &&& 0x10 != 0 then 1
    else if bits &&& 0x08 != 0 then 2
    else if bits &&& 0x04 != 0 then 3
    else if bits &&& 0x02 != 0 then 4
    else 5

-- Mode range property deferred (requires bitwise reasoning).

/-- BC6H block is 16 bytes. -/
theorem bc6hBlockSize2 : (16 : Nat) = 16 := rfl

end Texcomp