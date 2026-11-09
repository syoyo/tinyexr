/-
  TinyEXR - Lean 4 formalization of the ETC2 block format.

  First slice: block size constants (8 bytes RGB, 16 bytes RGBA with EAC alpha)
  and the alpha flag. Full decode comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def etc2RgbBlockSize : Nat := 8
def etc2RgbaBlockSize : Nat := 16
def eacR11BlockSize : Nat := 8

def etc2PayloadSize (w h : Nat) (alpha : Bool) : Nat :=
  let blocks := ((w + 3) / 4) * ((h + 3) / 4)
  blocks * (if alpha then etc2RgbaBlockSize else etc2RgbBlockSize)

theorem etc2RgbBlockSize_pos : etc2RgbBlockSize > 0 := by decide
theorem etc2RgbaBlockSize_pos : etc2RgbaBlockSize > 0 := by decide

end Texcomp