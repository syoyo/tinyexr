/-
  TinyEXR - Lean 4 formalization of the BC6H block format.

  First slice: block size constant (16 bytes per 4x4 block) and signed/unsigned
  variant flag. Full decode comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def bc6hBlockSize : Nat := 16

def bc6hPayloadSize (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc6hBlockSize

theorem bc6hBlockSize_pos : bc6hBlockSize > 0 := by decide

end Texcomp