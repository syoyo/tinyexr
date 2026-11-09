/-
  TinyEXR - Lean 4 formalization of the BC5 block format.

  First slice: block size constant (16 bytes per 4x4 block) and snorm flag.
  Full decode comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def bc5BlockSize : Nat := 16

def bc5PayloadSize (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc5BlockSize

theorem bc5BlockSize_pos : bc5BlockSize > 0 := by decide

end Texcomp