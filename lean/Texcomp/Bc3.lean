/-
  TinyEXR - Lean 4 formalization of the BC3 (DXT5) block format.

  First slice: block size constant (16 bytes per 4x4 block: 8-byte alpha
  + 8-byte color). Full decode comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def bc3BlockSize : Nat := 16

def bc3PayloadSize (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc3BlockSize

theorem bc3BlockSize_pos : bc3BlockSize > 0 := by decide

end Texcomp