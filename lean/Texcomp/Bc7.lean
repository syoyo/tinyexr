/-
  TinyEXR - Lean 4 formalization of the BC7 block format.

  First slice: block size constant (16 bytes per 4x4 block). Full decode
  (8 modes) comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def bc7BlockSize : Nat := 16

def bc7PayloadSize (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc7BlockSize

theorem bc7BlockSize_pos : bc7BlockSize > 0 := by decide

end Texcomp