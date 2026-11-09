/-
  TinyEXR - Lean 4 formalization of the BC1 block format.

  First slice: the 8-byte block layout (two RGB565 endpoints + 16 2-bit
  indices) and the punch-through (3-color) vs 4-color mode selection.
  Full decode and encode come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- An RGB565 color (5-6-5). -/
structure Rgb565 where
  r : Fin 32
  g : Fin 64
  b : Fin 32
  deriving Repr, DecidableEq

/-- A BC1 block: two endpoints and 16 2-bit indices (packed into 4 bytes). -/
structure Bc1Block where
  c0 : Rgb565
  c1 : Rgb565
  indices : Fin (2 ^ 32)  -- 16 x 2 bits packed
  deriving Repr

/-- BC1 uses 3-color mode (punch-through) when c0 <= c1 (as u16), else 4-color. -/
def Bc1Block.threeColor (blk : Bc1Block) : Bool :=
  -- compare packed u16 endpoints; placeholder: true when c0.r <= c1.r
  blk.c0.r.val ≤ blk.c1.r.val

/-- A BC1 block is always 8 bytes. -/
def bc1BlockSize : Nat := 8

theorem bc1BlockSize_pos : bc1BlockSize > 0 := by
  unfold bc1BlockSize
  decide

end Texcomp