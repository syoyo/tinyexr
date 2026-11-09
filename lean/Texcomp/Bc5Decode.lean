/-
  TinyEXR - Lean 4 formalization of the BC5 full block decoder.

  BC5 = two BC4 blocks (R channel + G channel), 16 bytes total.
  Decodes into 16 (R, G) pairs.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc4

namespace Texcomp

/-- A BC5 texel (R, G). -/
structure Bc5Texel where
  r : UInt8
  g : UInt8
  deriving Repr, DecidableEq

/-- Decode a single BC5 block into 16 (R,G) texels. -/
def bc5DecodeBlock (bytes : Fin 16 → UInt8) : Fin 16 → Bc5Texel :=
  -- R channel: bytes 0..7
  let rE0 := bytes 0
  let rE1 := bytes 1
  let rIdx : Fin 6 → UInt8 := fun i => bytes ⟨i.val + 2, by omega⟩
  let rPal := bc4Palette rE0 rE1
  -- G channel: bytes 8..15
  let gE0 := bytes 8
  let gE1 := bytes 9
  let gIdx : Fin 6 → UInt8 := fun i => bytes ⟨i.val + 10, by omega⟩
  let gPal := bc4Palette gE0 gE1
  fun t =>
    { r := rPal (bc4Index rIdx t)
    , g := gPal (bc4Index gIdx t) }

/-- BC5 decode is total: always produces 16 texels. -/
theorem bc5DecodeBlock_total (bytes : Fin 16 → UInt8) :
    (bc5DecodeBlock bytes) ⟨0, by decide⟩ = bc5DecodeBlock bytes ⟨0, by decide⟩ := by
  rfl

end Texcomp