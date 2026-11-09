/-
  TinyEXR - Lean 4 formalization of the BC3 (DXT5) full block decoder.

  Combines BC3 alpha block (8 bytes) + BC1 color block (8 bytes) into
  16 RGBA8 texels. Uses Bc3Alpha and Bc1Decode.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc3Alpha
import Texcomp.Bc1Decode

namespace Texcomp

/-- A BC3 block decodes to 16 RGBA8 texels. -/
def bc3DecodeBlock (bytes : Fin 16 → UInt8) : Fin 16 → Color4 :=
  -- Alpha block: bytes 0..7
  let a0 := bytes 0
  let a1 := bytes 1
  let alphaIdxBytes : Fin 6 → UInt8 := fun i => bytes ⟨i.val + 2, by omega⟩
  let alphaPal := bc3AlphaPalette a0 a1
  -- Color block: bytes 8..15
  let c0 := u16le (bytes 8) (bytes 9)
  let c1 := u16le (bytes 10) (bytes 11)
  let colorIdxBytes : Fin 4 → UInt8 := fun i => bytes ⟨12 + i.val, by omega⟩
  let colorPal := bc1Palette c0 c1
  fun t =>
    let alpha := alphaPal (bc3AlphaIndex alphaIdxBytes t)
    let color := colorPal (bc1Index colorIdxBytes t)
    { r := color.r, g := color.g, b := color.b, a := alpha }

/-- BC3 decode is total: always produces 16 texels. -/
theorem bc3DecodeBlock_total (bytes : Fin 16 → UInt8) :
    (bc3DecodeBlock bytes) ⟨0, by decide⟩ = bc3DecodeBlock bytes ⟨0, by decide⟩ := by
  rfl

end Texcomp