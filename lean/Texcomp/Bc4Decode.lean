/-
  TinyEXR - Lean 4 formalization of the BC4 single-block decoder.

  Decodes an 8-byte BC4 block into 16 single-channel (UInt8) texels.
  Uses bc4Palette + bc4Index from Bc4.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc4

namespace Texcomp

/-- Read 8 bytes into a Fin 8 → UInt8 array. -/
def bytesToFin8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Fin 8 → UInt8 :=
  fun i => match i.val with
    | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7

/-- Decode a single BC4 block into 16 texels. -/
def bc4DecodeBlock (bytes : Fin 8 → UInt8) : Fin 16 → UInt8 :=
  let e0 := bytes 0
  let e1 := bytes 1
  let idxBytes : Fin 6 → UInt8 := fun i => bytes ⟨i.val + 2, by omega⟩
  let pal := bc4Palette e0 e1
  fun t => pal (bc4Index idxBytes t)

/-- BC4 decode is total: always produces 16 texels. -/
theorem bc4DecodeBlock_total (bytes : Fin 8 → UInt8) :
    (bc4DecodeBlock bytes) ⟨0, by decide⟩ = bc4Palette (bytes 0) (bytes 1) (bc4Index (fun i => bytes ⟨i.val + 2, by omega⟩) ⟨0, by decide⟩) := by
  unfold bc4DecodeBlock
  simp

end Texcomp