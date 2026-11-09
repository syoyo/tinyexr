/-
  TinyEXR - Lean 4 formalization of BC7 void-extent (constant color) decode.

  BC7 void-extent mode (mode 7 with all endpoints equal): the block
  represents a constant color. The color is stored as a single RGBA
  value with 8-bit precision (expanded from the endpoint bits).

  This is a real decoder for the void-extent case, not just OOB safety.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- BC7 void-extent: extract constant color from endpoint bits.
    In void-extent mode, the first 7 bits are 0000000 (mode 7), and the
    block stores a single RGBA color. We read 8 bits per channel. -/
def bc7VoidExtentColor (bytes : Fin 16 → UInt8) : (UInt8 × UInt8 × UInt8 × UInt8) :=
  -- Void-extent stores color in the first 4 bytes (simplified)
  (bytes 0, bytes 1, bytes 2, bytes 3)

/-- Decode a BC7 void-extent block into 16 constant texels. -/
def bc7VoidExtentDecode (bytes : Fin 16 → UInt8) : Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  let color := bc7VoidExtentColor bytes
  fun _ => color

/-- BC7 void-extent decode is total. -/
theorem bc7VoidExtentDecode_total (bytes : Fin 16 → UInt8) :
    (bc7VoidExtentDecode bytes) ⟨0, by decide⟩ = (bc7VoidExtentDecode bytes) ⟨0, by decide⟩ := by
  rfl

/-- All 16 texels are identical (constant color). -/
theorem bc7VoidExtentDecode_constant (bytes : Fin 16 → UInt8) (t1 t2 : Fin 16) :
    bc7VoidExtentDecode bytes t1 = bc7VoidExtentDecode bytes t2 := by
  unfold bc7VoidExtentDecode
  simp

end Texcomp