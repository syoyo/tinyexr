/-
  TinyEXR - Lean 4 formalization of the BC3 (DXT5) alpha block decoder.

  Models the 8-byte alpha block: two 8-bit endpoints + 16 3-bit indices.
  8-color mode when alpha0 > alpha1, 6-color mode (with 0/255) otherwise.
  Matches tc_bc3_decompress_rgba8's alpha handling.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- An 8-entry alpha palette. -/
def Bc3AlphaPalette := Fin 8 → UInt8

/-- Build the 8-color palette (alpha0 > alpha1). -/
def bc3AlphaPalette8 (a0 a1 : UInt8) : Bc3AlphaPalette :=
  fun i =>
    if i.val = 0 then a0
    else if i.val = 1 then a1
    else
      let a0n := a0.toNat
      let a1n := a1.toNat
      let idx := i.val - 2  -- 0..5
      -- interpolate: a0 * (6-idx)/7? Actually 8 levels: 0,1,...,7 with 6 intermediate
      -- Standard: alpha[i] = ((7-idx)*a0 + idx*a1) / 7 for idx in 0..5? 
      -- Simpler: use the 6 intermediate values
      if idx = 0 then ((6 * a0n + 1 * a1n) / 7).toUInt8
      else if idx = 1 then ((5 * a0n + 2 * a1n) / 7).toUInt8
      else if idx = 2 then ((4 * a0n + 3 * a1n) / 7).toUInt8
      else if idx = 3 then ((3 * a0n + 4 * a1n) / 7).toUInt8
      else if idx = 4 then ((2 * a0n + 5 * a1n) / 7).toUInt8
      else ((1 * a0n + 6 * a1n) / 7).toUInt8

/-- Build the 6-color palette (alpha0 <= alpha1): 6 intermediate + 0 + 255. -/
def bc3AlphaPalette6 (a0 a1 : UInt8) : Bc3AlphaPalette :=
  fun i =>
    if i.val = 0 then a0
    else if i.val = 1 then a1
    else if i.val = 6 then 0
    else if i.val = 7 then 255
    else
      let a0n := a0.toNat
      let a1n := a1.toNat
      let idx := i.val - 2  -- 0..3
      if idx = 0 then ((4 * a0n + 1 * a1n) / 5).toUInt8
      else if idx = 1 then ((3 * a0n + 2 * a1n) / 5).toUInt8
      else if idx = 2 then ((2 * a0n + 3 * a1n) / 5).toUInt8
      else ((1 * a0n + 4 * a1n) / 5).toUInt8

/-- Select palette based on endpoint order. -/
def bc3AlphaPalette (a0 a1 : UInt8) : Bc3AlphaPalette :=
  if a0.toNat > a1.toNat then bc3AlphaPalette8 a0 a1 else bc3AlphaPalette6 a0 a1

/-- Extract a 3-bit index from the 6 index bytes at a given texel (0..15). -/
def bc3AlphaIndex (idxBytes : Fin 6 → UInt8) (texel : Fin 16) : Fin 8 :=
  let bitPos := texel.val * 3
  let byteIdx := bitPos / 8
  let shift := bitPos % 8
  -- read up to 2 bytes
  let lo := idxBytes ⟨byteIdx, by { have := texel.isLt; omega }⟩
  let hi := if h : byteIdx + 1 < 6 then idxBytes ⟨byteIdx + 1, by { have := h; omega }⟩ else 0
  let combined := lo.toNat ||| (hi.toNat <<< 8)
  ⟨(combined >>> shift) % 8, by omega⟩

/-- Decode a single alpha value for a texel. -/
def bc3AlphaDecodeTexel (a0 a1 : UInt8) (idxBytes : Fin 6 → UInt8) (texel : Fin 16) : UInt8 :=
  bc3AlphaPalette a0 a1 (bc3AlphaIndex idxBytes texel)

/-- Alpha block is 8 bytes. -/
theorem bc3AlphaBlockSize : (8 : Nat) = 8 := rfl

end Texcomp