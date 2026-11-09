/-
  TinyEXR - Lean 4 formalization of the BC4 (single-channel) block decoder.

  BC4: 8 bytes per 4x4 block. Two 8-bit endpoints + 16 3-bit indices.
  8-color mode when e0 > e1, 6-color mode (with 0/255) otherwise.
  Matches tc_bc5_decompress (per-channel) logic.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- BC4 palette (8 entries) for a single channel. -/
def bc4Palette (e0 e1 : UInt8) : Fin 8 → UInt8 :=
  if e0.toNat > e1.toNat then
    fun i =>
      if i.val = 0 then e0
      else if i.val = 1 then e1
      else
        let e0n := e0.toNat
        let e1n := e1.toNat
        let idx := i.val - 2
        if idx = 0 then ((6 * e0n + 1 * e1n) / 7).toUInt8
        else if idx = 1 then ((5 * e0n + 2 * e1n) / 7).toUInt8
        else if idx = 2 then ((4 * e0n + 3 * e1n) / 7).toUInt8
        else if idx = 3 then ((3 * e0n + 4 * e1n) / 7).toUInt8
        else if idx = 4 then ((2 * e0n + 5 * e1n) / 7).toUInt8
        else ((1 * e0n + 6 * e1n) / 7).toUInt8
  else
    fun i =>
      if i.val = 0 then e0
      else if i.val = 1 then e1
      else if i.val = 6 then 0
      else if i.val = 7 then 255
      else
        let e0n := e0.toNat
        let e1n := e1.toNat
        let idx := i.val - 2
        if idx = 0 then ((4 * e0n + 1 * e1n) / 5).toUInt8
        else if idx = 1 then ((3 * e0n + 2 * e1n) / 5).toUInt8
        else if idx = 2 then ((2 * e0n + 3 * e1n) / 5).toUInt8
        else ((1 * e0n + 4 * e1n) / 5).toUInt8

/-- Extract a 3-bit index from 6 index bytes at a given texel. -/
def bc4Index (idxBytes : Fin 6 → UInt8) (texel : Fin 16) : Fin 8 :=
  let bitPos := texel.val * 3
  let byteIdx := bitPos / 8
  let shift := bitPos % 8
  let lo := idxBytes ⟨byteIdx, by { have := texel.isLt; omega }⟩
  let hi := if h : byteIdx + 1 < 6 then idxBytes ⟨byteIdx + 1, by { have := h; omega }⟩ else 0
  let combined := lo.toNat ||| (hi.toNat <<< 8)
  ⟨(combined >>> shift) % 8, by omega⟩

/-- Decode a single BC4 channel texel. -/
def bc4DecodeTexel (e0 e1 : UInt8) (idxBytes : Fin 6 → UInt8) (texel : Fin 16) : UInt8 :=
  bc4Palette e0 e1 (bc4Index idxBytes texel)

/-- BC4 block is 8 bytes. -/
def bc4BlockSize : Nat := 8

/-- BC5 block is 16 bytes (two BC4 blocks). -/
def bc5BlockSize2 : Nat := 16

end Texcomp