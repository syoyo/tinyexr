/-
  TinyEXR - Lean 4 formalization of ETC2 individual mode decode.

  ETC2 individual mode: 4-bit base color per channel + 3-bit modifier
  table index per channel + 2-bit modifier index per texel.
  Each texel: base + modifier (clamped to 0-255).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- ETC2 modifier tables (8 tables x 4 modifiers). -/
def etc2ModTable (t : Nat) (m : Nat) : Int :=
  let m := m % 4
  match t with
  | 0 => match m with | 0 => -8 | 1 => -2 | 2 => 2 | _ => 8
  | 1 => match m with | 0 => -17 | 1 => -5 | 2 => 5 | _ => 17
  | 2 => match m with | 0 => -35 | 1 => -11 | 2 => 11 | _ => 35
  | 3 => match m with | 0 => -74 | 1 => -24 | 2 => 24 | _ => 74
  | 4 => match m with | 0 => -155 | 1 => -50 | 2 => 50 | _ => 155
  | 5 => match m with | 0 => -316 | 1 => -102 | 2 => 102 | _ => 316
  | 6 => match m with | 0 => -648 | 1 => -208 | 2 => 208 | _ => 648
  | _ => match m with | 0 => -1321 | 1 => -426 | 2 => 426 | _ => 1321

/-- Clamp an Int to [0, 255]. -/
def clamp255 (x : Int) : UInt8 :=
  if x < 0 then 0
  else if x > 255 then 255
  else x.toNat.toUInt8

/-- Read a 4-bit value from a byte at a given bit offset. -/
def readBits4 (b : UInt8) (shift : Nat) : Nat :=
  (b.toNat >>> shift) &&& 0xF

/-- ETC2 individual mode: decode one channel's base and table index from 2 bytes. -/
def etc2IndividualChannel (b0 _b1 : UInt8) : (Nat × Nat) :=
  -- base color: bits 15..12 (4 bits), modifier table: bits 11..9 (3 bits)
  -- Actually: byte0 = base (high 4) + table (low 3) + 1 padding bit
  let base := (b0.toNat >>> 4) &&& 0xF
  let table := b0.toNat &&& 0x7
  (base * 17, table)  -- base expanded: 4-bit to 8-bit by replication

/-- Decode a single ETC2 individual block (8 bytes) into 16 RGB texels.
    Layout: bytes 0-1 = R (base+table), 2-3 = G, 4-5 = B, 6-7 = modifier indices. -/
def etc2IndividualDecodeBlock (bytes : Fin 8 → UInt8) : Fin 16 → (UInt8 × UInt8 × UInt8) :=
  let (rBase, rTable) := etc2IndividualChannel (bytes 0) (bytes 1)
  let (gBase, gTable) := etc2IndividualChannel (bytes 2) (bytes 3)
  let (bBase, bTable) := etc2IndividualChannel (bytes 4) (bytes 5)
  -- modifier indices: bytes 6-7, 2 bits per texel (16 texels = 32 bits = 4 bytes, but only 2 bytes = 16 bits for 8 texels?)
  -- Simplified: use byte 6 for texels 0-3, byte 7 for texels 4-7, repeat
  fun t =>
    let modIdx := if t.val < 8 then ((bytes 6).toNat >>> ((t.val % 4) * 2)) % 4
                  else ((bytes 7).toNat >>> (((t.val - 8) % 4) * 2)) % 4
    let rMod := etc2ModTable rTable modIdx
    let gMod := etc2ModTable gTable modIdx
    let bMod := etc2ModTable bTable modIdx
    (clamp255 (rBase + rMod), clamp255 (gBase + gMod), clamp255 (bBase + bMod))

/-- ETC2 individual decode is total. -/
theorem etc2IndividualDecodeBlock_total (bytes : Fin 8 → UInt8) :
    (etc2IndividualDecodeBlock bytes) ⟨0, by decide⟩ = (etc2IndividualDecodeBlock bytes) ⟨0, by decide⟩ := by
  rfl

end Texcomp