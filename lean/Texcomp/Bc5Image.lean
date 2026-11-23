/-
  TinyEXR - Lean 4 formalization of the BC5 full-image decoder.

  Mirrors `tc_bc5_decompress_rgba8` (unorm8 path): two BC4 blocks per 4x4
  tile, row-major output, B=0 and A=255. Bit-exact against C via
  `make texcomp-bc5-img-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc5Decode

namespace Texcomp

/-- Bytes per BC5 block. -/
def bc5BlockBytes : Nat := 16

/-- Bytes needed for a BC5 image of w x h. -/
def bc5ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc5BlockBytes

def bc5Byte (data : List UInt8) (i : Nat) : UInt8 := data.getD i 0

def bc5ImageBlock (data : List UInt8) (bi : Nat) : Fin 16 → UInt8 :=
  fun i => bc5Byte data (bi * 16 + i.val)

/-- One output step for BC5 image decoding. -/
def bc5OutStep (data : List UInt8) (w bx : Nat) (k : Nat)
    (acc : List UInt8) : List UInt8 :=
  let x := k % w
  let y := k / w
  let bi := (y / 4) * bx + x / 4
  let t := (y % 4) * 4 + x % 4
  let px := bc5DecodeBlock (bc5ImageBlock data bi) ⟨t, by omega⟩
  [px.r, px.g, 0, 255] ++ acc

theorem bc5OutStep_length (data : List UInt8) (w bx k : Nat) (acc : List UInt8) :
    (bc5OutStep data w bx k acc).length = acc.length + 4 := by
  simp [bc5OutStep]

/-- `foldr` over `n` outputs emits `4n` bytes. -/
theorem bc5Fold_length (data : List UInt8) (w bx : Nat) :
    ∀ (l : List Nat) (acc : List UInt8),
      (l.foldr (bc5OutStep data w bx) acc).length = acc.length + l.length * 4
  | [], acc => by simp
  | k :: ks, acc => by
      simp [bc5Fold_length data w bx ks, bc5OutStep_length]
      omega

/-- Decode a BC5 image into RGBA8 (`b = 0`, `a = 255`). -/
def bc5DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc5ImageBytes w h then none
  else
    let bx := (w + 3) / 4
    if w == 0 || h == 0 then some []
    else
      some ((List.range (w * h)).foldr (bc5OutStep data w bx) [])

theorem bc5DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc5ImageBytes w h) :
    bc5DecodeImage data w h = none := by
  unfold bc5DecodeImage
  simp [hsmall]

/-- A successful decode returns exactly `w * h * 4` bytes. -/
theorem bc5DecodeImage_length {data : List UInt8} {w h : Nat} {out : List UInt8}
    (hok : bc5DecodeImage data w h = some out) : out.length = w * h * 4 := by
  unfold bc5DecodeImage at hok
  by_cases hs : data.length < bc5ImageBytes w h
  · simp [hs] at hok
  · simp [hs] at hok
    by_cases hw : w = 0 ∨ h = 0
    · simp [hw] at hok
      rw [hok]
      cases hw with
      | inl hw0 => simp [hw0]
      | inr hh0 => simp [hh0]
    · simp [hw] at hok
      rw [← hok]
      rw [bc5Fold_length]
      simp

theorem bc5BlockBytes_pos : bc5BlockBytes > 0 := by decide

end Texcomp
