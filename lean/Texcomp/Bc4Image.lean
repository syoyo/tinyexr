/-
  TinyEXR - Lean 4 formalization of the BC4 full-image decoder.

  Unlike the original length-check placeholder, this decodes every output
  texel through the per-block `bc4DecodeBlock` model. Partial blocks are
  handled by the row-major output index (no padding texels are returned).
  Bit-exact against C via `make texcomp-bc4-img-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc4Decode

namespace Texcomp

/-- Bytes per BC4 block. -/
def bc4BlockBytes : Nat := 8

/-- Bytes needed for a BC4 image of w x h. -/
def bc4ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc4BlockBytes

/-- Total byte read (zero beyond the buffer; the image decoder checks the
  buffer length before using this). -/
def bc4Byte (data : List UInt8) (i : Nat) : UInt8 := data.getD i 0

/-- Read block `bi` (row-major block order). -/
def bc4ImageBlock (data : List UInt8) (bi : Nat) : Fin 8 → UInt8 :=
  fun i => bc4Byte data (bi * 8 + i.val)

/-- Decode a full BC4 image into `w * h` single-channel texels. -/
def bc4DecodeImage (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc4ImageBytes w h then none
  else
    let bx := (w + 3) / 4
    if w == 0 || h == 0 then some []
    else
      some ((List.range (w * h)).map (fun k =>
        let x := k % w
        let y := k / w
        let bi := (y / 4) * bx + x / 4
        let t := (y % 4) * 4 + x % 4
        (bc4DecodeBlock (bc4ImageBlock data bi)) ⟨t, by omega⟩))

/-- OOB safety theorem. -/
theorem bc4DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc4ImageBytes w h) :
    bc4DecodeImage data w h = none := by
  unfold bc4DecodeImage
  simp [hsmall]

/-- A successful decode returns exactly `w * h` texels. -/
theorem bc4DecodeImage_length {data : List UInt8} {w h : Nat} {out : List UInt8}
    (hok : bc4DecodeImage data w h = some out) : out.length = w * h := by
  unfold bc4DecodeImage at hok
  by_cases hs : data.length < bc4ImageBytes w h
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
      simp

theorem bc4BlockBytes_pos : bc4BlockBytes > 0 := by decide

end Texcomp
