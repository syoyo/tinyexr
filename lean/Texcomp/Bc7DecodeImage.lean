/-
  TinyEXR - Lean 4 formalization of the BC7 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*16 bytes,
  decodes each 4x4 tile through `bc7DecodeBlock` and returns row-major RGBA8.
  Bit-exact against C via `make texcomp-bc7-img-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7AllModes

namespace Texcomp

/-- Bytes per BC7 block. -/
def bc7BlockBytes2 : Nat := 16

/-- Bytes needed for a BC7 image of w x h. -/
def bc7ImageBytes2 (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc7BlockBytes2

def bc7Byte (data : List UInt8) (i : Nat) : UInt8 := data.getD i 0

def bc7ImageBlock (data : List UInt8) (bi : Nat) : Fin 16 → UInt8 :=
  fun i => bc7Byte data (bi * 16 + i.val)

def bc7Pixel (data : List UInt8) (bx k w : Nat) : List UInt8 :=
  let x := k % w
  let y := k / w
  let bi := (y / 4) * bx + x / 4
  let t := (y % 4) * 4 + x % 4
  let px := bc7DecodeBlock (bc7ImageBlock data bi) ⟨t, by omega⟩
  [px.1, px.2.1, px.2.2.1, px.2.2.2]

theorem bc7Pixel_length (data : List UInt8) (bx k w : Nat) :
    (bc7Pixel data bx k w).length = 4 := by
  simp [bc7Pixel]

/-- Decode a full BC7 image. Returns none if input too small. -/
def bc7DecodeImage2 (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc7ImageBytes2 w h then none
  else
    let bx := (w + 3) / 4
    if w == 0 || h == 0 then some []
    else
      some ((List.range (w * h)).foldr
        (fun k acc => bc7Pixel data bx k w ++ acc) [])

/-- OOB safety theorem. -/
theorem bc7DecodeImage2_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc7ImageBytes2 w h) :
    bc7DecodeImage2 data w h = none := by
  unfold bc7DecodeImage2
  simp [hsmall]

theorem bc7BlockBytes2_pos : bc7BlockBytes2 > 0 := by decide

end Texcomp
