/-
  TinyEXR - Lean 4 formalization of the BC1 full-image decoder.

  Total function: given a byte array and dimensions, checks that the input
  has at least (ceil(w/4)*ceil(h/4))*8 bytes, then decodes each 4x4 block
  into 16 texels. Returns none on truncated input (OOB-safe).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc1Decode

namespace Texcomp

/-- Number of bytes needed for a BC1 image of w x h. -/
def bc1ImageBytes (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * 8

/-- Read 8 bytes from a list starting at offset. -/
def readBlock (data : List UInt8) (off : Nat) : Option (Fin 8 → UInt8) :=
  if h : off + 8 ≤ data.length then
    some (fun i => data.get ⟨off + i.val, by { have hi := i.isLt; have hh := h; omega }⟩)
  else none

/-- Decode a full BC1 image. Returns none if input is too small. -/
def bc1DecodeImage (data : List UInt8) (w h : Nat) : Option (List Color4) :=
  if data.length < bc1ImageBytes w h then none
  else
    let bx := (w + 3) / 4
    let by_ := (h + 3) / 4
    let numBlocks := bx * by_
    -- Decode each block; collect all texels in row-major block order.
    let rec go (bi : Nat) (acc : List Color4) : List Color4 :=
      if bi ≥ numBlocks then acc.reverse
      else
        let off := bi * 8
        let blk := readBlock data off
        match blk with
        | none => acc.reverse
        | some b =>
            let texels := (List.finRange 16).map (fun t =>
              bc1DecodeBlock b t)
            go (bi + 1) (texels.reverse ++ acc)
    some (go 0 [])

/-- OOB safety: truncated input returns none. -/
theorem bc1DecodeImage_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc1ImageBytes w h) :
    bc1DecodeImage data w h = none := by
  unfold bc1DecodeImage
  simp [hsmall]

/-- Empty image (0 width) needs 0 bytes. -/
theorem bc1ImageBytes_zero (h : Nat) : bc1ImageBytes 0 h = 0 := by
  unfold bc1ImageBytes
  simp

end Texcomp