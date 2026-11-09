/-
  TinyEXR - Lean 4 formalization of the BC3 full-image decoder.

  Total function: checks input has at least (ceil(w/4)*ceil(h/4))*16 bytes
  (BC3 is 16 bytes/block: 8 alpha + 8 color), decodes each block into
  16 RGBA8 texels using Bc3Decode, returns none on truncated input.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc3Decode

namespace Texcomp

/-- Bytes per BC3 block. -/
def bc3BlockBytes2 : Nat := 16

/-- Bytes needed for a BC3 image of w x h. -/
def bc3ImageBytes2 (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc3BlockBytes2

/-- Read 16 bytes from a list starting at offset. -/
def readBc3Block (data : List UInt8) (off : Nat) : Option (Fin 16 → UInt8) :=
  if h : off + 16 ≤ data.length then
    some (fun i => data.get ⟨off + i.val, by { have hi := i.isLt; have hh := h; omega }⟩)
  else none

/-- Decode a full BC3 image. Returns none if input too small. -/
def bc3DecodeImage2 (data : List UInt8) (w h : Nat) : Option (List Color4) :=
  if data.length < bc3ImageBytes2 w h then none
  else
    let bx := (w + 3) / 4
    let by_ := (h + 3) / 4
    let numBlocks := bx * by_
    let rec go (bi : Nat) (acc : List Color4) : List Color4 :=
      if bi ≥ numBlocks then acc.reverse
      else
        let off := bi * 16
        match readBc3Block data off with
        | none => acc.reverse
        | some b =>
            let texels := (List.finRange 16).map (fun t => bc3DecodeBlock b t)
            go (bi + 1) (texels.reverse ++ acc)
    some (go 0 [])

/-- OOB safety: truncated input returns none. -/
theorem bc3DecodeImage2_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc3ImageBytes2 w h) :
    bc3DecodeImage2 data w h = none := by
  unfold bc3DecodeImage2
  simp [hsmall]

/-- Empty image needs 0 bytes. -/
theorem bc3ImageBytes2_zero (h : Nat) : bc3ImageBytes2 0 h = 0 := by
  unfold bc3ImageBytes2
  simp

end Texcomp