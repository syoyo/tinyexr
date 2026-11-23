/-
  TinyEXR - Lean 4 formalization of the ASTC full-image decoder.

  Wraps the already byte-exact `astcDecodeImageRgba8` block-grid decoder
  (covered by `make texcomp-astc-ldrdec-diff`) with the raw byte-stream
  framing used by the public `tc_astc_decompress_rgba8` API.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcLdrImgDec

namespace Texcomp

/-- Bytes per ASTC block. -/
def astcBlockBytes : Nat := 16

/-- Bytes needed for an ASTC image of w x h with block footprint bx x by. -/
def astcImageBytes (bx by_ w h : Nat) : Nat :=
  ((w + bx - 1) / bx) * ((h + by_ - 1) / by_) * astcBlockBytes

/-- Split a raw block stream into the `List (List Nat)` representation used
  by the block-grid decoder. -/
def astcToBlocks (data : List UInt8) (nb : Nat) : List (List Nat) :=
  (List.range nb).map (fun bi =>
    (List.range 16).map (fun i => (data.getD (bi * 16 + i) 0).toNat))

/-- Decode a raw ASTC LDR image into row-major RGBA8 bytes. -/
def astcDecodeImage (data : List UInt8) (bx by_ w h : Nat) : Option (List UInt8) :=
  if bx == 0 || by_ == 0 then none
  else if data.length < astcImageBytes bx by_ w h then none
  else
    let bw := (w + bx - 1) / bx
    let bh := (h + by_ - 1) / by_
    match astcDecodeImageRgba8 (astcToBlocks data (bw * bh)) w h bx by_ with
    | none => none
    | some px =>
        some (px.foldr (fun p acc =>
          (p.getD 0 0).toUInt8 :: (p.getD 1 0).toUInt8 ::
          (p.getD 2 0).toUInt8 :: (p.getD 3 0).toUInt8 :: acc) [])

/-- OOB safety theorem. -/
theorem astcDecodeImage_none_if_small (data : List UInt8) (bx by_ w h : Nat)
    (hsmall : data.length < astcImageBytes bx by_ w h) :
    astcDecodeImage data bx by_ w h = none := by
  unfold astcDecodeImage
  simp [hsmall]

theorem astcBlockBytes_pos : astcBlockBytes > 0 := by decide

end Texcomp
