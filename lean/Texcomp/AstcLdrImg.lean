/-
  TinyEXR - ASTC LDR image-level compress driver (Lean model).

  Models `tc_astc_compress_rgba8` from `tools/texcomp/src/texcomp_astc.c`
  (the `tc_astc_compress_band` inner loop): gather each block dims × block
  size tile of the RGBA8 image with edge clamping (`y >= height` →
  `height - 1`, `x >= width` → `width - 1`, mirroring the C `if (y >= height)
  y = height - 1u;` clamps), then dispatch:

    uastc != 0          → `tc_encode_uastc_ldr_block` (solid handled inside)
    !block_is_solid     → `tc_encode_astc_ldr_block` (quality from context,
                           context is inited with `opt->quality`)
    otherwise           → `tc_encode_astc_const_block`

  The threads field only partitions block rows across workers; output is
  byte-identical for any thread count, so the model is the serial path with
  `threads = 1`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcUastc
import Texcomp.AstcLdr

namespace Texcomp

/-- Edge-clamped gather of one `bdx × bdy` RGBA8 block at texel origin
  `(bx, by0)` from a row-major `width × height` image (each texel a 4-tuple
  of 0..255 bytes). Returns the block texels in C gather order (yy outer,
  xx inner) plus the first gathered texel (unused by the driver, kept for
  parity with `hdrGatherBlock`). -/
def astcGatherBlockU8 (pix : List (List Nat)) (width height bx by0 bdx bdy : Nat) :
    List (List Nat) × List Nat :=
  let cells := (List.range (bdy * bdx)).map (fun idx =>
    let yy := idx / bdx
    let xx := idx % bdx
    let y := min (by0 + yy) (height - 1)
    let x := min (bx + xx) (width - 1)
    pix.getD (y * width + x) [])
  (cells, cells.getD 0 [])

/-- `tc_astc_compress_rgba8`: RGBA8 image → ASTC block stream (block dims
  `bdx × bdy`, quality / uastc from the options). Row-major block fold,
  block bytes concatenated in scan order. -/
def astcCompressRgba8 (pix : List (List Nat)) (width height bdx bdy quality uastc : Nat) :
    List Nat :=
  let nBlocksX := (width + bdx - 1) / bdx
  let nBlocksY := (height + bdy - 1) / bdy
  (List.range (nBlocksY * nBlocksX)).foldl (fun (acc : List Nat) bi =>
    let byB := (bi / nBlocksX) * bdy
    let bx := (bi % nBlocksX) * bdx
    let (block, _) := astcGatherBlockU8 pix width height bx byB bdx bdy
    let count := bdx * bdy
    let bytes : List Nat :=
      if uastc != 0 then astcEncodeUastcLdrBlock block count quality bdx bdy
      else if !(astcBlockIsSolid block count) then
        astcEncodeLdrBlock block count quality bdx bdy
      else astcEncodeConstBlock block count
    acc ++ bytes) []

end Texcomp
