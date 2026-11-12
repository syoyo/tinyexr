/-
  TinyEXR - texcomp "uni" BC1 / BC7 transcode (Lean model).

  Models `tc_uni_transcode_bc1` and `tc_uni_transcode_bc7`
  (`tools/texcomp/src/texcomp_uni.c`): decode the uni (UASTC 4x4) blocks to
  RGBA8, then run the target's whole-image encoder with default options:

    tc_bc1_compress_rgba8  -> `bc1CompressRgba8`  (edge-clamped row-major
                              gather, `tc_encode_bc1_color_block(dxt1 = 1)`)
    tc_bc7_compress_rgba8  -> `bc7CompressRgba8`  (same gather,
                              `tc_encode_bc7_all_modes_block` at the default
                              options: quick = 2, pca_endpoints = 0,
                              mode_mask = 0xff, rdo = 0)

    tc_etc2_compress_rgba8 -> `etc2CompressRgba8` (Etc2Encode.lean; column-major
                              gather, optional EAC alpha block before each RGB block)

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Uni
import Texcomp.Bc1Encode
import Texcomp.Bc7EncodeAll
import Texcomp.Etc2Encode

namespace Texcomp

/-- Run a per-block encoder over the 4x4 tiling of a `w × h` RGBA8 image with
  the C drivers' edge clamping (yy outer, xx inner), concatenating output. -/
def encodeImage4x4 (blockEnc : List (List Nat) → List Nat)
    (pix : List (List Nat)) (w h : Nat) : List Nat :=
  let bw := (w + 3) / 4
  let bh := (h + 3) / 4
  (List.range (bh * bw)).foldl (fun (acc : List Nat) bi =>
    let (block, _) := astcGatherBlockU8 pix w h ((bi % bw) * 4) ((bi / bw) * 4) 4 4
    acc ++ blockEnc block) []

/-- `tc_bc1_compress_rgba8` (options are ignored by the C). -/
def bc1CompressRgba8 (pix : List (List Nat)) (w h : Nat) : List Nat :=
  encodeImage4x4 (fun block =>
    encodeBc1ColorBlock (block.map (fun p =>
      (p.getD 0 0, p.getD 1 0, p.getD 2 0, p.getD 3 0))) true) pix w h

/-- `tc_bc7_compress_rgba8` with `tc_bc7_options_init` defaults. -/
def bc7CompressRgba8 (pix : List (List Nat)) (w h : Nat) : List Nat :=
  encodeImage4x4 bc7EncodeBlockDefault pix w h

/-- `tc_uni_transcode_bc1`; `none` = decode failure (`TC_ERROR_CORRUPT`). -/
def uniTranscodeBc1 (bytes : List Nat) (w h : Nat) : Option (List Nat) :=
  (uniDecompressRgba8 bytes w h).map (fun img => bc1CompressRgba8 img w h)

/-- `tc_uni_transcode_bc7`; `none` = decode failure (`TC_ERROR_CORRUPT`). -/
def uniTranscodeBc7 (bytes : List Nat) (w h : Nat) : Option (List Nat) :=
  (uniDecompressRgba8 bytes w h).map (fun img => bc7CompressRgba8 img w h)

/-- `tc_uni_transcode_etc2`; `alpha` selects ETC2 RGBA (EAC alpha + RGB). -/
def uniTranscodeEtc2 (bytes : List Nat) (w h : Nat) (alpha : Bool) : Option (List Nat) :=
  (uniDecompressRgba8 bytes w h).map (fun img => etc2CompressRgba8 img w h alpha)

theorem uniTranscodeEtc2_none (bytes : List Nat) (w h : Nat) (alpha : Bool)
    (h0 : uniDecompressRgba8 bytes w h = none) : uniTranscodeEtc2 bytes w h alpha = none := by
  simp [uniTranscodeEtc2, h0]

/-- A failed decode propagates: no transcode output is produced. -/
theorem uniTranscodeBc1_none (bytes : List Nat) (w h : Nat)
    (h0 : uniDecompressRgba8 bytes w h = none) : uniTranscodeBc1 bytes w h = none := by
  simp [uniTranscodeBc1, h0]

theorem uniTranscodeBc7_none (bytes : List Nat) (w h : Nat)
    (h0 : uniDecompressRgba8 bytes w h = none) : uniTranscodeBc7 bytes w h = none := by
  simp [uniTranscodeBc7, h0]

end Texcomp
