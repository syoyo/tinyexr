/-
  TinyEXR - texcomp "uni" universal transcodable texture (Lean model).

  Models `tools/texcomp/src/texcomp_uni.c`. A uni image stores one UASTC LDR
  4x4 block (16 bytes) per 4x4 tile. Modelled entry points:

    tc_uni_compressed_size    -> `uniCompressedSize`
    tc_uni_compress_rgba8     -> `uniCompressRgba8`  (= `astcCompressRgba8`
                                  with 4x4 blocks, uastc = 1; the quality field
                                  is irrelevant on the UASTC path)
    tc_uni_decompress_rgba8   -> `uniDecompressRgba8` (= 4x4 ASTC image decode)
    tc_uni_transcode_astc     -> `uniTranscodeAstc`   (byte copy)

  The BC7 / BC1 / ETC2 transcodes are "decode, then run the target's
  whole-image encoder". The decode half is `uniDecompressRgba8`; the
  whole-image BC7/BC1/ETC2 encoder drivers are not modelled in Lean (only their
  block encoders are), so those three transcodes are a documented boundary.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcLdrImg
import Texcomp.AstcLdrImgDec

namespace Texcomp

/-- `TC_UNI_BLOCK_BYTES`. -/
def uniBlockBytes : Nat := 16

/-- `tc_uni_compressed_size`: `ceil(w/4) * ceil(h/4) * 16`. -/
def uniCompressedSize (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * uniBlockBytes

/-- `tc_uni_compress_rgba8` (quality is unused by the UASTC path; the C
  options default is 2). -/
def uniCompressRgba8 (pix : List (List Nat)) (w h : Nat) : List Nat :=
  astcCompressRgba8 pix w h 4 4 2 1

/-- Split a flat byte stream into 16-byte blocks (missing bytes read as 0,
  which the C never reaches because the size is validated by the caller). -/
def uniBlocks (bytes : List Nat) (n : Nat) : List (List Nat) :=
  (List.range n).map (fun i => (List.range uniBlockBytes).map (fun c =>
    bytes.getD (i * uniBlockBytes + c) 0))

/-- `tc_uni_decompress_rgba8`: per-block 4x4 ASTC decode; `none` is
  `TC_ERROR_CORRUPT`. -/
def uniDecompressRgba8 (bytes : List Nat) (w h : Nat) : Option (List (List Nat)) :=
  astcDecodeImageRgba8 (uniBlocks bytes (((w + 3) / 4) * ((h + 3) / 4))) w h 4 4

/-- `tc_uni_transcode_astc`: the stored blocks already are ASTC 4x4. -/
def uniTranscodeAstc (bytes : List Nat) (w h : Nat) : List Nat :=
  (uniBlocks bytes (((w + 3) / 4) * ((h + 3) / 4))).foldr (· ++ ·) []

theorem uniCompressedSize_mul16 (w h : Nat) : uniCompressedSize w h % 16 = 0 := by
  unfold uniCompressedSize uniBlockBytes
  exact Nat.mul_mod_left _ 16

theorem uniBlocks_length (bytes : List Nat) (n : Nat) : (uniBlocks bytes n).length = n := by
  simp [uniBlocks]

/-- Every block `uniBlocks` yields has exactly 16 bytes. -/
theorem uniBlocks_block_length (bytes : List Nat) (n : Nat) (b : List Nat)
    (hb : b ∈ uniBlocks bytes n) : b.length = uniBlockBytes := by
  simp [uniBlocks] at hb
  obtain ⟨_, _, rfl⟩ := hb
  simp

/-- The ASTC transcode always emits exactly `uniCompressedSize` bytes
  (the C `memcpy` of `tc_uni_compressed_size` bytes). -/
theorem uniTranscodeAstc_length (bytes : List Nat) (w h : Nat) :
    (uniTranscodeAstc bytes w h).length = uniCompressedSize w h := by
  have key : ∀ (l : List (List Nat)), (∀ b ∈ l, b.length = uniBlockBytes) →
      (l.foldr (· ++ ·) []).length = l.length * uniBlockBytes := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [List.foldr_cons, List.length_append, ha, ht, List.length_cons]
      rw [Nat.succ_mul]; omega
  unfold uniTranscodeAstc uniCompressedSize
  rw [key _ (fun b hb => uniBlocks_block_length _ _ b hb), uniBlocks_length]

end Texcomp
