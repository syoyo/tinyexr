/-
  TinyEXR - Lean models of the public texcomp decompress wrappers whose
  output is half/float rather than unorm8.

  Mirrors `tc_bc6h_decompress_rgb16f/_rgbaf`, `tc_bc7_decompress_rgbaf`
  and `tc_astc_hdr_decompress_rgbaf` with tightly packed strides. Odd
  dimensions and short buffers are handled by Option returns.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc6hFull
import Texcomp.Bc6hDecode
import Texcomp.Bc7DecodeImage
import Texcomp.AstcHdr

namespace Texcomp

set_option linter.unusedVariables false

def blocksX (w bs : Nat) : Nat := (w + bs - 1) / bs

def blockBytes (data : List UInt8) (bi n : Nat) : Fin n → UInt8 :=
  fun i => data.getD (bi * n + i.val) 0

/-- BC6H -> RGB half (3 x UInt16 per pixel), row-major. -/
def bc6hDecodeRgb16f (data : List UInt8) (w h : Nat) (isSigned : Bool) :
    Option (List UInt16) :=
  if w == 0 || h == 0 then some []
  else if data.length < bc6hImageBytes2 w h then none
  else
    let bx := blocksX w 4
    some ((List.range (w * h)).foldr (fun k acc =>
      let x := k % w
      let y := k / w
      let bi := (y / 4) * bx + x / 4
      let t := (y % 4) * 4 + x % 4
      let c := bc6hDecodeBlock (blockBytes data bi 16) isSigned ⟨t, by omega⟩
      [c.1, c.2.1, c.2.2] ++ acc) [])

/-- Convert packed half triples to RGBA float tuples with opaque alpha. -/
def halfTriplesToRgbaF : List UInt16 → List Float32
  | [] => []
  | r :: g :: b :: rest =>
      halfToFloat r.toNat :: halfToFloat g.toNat :: halfToFloat b.toNat ::
        (1.0 : Float32) :: halfTriplesToRgbaF rest
  | _ => []

/-- BC6H -> RGBA float: half channels plus alpha = 1.0f. -/
def bc6hDecodeRgbaf (data : List UInt8) (w h : Nat) (isSigned : Bool) :
    Option (List Float32) :=
  (bc6hDecodeRgb16f data w h isSigned).map halfTriplesToRgbaF

/-- BC7 RGBA8 -> RGBA float, dividing each channel by 255. -/
def bc7DecodeRgbaf (data : List UInt8) (w h : Nat) : Option (List Float32) :=
  (bc7DecodeImage2 data w h).map (fun bs =>
    bs.map (fun b => Float32.ofNat b.toNat / (255.0 : Float32)))

/-- ASTC HDR -> RGBA float, row-major for arbitrary block dimensions. -/
def astcHdrDecodeRgbaf (data : List UInt8) (w h bx byy : Nat) :
    Option (List Float32) := by
  by_cases hw : w == 0
  · exact some []
  by_cases hh : h == 0
  · exact some []
  by_cases hbx : bx == 0
  · exact none
  by_cases hby : byy == 0
  · exact none
  by_cases hrange : bx > 12 || byy > 12
  · exact none
  · have hbxp : 0 < bx := Nat.pos_of_ne_zero (by simpa using hbx)
    have hbyp : 0 < byy := Nat.pos_of_ne_zero (by simpa using hby)
    let bxc := blocksX w bx
    let need := bxc * ((h + byy - 1) / byy) * 16
    by_cases hshort : data.length < need
    · exact none
    · exact some ((List.range (w * h)).foldr (fun k acc =>
        let x := k % w
        let y := k / w
        let bi := (y / byy) * bxc + x / bx
        let t := (y % byy) * bx + x % bx
        let raw : List Nat := (List.range 16).map (fun i => (data.getD (bi * 16 + i) 0).toNat)
        let c := astcDecodeBlockHdr raw bx byy ⟨t % (bx * byy), Nat.mod_lt _ (Nat.mul_pos hbxp hbyp)⟩
        [c.1, c.2.1, c.2.2.1, c.2.2.2] ++ acc) [])

end Texcomp
