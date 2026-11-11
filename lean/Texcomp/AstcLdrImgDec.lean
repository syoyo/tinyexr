/-
  TinyEXR - ASTC LDR image-level decoder (Lean model).

  Ports `tc_astc_decode_block_rgba8` + `tc_astc_decode_image_rgba8` from
  `tools/texcomp/src/texcomp_astc_decode.c`: decode each 16-byte block once
  (error propagation as `Option`, mirroring the C's 0/1 returns), then copy
  the in-bounds texels into the row-major RGBA8 image. Reuses the block-mode
  / ISE / partition / CEM machinery from `AstcDecode.lean`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_decode_block_rgba8`: decode one 16-byte block into `bx * by`
  RGBA texels (row-major, each `[r, g, b, a]`). `none` on any decode failure
  (the C returns 0 and the image decode aborts with TC_ERROR_CORRUPT). -/
def astcDecodeBlockRgba8Opt (bytesList : List Nat) (bx by_ : Nat) :
    Option (List (List Nat)) :=
  let mode := rdBits bytesList 0 11
  if (mode &&& 0x1FF) == 0x1FC then
    -- void extent: bit 9 must be clear, then the constant colour is the
    -- high byte of each 16-bit lane at bytes 8..15
    if (mode &&& (1 <<< 9)) != 0 then none
    else
      let px := (List.range 4).map (fun c =>
        ((bytesList.getD (8 + c * 2) 0 ||| (bytesList.getD (9 + c * 2) 0 <<< 8)) >>> 8) % 256)
      some ((List.range (bx * by_)).map (fun _ => px))
  else
    match decodeBlockMode mode with
    | none => none
    | some bm =>
      if bm.wx > bx || bm.wy > by_ then none
      else
        let partCount := rdBits bytesList 11 2 + 1
        if bm.dual != 0 && partCount == 4 then none
        else
          let weightCount := bm.wx * bm.wy * (if bm.dual != 0 then 2 else 1)
          if weightCount > 64 then none
          else
            let weightBits := iseBitcount weightCount bm.quant
            if weightBits < 24 || weightBits > 96 then none
            else
              let rev := (List.range 16).map (fun i => bitrev8 (bytesList.getD (15 - i) 0))
              match iseDecode bm.quant weightCount rev 0 with
              | none => none
              | some wsyms =>
                let uq := weightUnquant.getD bm.quant []
                let wgrid0 := (List.range (bm.wx * bm.wy)).map (fun i =>
                  uq.getD (wsyms.getD (if bm.dual != 0 then i * 2 else i) 0) 0)
                let wgrid1 := (List.range (bm.wx * bm.wy)).map (fun i =>
                  uq.getD (wsyms.getD (i * 2 + 1) 0) 0)
                let partsInfo : Option (List Nat × Nat × Nat × Nat) :=
                  if partCount == 1 then
                    some ([rdBits bytesList 13 4], 17, 0, 0)
                  else
                    let pindex := rdBits bytesList 13 10
                    let cf := rdBits bytesList 23 6
                    if (cf &&& 3) == 0 then
                      some ((List.range partCount).map (fun _ => cf >>> 2), 29, 0, pindex)
                    else
                      let baseClass := (cf &&& 3) - 1
                      let extra := 3 * partCount - 4
                      if weightBits + extra > 128 - 29 then none
                      else
                        let extPos := 128 - weightBits - extra
                        let code := cf + (rdBits bytesList extPos extra <<< 6)
                        some ((List.range partCount).map (fun i =>
                          (((baseClass + ((code >>> (2 + i)) &&& 1)) <<< 2) +
                           ((code >>> (2 + partCount + 2 * i)) &&& 3))), 29, extra, pindex)
                match partsInfo with
                | none => none
                | some (cems, colorStart, extraBits, pindex) =>
                  let ccsInfo : Option Nat :=
                    if bm.dual != 0 then
                      if weightBits + extraBits + 2 > 128 - colorStart then none
                      else some (rdBits bytesList (128 - weightBits - extraBits - 2) 2)
                    else some 3
                  match ccsInfo with
                  | none => none
                  | some ccs =>
                    let ccsBits := if bm.dual != 0 then 2 else 0
                    let vcount := (List.range partCount).foldl (fun acc i =>
                      acc + (((cems.getD i 0 >>> 2) + 1) * 2)) 0
                    if vcount > 18 then none
                    else
                      let used := colorStart + weightBits + extraBits + ccsBits
                      if used > 128 then none
                      else
                        let avail := 128 - used
                        let cq := (List.range 21).reverse.find? (fun i =>
                          (not (i < 4)) && (iseBitcount vcount i <= avail))
                        match cq with
                        | none => none
                        | some cq =>
                          match iseDecode cq vcount bytesList colorStart with
                          | none => none
                          | some csyms =>
                            let cu := colorUnquant.getD (cq - 4) []
                            let vals := (List.range vcount).map (fun i =>
                              if cq == 20 then csyms.getD i 0 else cu.getD (csyms.getD i 0) 0)
                            let foldEl (acc : Option (List ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat)) × Nat)) i :=
                              match acc with
                              | none => none
                              | some (l, off) =>
                                match decodeCem (cems.getD i 0) (vals.drop off) with
                                | none => none
                                | some (e0, e1, n) => some (l ++ [(e0, e1)], off + n)
                            match (List.range partCount).foldl foldEl (some ([], 0)) with
                            | none => none
                            | some (elist, consumed) =>
                              if consumed != vcount then none
                              else
                                let smallBlock := bx * by_ < 32
                                let texel := fun t : Nat =>
                                  let x := t % bx
                                  let y := t / bx
                                  let part := if partCount == 1 then 0
                                              else selectPartition pindex x y partCount smallBlock
                                  let part := if part >= partCount then partCount - 1 else part
                                  let w0 := infillWeight wgrid0 bm.wx bm.wy bx by_ x y
                                  let w1 := if bm.dual != 0 then
                                    infillWeight wgrid1 bm.wx bm.wy bx by_ x y else w0
                                  let (e0, e1) := elist.getD part ((0, 0, 0, 0), (0, 0, 0, 0))
                                  let chan := fun t : Nat × Nat × Nat × Nat => fun c =>
                                    match c with | 0 => t.1 | 1 => t.2.1 | 2 => t.2.2.1 | _ => t.2.2.2
                                  let interp := fun c w =>
                                    ((((chan e0 c) * (64 - w) + (chan e1 c) * w) * 257 + 32) / 64) / 256
                                  [interp 0 (if bm.dual != 0 && ccs == 0 then w1 else w0),
                                   interp 1 (if bm.dual != 0 && ccs == 1 then w1 else w0),
                                   interp 2 (if bm.dual != 0 && ccs == 2 then w1 else w0),
                                   interp 3 (if bm.dual != 0 && ccs == 3 then w1 else w0)]
                                some ((List.range (bx * by_)).map texel)

/-- `tc_astc_decode_image_rgba8`: decode a `bw × bh` grid of 16-byte blocks
  (row-major, block row `j` outer) into a row-major `width × height` RGBA8
  image, copying only the in-bounds texels of edge blocks. `none` when any
  block fails to decode (TC_ERROR_CORRUPT) or the block dims exceed the
  2D footprint bound (TC_ERROR_UNSUPPORTED). -/
def astcDecodeImageRgba8 (blocks : List (List Nat)) (width height bx by_ : Nat) :
    Option (List (List Nat)) :=
  if bx == 0 || by_ == 0 || bx > 12 || by_ > 12 then none
  else
    let bw := (width + bx - 1) / bx
    let bh := (height + by_ - 1) / by_
    let step (acc : Option (List (List Nat))) bi :=
      match acc with
      | none => none
      | some img =>
        let j := bi / bw
        let i := bi % bw
        match astcDecodeBlockRgba8Opt (blocks.getD (j * bw + i) []) bx by_ with
        | none => none
        | some texels =>
          let img := (List.range (by_ * bx)).foldl (fun (img : List (List Nat)) t =>
            let y := t / bx
            let x := t % bx
            let py := j * by_ + y
            let px := i * bx + x
            if py < height && px < width then
              img.set (py * width + px) (texels.getD t [0, 0, 0, 0])
            else img) img
          some img
    ((List.range (bh * bw)).foldl step (some ((List.range (width * height)).map (fun _ => [0, 0, 0, 0]))))

end Texcomp
