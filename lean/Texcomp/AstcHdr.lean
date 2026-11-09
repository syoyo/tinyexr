/-
  TinyEXR - Lean 4 formalization of the ASTC HDR decode path.

  Ports the HDR variants of
  `tools/texcomp/src/texcomp_astc_decode.c`:
  void-extent (FP16 direct / UNORM16), HDR endpoint unpacks for CEM
  2/3/7/11/14/15 (with the LDR endpoint modes as a legal fallback inside
  HDR texture), and the final 16-bit domain conversion kernels
  (`lns16ToSf16`, `unorm16ToSf16`, `halfToFloat`). The block front-end
  (block mode, weights, partitions, CEM extraction) mirrors
  `Texcomp.AstcDecode.astcDecodeBlock`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

open scoped Nat

/-- IEEE half (sf16) → float32, mirroring `tacd_half_to_float`. -/
def halfToFloat (h : Nat) : Float32 :=
  let sign : Nat := ((h &&& 0x8000) <<< 16)
  let exp : Nat := (h >>> 10) &&& 0x1F
  let man0 : Nat := h &&& 0x3FF
  let rec go : Nat → Nat → Nat → Nat × Nat
    | 0, man, e => (man, e)
    | fuel + 1, man, e =>
      if (man &&& 0x400) != 0 then (man, e) else go fuel (man <<< 1) (e - 1)
  if exp == 0 then
    if man0 == 0 then Float32.ofBits (UInt32.ofNat sign)
    else
      let (man', e') := go 11 man0 (127 - 15 + 1)
      Float32.ofBits (UInt32.ofNat (sign ||| (e' <<< 23) ||| ((man' &&& 0x3FF) <<< 13)))
  else if exp == 31 then
    Float32.ofBits (UInt32.ofNat (sign ||| 0x7F800000 ||| (man0 <<< 13)))
  else
    Float32.ofBits (UInt32.ofNat (sign ||| ((exp + 127 - 15) <<< 23) ||| (man0 <<< 13)))

/-- UNORM16 → FP16 (astcenc `unorm16_to_sf16` / spec C.2.19). -/
def unorm16ToSf16 (p : Nat) : Nat :=
  if p == 0xFFFFFFFF then 0x3C00
  else if p < 4 then p <<< 8
  else
    let rec lz : Nat → Nat → Nat → Nat
      | 0, t, l => l
      | fuel + 1, t, l => if (t &&& 0x8000) != 0 then l else lz fuel (t <<< 1) (l + 1)
    let l := lz 16 (p &&& 0xFFFF) 0
    let p' := ((p <<< (l + 1)) &&& 0xFFFF) >>> 6
    p' ||| ((14 - l) <<< 10)

/-- LNS16 → FP16 bits, mirroring `tc_astc_lns16_to_sf16` (astcenc write to
  `lns_to_sf16`). The input domain is the 16-bit LNS value; the output
  clamps at the max FP16 (0x7BFF). -/
def lns16ToSf16 (p : Nat) : Nat :=
  let p := p &&& 0xFFFF
  let mc : Nat := p &&& 0x7FF
  let ec : Nat := p >>> 11
  let mt : Int :=
    if mc < 512 then (mc : Int) * 3
    else if mc < 1536 then (mc : Int) * 4 - 512
    else (mc : Int) * 5 - 2048
  let res : Int := (ec <<< 10) + (mt >>> 3)
  if res > 0x7BFF then 0x7BFF else res.toNat

/-- HDR alpha unpack (CEM 14/15 extra pair); port of
  `tc_astc_hdr_alpha_unpack`. Returns `(a0, a1)` 16-bit LNS. -/
def hdrAlphaUnpack (v : List Nat) : Nat × Nat :=
  let v6 := v.getD 0 0
  let v7 := v.getD 1 0
  let modeval : Nat := ((v6 >>> 7) &&& 1) ||| ((v7 >>> 6) &&& 2)
  let v6' := v6 &&& 0x7F
  let v7' := v7 &&& 0x7F
  if modeval == 3 then ((v6' <<< 5) <<< 4, (v7' <<< 5) <<< 4)
  else
    let v6'' := v6' ||| ((v7' <<< (modeval + 1)) &&& 0x780)
    let v7a := v7' &&& (0x3F >>> modeval)
    let v7b : Int := ((v7a ^^^ (32 >>> modeval) : Nat) : Int) - (32 >>> modeval)
    let u : Int := Int.emod v7b (1 <<< 32)
    let w : Int := Int.emod (u <<< (4 - modeval)) (1 <<< 32)
    let w' : Int := if w >= (1 <<< 31) then w - (1 <<< 32) else w
    let v6''' := v6'' <<< (4 - modeval)
    let ssum : Int := (v6''' : Int) + w'
    let sclamped : Int := if ssum < 0 then 0 else if ssum > 0xFFF then 0xFFF else ssum
    ((v6''' <<< 4), (sclamped.toNat <<< 4))

/-- Set a bit in `x` when `c` holds (avoids term-mode mutation). -/
def setBit (x : Nat) (c : Bool) (bit : Nat) : Nat := if c then x ||| bit else x

/-- CEM 11 unpack: 6 values → two endpoints as 16-bit LNS (port of
  `tc_astc_cem11_unpack`). Returns `(e0(3), e1(3))`. -/
def cem11Unpack (v : List Nat) :
    (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  let v0 := v.getD 0 0
  let v1 := v.getD 1 0
  let v2 := v.getD 2 0
  let v3 := v.getD 3 0
  let v4 := v.getD 4 0
  let v5 := v.getD 5 0
  let modeval : Nat := ((v1 >>> 7) &&& 1) ||| (((v2 >>> 7) &&& 1) <<< 1) |||
    (((v3 >>> 7) &&& 1) <<< 2)
  let majcomp : Nat := ((v4 >>> 7) &&& 1) ||| (((v5 >>> 7) &&& 1) <<< 1)
  if majcomp == 3 then
    (((v0 <<< 8), (v2 <<< 8), ((v4 &&& 0x7F) <<< 9)),
     ((v1 <<< 8), (v3 <<< 8), ((v5 &&& 0x7F) <<< 9)))
  else
    let dbits := [7, 6, 7, 6, 5, 6, 5, 6].getD modeval 7
    let a0 : Nat := v0 ||| ((v1 &&& 0x40) <<< 2)
    let b0 : Nat := v2 &&& 0x3F
    let b1 : Nat := v3 &&& 0x3F
    let c0 : Nat := v1 &&& 0x3F
    let d0 : Nat := v4 &&& 0x7F
    let d1 : Nat := v5 &&& 0x7F
    let bit0 := (v2 >>> 6) &&& 1
    let bit1 := (v3 >>> 6) &&& 1
    let bit2 := (v4 >>> 6) &&& 1
    let bit3 := (v5 >>> 6) &&& 1
    let bit4 := (v4 >>> 5) &&& 1
    let bit5 := (v5 >>> 5) &&& 1
    let ohmod := 1 <<< modeval
    let a : Nat := a0
    let a := setBit a ((ohmod &&& 0xA4) != 0) (bit0 <<< 9)
    let a := setBit a ((ohmod &&& 0x8) != 0) (bit2 <<< 9)
    let a := setBit a ((ohmod &&& 0x50) != 0) (bit4 <<< 9)
    let a := setBit a ((ohmod &&& 0x50) != 0) (bit5 <<< 10)
    let a := setBit a ((ohmod &&& 0xA0) != 0) (bit1 <<< 10)
    let a := setBit a ((ohmod &&& 0xC0) != 0) (bit2 <<< 11)
    let c : Nat := c0
    let c := setBit c ((ohmod &&& 0x4) != 0) (bit1 <<< 6)
    let c := setBit c ((ohmod &&& 0xE8) != 0) (bit3 <<< 6)
    let c := setBit c ((ohmod &&& 0x20) != 0) (bit2 <<< 7)
    let b0' := setBit (setBit b0 ((ohmod &&& 0x5B) != 0) (bit0 <<< 6))
      ((ohmod &&& 0x12) != 0) (bit2 <<< 7)
    let b1' := setBit (setBit b1 ((ohmod &&& 0x5B) != 0) (bit1 <<< 6))
      ((ohmod &&& 0x12) != 0) (bit3 <<< 7)
    let d0' := setBit (setBit d0 ((ohmod &&& 0xAF) != 0) (bit4 <<< 5))
      ((ohmod &&& 0x5) != 0) (bit2 <<< 6)
    let d1' := setBit (setBit d1 ((ohmod &&& 0xAF) != 0) (bit5 <<< 5))
      ((ohmod &&& 0x5) != 0) (bit3 <<< 6)
    let signExt (x : Nat) (bits : Nat) : Int :=
      let x' := x &&& ((1 <<< bits) - 1)
      if x' >= (1 <<< (bits - 1)) then (x' : Int) - (1 <<< bits) else (x' : Int)
    let d0s : Int := signExt d0' dbits
    let d1s : Int := signExt d1' dbits
    let valsh : Nat := (modeval >>> 1) ^^^ 3
    let sc : Nat := 1 <<< valsh
    let a' : Int := ((a * sc : Nat) : Int)
    let b0s : Int := ((b0' * sc : Nat) : Int)
    let b1s : Int := ((b1' * sc : Nat) : Int)
    let cs : Int := ((c * sc : Nat) : Int)
    let r1 : Int := a'
    let g1 : Int := a' - b0s
    let bl1 : Int := a' - b1s
    let r0 : Int := a' - cs
    let g0 : Int := a' - b0s - cs - d0s * (sc : Int)
    let bl0 : Int := a' - b1s - cs - d1s * (sc : Int)
    let scOf (x : Int) : Nat := if x < 0 then 0 else if x > 4095 then 4095 else x.toNat
    let (r0', g0', bl0', r1', g1', bl1') :=
      if majcomp == 1 then (g0, r0, bl0, g1, r1, bl1)
      else if majcomp == 2 then (bl0, g0, r0, bl1, g1, r1)
      else (r0, g0, bl0, r1, g1, bl1)
    (((scOf r0' <<< 4), (scOf g0' <<< 4), (scOf bl0' <<< 4)),
     ((scOf r1' <<< 4), (scOf g1' <<< 4), (scOf bl1' <<< 4)))

/-- CEM 7 unpack: 4 values → two LNS endpoints (port of
  `tc_astc_cem7_unpack`). Returns `(e0(3), e1(3))`. -/
def cem7Unpack (v : List Nat) :
    (Nat × Nat × Nat) × (Nat × Nat × Nat) :=
  let v0 := v.getD 0 0
  let v1 := v.getD 1 0
  let v2 := v.getD 2 0
  let v3 := v.getD 3 0
  let modeval : Nat := ((v0 &&& 0xC0) >>> 6) ||| (((v1 >>> 7) &&& 1) <<< 2) |||
    (((v2 >>> 7) &&& 1) <<< 3)
  let (majcomp, mode) :=
    if (modeval &&& 0xC) != 0xC then (modeval >>> 2, modeval &&& 3)
    else if modeval != 0xF then (modeval &&& 3, 4)
    else (0, 5)
  let oh : Nat := 1 <<< mode
  let shamts : List Nat := [1, 1, 2, 3, 4, 5]
  let red0 : Nat := v0 &&& 0x3F
  let grn0 : Nat := v1 &&& 0x1F
  let blu0 : Nat := v2 &&& 0x1F
  let sca0 : Nat := v3 &&& 0x1F
  let bit0 := (v1 >>> 6) &&& 1
  let bit1 := (v1 >>> 5) &&& 1
  let bit2 := (v2 >>> 6) &&& 1
  let bit3 := (v2 >>> 5) &&& 1
  let bit4 := (v3 >>> 7) &&& 1
  let bit5 := (v3 >>> 6) &&& 1
  let bit6 := (v3 >>> 5) &&& 1
  let green1 := setBit (setBit grn0 ((oh &&& 0x30) != 0) (bit0 <<< 6))
    ((oh &&& 0x3A) != 0) (bit1 <<< 5)
  let blue1 := setBit (setBit blu0 ((oh &&& 0x30) != 0) (bit2 <<< 6))
    ((oh &&& 0x3A) != 0) (bit3 <<< 5)
  let scale1 := setBit (setBit (setBit sca0 ((oh &&& 0x3D) != 0) (bit6 <<< 5))
    ((oh &&& 0x2D) != 0) (bit5 <<< 6)) ((oh &&& 0x04) != 0) (bit4 <<< 7)
  let red1 : Nat := red0
  let red1 := setBit red1 ((oh &&& 0x3B) != 0) (bit4 <<< 6)
  let red1 := setBit red1 ((oh &&& 0x04) != 0) (bit3 <<< 6)
  let red1 := setBit red1 ((oh &&& 0x10) != 0) (bit5 <<< 7)
  let red1 := setBit red1 ((oh &&& 0x0F) != 0) (bit2 <<< 7)
  let red1 := setBit red1 ((oh &&& 0x05) != 0) (bit1 <<< 8)
  let red1 := setBit red1 ((oh &&& 0x0A) != 0) (bit0 <<< 8)
  let red1 := setBit red1 ((oh &&& 0x05) != 0) (bit0 <<< 9)
  let red1 := setBit red1 ((oh &&& 0x02) != 0) (bit6 <<< 9)
  let red1 := setBit red1 ((oh &&& 0x01) != 0) (bit3 <<< 10)
  let red1 := setBit red1 ((oh &&& 0x02) != 0) (bit5 <<< 10)
  let sh : Nat := shamts.getD mode 1
  let redB : Int := (red1 <<< sh : Nat)
  let grnB : Int := (green1 <<< sh : Nat)
  let bluB : Int := (blue1 <<< sh : Nat)
  let scaB : Int := (scale1 <<< sh : Nat)
  let (red', green', blue') :=
    if mode != 5 then (redB, redB - grnB, redB - bluB) else (redB, grnB, bluB)
  let (red'', green'', blue'') :=
    if majcomp == 1 then (green', red', blue')
    else if majcomp == 2 then (blue', green', red')
    else (red', green', blue')
  let r0 : Int := red'' - scaB
  let g0 : Int := green'' - scaB
  let b0 : Int := blue'' - scaB
  let cl (x : Int) : Nat := if x <= 0 then 0 else x.toNat
  (((cl r0 <<< 4), (cl g0 <<< 4), (cl b0 <<< 4)),
   ((cl red'' <<< 4), (cl green'' <<< 4), (cl blue'' <<< 4)))

/-- Unpack one partition's endpoints into the 16-bit interpolation
  domain, mirroring `tacd_hdr_unpack_endpoints`. Returns
  `(e0(4), e1(4), rgbHdr, alphaHdr)` or `none` on failure. -/
def hdrUnpackEndpoints (cem : Nat) (v : List Nat) :
    Option ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) × Bool × Bool) :=
  let widen (rgbHdr alphaHdr : Bool)
      (e0 : Nat × Nat × Nat × Nat) (e1 : Nat × Nat × Nat × Nat) :=
    let w := fun (hdr : Bool) (x : Nat) => if hdr then x else x * 257
    ((w rgbHdr e0.1, w rgbHdr e0.2.1, w rgbHdr e0.2.2.1, w alphaHdr e0.2.2.2),
     (w rgbHdr e1.1, w rgbHdr e1.2.1, w rgbHdr e1.2.2.1, w alphaHdr e1.2.2.2),
     rgbHdr, alphaHdr)
  match cem with
  | 2 =>
    let v0 := v.getD 0 0
    let v1 := v.getD 1 0
    let (y0, y1) := if v1 >= v0 then (v0 <<< 4, v1 <<< 4) else ((v1 <<< 4) + 8, (v0 <<< 4) - 8)
    let (e0, e1) := ((y0 <<< 4, y0 <<< 4, y0 <<< 4, 0x7800), (y1 <<< 4, y1 <<< 4, y1 <<< 4, 0x7800))
    some (widen true true e0 e1)
  | 3 =>
    let v0 := v.getD 0 0
    let v1 := v.getD 1 0
    let (y0, y1) :=
      if (v0 &&& 0x80) != 0 then
        (((v1 &&& 0xE0) <<< 4) ||| ((v0 &&& 0x7F) <<< 2), (v1 &&& 0x1F) <<< 2)
      else
        (((v1 &&& 0xF0) <<< 4) ||| ((v0 &&& 0x7F) <<< 1), (v1 &&& 0x0F) <<< 1)
    let y1 := if y1 + y0 > 0xFFF then 0xFFF else y1 + y0
    let (e0, e1) := ((y0 <<< 4, y0 <<< 4, y0 <<< 4, 0x7800), (y1 <<< 4, y1 <<< 4, y1 <<< 4, 0x7800))
    some (widen true true e0 e1)
  | 7 =>
    let (a, b) := cem7Unpack v
    let (a1, a2, a3) := a
    let (b1, b2, b3) := b
    let (e0, e1) := ((a1, a2, a3, 0x7800), (b1, b2, b3, 0x7800))
    some (widen true true e0 e1)
  | 11 =>
    let (a, b) := cem11Unpack v
    let (a1, a2, a3) := a
    let (b1, b2, b3) := b
    let (e0, e1) := ((a1, a2, a3, 0x7800), (b1, b2, b3, 0x7800))
    some (widen true true e0 e1)
  | 14 =>
    let (a, b) := cem11Unpack v
    let (a1, a2, a3) := a
    let (b1, b2, b3) := b
    let (e0, e1) := ((a1, a2, a3, v.getD 6 0), (b1, b2, b3, v.getD 7 0))
    some (widen true false e0 e1)
  | 15 =>
    let (a, b) := cem11Unpack v
    let (a1, a2, a3) := a
    let (b1, b2, b3) := b
    let (aa0, aa1) := hdrAlphaUnpack [v.getD 6 0, v.getD 7 0]
    let (e0, e1) := ((a1, a2, a3, aa0), (b1, b2, b3, aa1))
    some (widen true true e0 e1)
  | _ =>
    match decodeCem cem v with
    | some (e0, e1, _) => some (widen false false e0 e1)
    | none => none

/-- Convert a 16-bit domain record to float, per `tacd_*_to_sf16` + half. -/
def recToFloat (hdr : Bool) (rec : Int) : Float32 :=
  let rec' := if rec < 0 then 0 else if rec > 0xFFFF then 0xFFFF else rec.toNat
  if hdr then halfToFloat (lns16ToSf16 rec')
  else halfToFloat (unorm16ToSf16 rec')

/-- Decode one ASTC HDR block to bw*bh RGBA float texels (row-major),
  mirroring `tc_astc_decode_block_hdr_rgbaf`. Invalid → zeros. -/
def astcDecodeBlockHdr (bytesList : List Nat) (bw bh : Nat) :
    Fin (bw * bh) → (Float32 × Float32 × Float32 × Float32) :=
  fun texel =>
    let mode := rdBits bytesList 0 11
    let zero : Float32 × Float32 × Float32 × Float32 := (0, 0, 0, 0)
    if (mode &&& 0x1FF) == 0x1FC then
      let hdr := (mode &&& (1 <<< 9)) != 0
      let v := fun c => (bytesList.getD (8 + c * 2) 0 ||| (bytesList.getD (9 + c * 2) 0 <<< 8))
      let conv := fun c => if hdr then halfToFloat (v c) else halfToFloat (unorm16ToSf16 (v c))
      (conv 0, conv 1, conv 2, conv 3)
    else
      match decodeBlockMode mode with
      | none => zero
      | some bm =>
        if bm.wx > bw || bm.wy > bh then zero
        else
          let partCount := rdBits bytesList 11 2 + 1
          if bm.dual != 0 && partCount == 4 then zero
          else
            let weightCount := bm.wx * bm.wy * (if bm.dual != 0 then 2 else 1)
            let weightBits := iseBitcount weightCount bm.quant
            if weightCount > 64 || weightBits < 24 || weightBits > 96 then zero
            else
              let rev := (List.range 16).map (fun i => bitrev8 (bytesList.getD (15 - i) 0))
              match iseDecode bm.quant weightCount rev 0 with
              | none => zero
              | some wvalues =>
                let wx := bm.wx
                let wy := bm.wy
                let uq := weightUnquant.getD bm.quant []
                let wgrid0 := (List.range (wx * wy)).map (fun i =>
                  uq.getD (wvalues.getD (if bm.dual != 0 then i * 2 else i) 0) 0)
                let wgrid1 := (List.range (wx * wy)).map (fun i =>
                  uq.getD (wvalues.getD (i * 2 + 1) 0) 0)
                let (cems, colorStart, extraBits, pindex) :
                    (List Nat × Nat × Nat × Nat) :=
                  if partCount == 1 then
                    ([rdBits bytesList 13 4], 17, 0, 0)
                  else
                    let pindex := rdBits bytesList 13 10
                    let cf := rdBits bytesList 23 6
                    if (cf &&& 3) == 0 then
                      ((List.range partCount).map (fun _ => cf >>> 2), 29, 0, pindex)
                    else
                      let baseClass := (cf &&& 3) - 1
                      let extra := 3 * partCount - 4
                      let extPos := 128 - weightBits - extra
                      let code := cf + (rdBits bytesList extPos extra <<< 6)
                      ((List.range partCount).map (fun i =>
                        (((baseClass + ((code >>> (2 + i)) &&& 1)) <<< 2) +
                         ((code >>> (2 + partCount + 2 * i)) &&& 3))), 29, extra, pindex)
                let (extraBits', ccs) :
                    (Nat × Nat) :=
                  if bm.dual != 0 then
                    (extraBits, rdBits bytesList (128 - weightBits - extraBits - 2) 2)
                  else (extraBits, 3)
                let ccsBits := if bm.dual != 0 then 2 else 0
                let vcount := (List.range partCount).foldl (fun acc i =>
                  acc + (((cems.getD i 0 >>> 2) + 1) * 2)) 0
                let used := colorStart + weightBits + extraBits' + ccsBits
                let avail := 128 - used
                let cq := (List.range 21).reverse.find? (fun i =>
                  (not (i < 4)) && (iseBitcount vcount i <= avail))
                match cq with
                | none => zero
                | some cq =>
                  match iseDecode cq vcount bytesList colorStart with
                  | none => zero
                  | some csyms =>
                    let cu := colorUnquant.getD (cq - 4) []
                    let vals := (List.range vcount).map (fun i =>
                      if cq == 20 then csyms.getD i 0 else cu.getD (csyms.getD i 0) 0)
                    let (elist, consumed) :=
                      (List.range partCount).foldl (fun a i =>
                        match hdrUnpackEndpoints (cems.getD i 0) (vals.drop a.2) with
                        | none => (a.1, a.2)
                        | some u => (a.1 ++ [u], a.2 + 2 * ((cems.getD i 0 >>> 2) + 1)))
                        (([] : List ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) × Bool × Bool)), 0)
                    if consumed != vals.length then zero
                    else
                      let smallBlock := bw * bh < 32
                      let x := texel.val % bw
                      let y := texel.val / bw
                      let part := if partCount == 1 then 0
                                  else selectPartition pindex x y partCount smallBlock
                      let part := if part >= partCount then partCount - 1 else part
                      let w0 := infillWeight wgrid0 wx wy bw bh x y
                      let w1 := if bm.dual != 0 then infillWeight wgrid1 wx wy bw bh x y else w0
                      let (e0, e1, rgbHdr, alphaHdr) :=
                        elist.getD part ((0, 0, 0, 0), (0, 0, 0, 0), false, false)
                      let chan := fun (t : Nat × Nat × Nat × Nat) (c : Nat) =>
                        match c with | 0 => t.1 | 1 => t.2.1 | 2 => t.2.2.1 | _ => t.2.2.2
                      let lane (c : Nat) (w : Nat) : Float32 :=
                        let hdr := if c == 3 then alphaHdr else rgbHdr
                        let recVal := ((chan e0 c) * (64 - w) + (chan e1 c) * w + 32) >>> 6
                        recToFloat hdr (recVal : Int)
                      (lane 0 (if bm.dual != 0 && ccs == 0 then w1 else w0),
                       lane 1 (if bm.dual != 0 && ccs == 1 then w1 else w0),
                       lane 2 (if bm.dual != 0 && ccs == 2 then w1 else w0),
                       lane 3 (if bm.dual != 0 && ccs == 3 then w1 else w0))

end Texcomp
