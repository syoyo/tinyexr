/-
  TinyEXR - Lean 4 formalization of the ASTC HDR endpoint packers
  (encoder side).

  Ports `tc_astc_cem11_pack`, `tc_astc_cem11_unpack`, `tc_astc_cem15_pack` /
  `_unpack`, `tc_astc_cem7_pack` / `_unpack`, `tc_astc_hdr_alpha_pack` /
  `_unpack` and `tc_astc_hdr_write_void_extent` in
  `tools/texcomp/src/texcomp_astc_hdr.c`. The packers quantize endpoints
  through `tc_astc_hdr_color_roundtrip` (colour quant level); level 20
  (identity) is the common case, the sub-256 levels are used by the
  2-subset block encoder. Integer kernels use `Int32` (C
  `int`), floats use `Float32` with the C evaluation order and `rtn`
  (round half away from zero).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Math
import Texcomp.AstcColorQuant

namespace Texcomp

set_option linter.unusedVariables false

/-- tc_rtn: round to nearest integer, halves away from zero.
  `(int)(x >= 0 ? x + 0.5f : x - 0.5f)` -/
def rtnF (x : Float32) : Int32 :=
  Int32.ofInt (Tocio.truncToIntF (if x ≥ 0.0 then x + 0.5 else x - 0.5))

/-- Clamp a float into [lo, hi]. -/
def fclamp (x lo hi : Float32) : Float32 := if x < lo then lo else if x > hi then hi else x

/-- Low 8 bits of an `Int32` as `Nat` (C `(uint8_t)` cast). -/
def byteOf (x : Int32) : Nat := x.toUInt32.toNat &&& 0xFF

/-- `i32` arithmetic helpers: explicit argument types keep every literal
  `Int32` (Lean would otherwise leave bare literals as `Nat`). -/
def band (a b : Int32) : Int32 := a &&& b
def bor (a b : Int32) : Int32 := a ||| a &&& b ||| b -- keep both args used
def bshl (a b : Int32) : Int32 := a <<< b
def bshr (a b : Int32) : Int32 := a >>> b

/-- HDR alpha pack: two LNS alpha endpoints → 2 packed values (port of
  `tc_astc_hdr_alpha_pack`). -/
def hdrAlphaPack (alns0 alns1 : Int) : Nat × Nat :=
  let ia0 : Int32 := rtnF (fclamp (Float32.ofInt alns0) 0.0 65280.0)
  let ia1 : Int32 := rtnF (fclamp (Float32.ofInt alns1) 0.0 65280.0)
  let val0 (i : Int32) : Int32 := bshr (ia0 + bshr 128 i) (8 - i)
  let val1 (i : Int32) : Int32 := bshr (ia1 + bshr 128 i) (8 - i)
  let diffv (i : Int32) : Int32 := val1 i - val0 i
  let cutoff (i : Int32) : Int32 := bshr 32 i
  let enc (i : Int32) : Nat × Nat :=
    let v6 : Int32 := bor (band (val0 i) 0x7F) (bshl (band i 1) 7)
    let mask : Int32 := 2 * cutoff i - 1
    let v7 : Int32 := bor (bor (bshl (band i 2) 6) (bshl (bshr (val0 i) 7) (6 - i)))
      (band (diffv i) mask)
    (byteOf v6, byteOf v7)
  let fits (i : Int32) : Bool :=
    !(diffv i < -cutoff i || diffv i >= cutoff i)
  if fits 2 then enc 2
  else if fits 1 then enc 1
  else if fits 0 then enc 0
  else
    let v0 : Int32 := bshr (ia0 + 256) 9
    let v1 : Int32 := bshr (ia1 + 256) 9
    (byteOf v0 ||| 0x80, byteOf v1 ||| 0x80)

/-- `tc_cem11_qc`: quant_color round trip at colour quant `level`
  (identity at 256). -/
def hdrCem11Qc (level value : Nat) : Nat :=
  hdrColorRoundtrip level value

/-- `tc_cem11_retain`: walk the value down until the top bits survive the
  quantizer round trip (`value <= 0` also stops). -/
def hdrCem11Retain (level topmask : Nat) : Nat → Nat
  | 0 => hdrCem11Qc level 0
  | v + 1 =>
    let q := hdrCem11Qc level (v + 1)
    if ((v + 1) &&& topmask) == (q &&& topmask) then q
    else hdrCem11Retain level topmask v

/-- CEM 11 pack: two 3-channel LNS endpoint triples → 6 packed bytes
  (port of `tc_astc_cem11_pack`), general colour-quant level. -/
def cem11Pack (lns0 lns1 : List Nat) (level : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  let modeBits : List (Int32 × Int32 × Int32 × Int32) :=
    [(9, 7, 6, 7), (9, 8, 6, 6), (10, 6, 7, 7), (10, 7, 7, 6),
     (11, 8, 6, 5), (11, 6, 8, 6), (12, 7, 7, 5), (12, 6, 7, 6)]
  let modeCut : List (Int32 × Int32 × Int32 × Int32) :=
    [(16384, 8192, 8192, 8), (32768, 8192, 4096, 8), (4096, 8192, 4096, 4),
     (8192, 8192, 2048, 4), (8192, 2048, 512, 2), (2048, 8192, 1024, 2),
     (2048, 2048, 256, 1), (1024, 2048, 512, 1)]
  let modeScale : List Float32 :=
    [1.0 / 128, 1.0 / 128, 1.0 / 64, 1.0 / 64, 1.0 / 32, 1.0 / 32, 1.0 / 16, 1.0 / 16]
  let modeRscale : List Float32 := [128, 128, 64, 64, 32, 32, 16, 16]
  let clamp0 := fun (x : Nat) => fclamp (Float32.ofNat x) 0.0 65535.0
  let c0o : List Float32 := (List.range 3).map (fun i => clamp0 (lns0.getD i 0))
  let c1o : List Float32 := (List.range 3).map (fun i => clamp0 (lns1.getD i 0))
  let majcomp : Int32 :=
    if c1o.getD 0 0.0 > c1o.getD 1 0.0 && c1o.getD 0 0.0 > c1o.getD 2 0.0 then 0
    else if c1o.getD 1 0.0 > c1o.getD 2 0.0 then 1 else 2
  -- Swap the major component into slot 0 (C swaps 0↔1 or 0↔2).
  let (c0, c1) :=
    if majcomp == 0 then (c0o, c1o)
    else if majcomp == 1 then
      ([c0o.getD 1 0.0, c0o.getD 0 0.0, c0o.getD 2 0.0],
       [c1o.getD 1 0.0, c1o.getD 0 0.0, c1o.getD 2 0.0])
    else
      ([c0o.getD 2 0.0, c0o.getD 1 0.0, c0o.getD 0 0.0],
       [c1o.getD 2 0.0, c1o.getD 1 0.0, c1o.getD 0 0.0])
  let aBase : Float32 := c1.getD 0 0.0
  let b0b : Float32 := aBase - c1.getD 1 0.0
  let b1b : Float32 := aBase - c1.getD 2 0.0
  let cb : Float32 := aBase - c0.getD 0 0.0
  let d0b : Float32 := aBase - b0b - cb - c0.getD 1 0.0
  let d1b : Float32 := aBase - b1b - cb - c0.getD 2 0.0
  let absF (x : Float32) : Float32 := if x < 0.0 then -x else x
  let iabs (x : Int32) : Int32 := if x < 0 then -x else x
  let tryMode (mode : Int32) :
      Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
    let mBits : Int32 × Int32 × Int32 × Int32 := modeBits.getD mode.toNatClampNeg (0, 0, 0, 0)
    let mCut : Int32 × Int32 × Int32 × Int32 := modeCut.getD mode.toNatClampNeg (0, 0, 0, 0)
    let ms : Float32 := modeScale.getD mode.toNatClampNeg 0.0
    let mr : Float32 := modeRscale.getD mode.toNatClampNeg 0.0
    let bIc : Int32 := bshl 1 mBits.2.1
    let cIc : Int32 := bshl 1 mBits.2.2.1
    let dIc : Int32 := bshl 1 (mBits.2.2.2 - 1)
    if b0b > Float32.ofInt mCut.1.toInt || b1b > Float32.ofInt mCut.1.toInt ||
       cb > Float32.ofInt mCut.2.1.toInt ||
       absF d0b > Float32.ofInt mCut.2.2.1.toInt ||
       absF d1b > Float32.ofInt mCut.2.2.1.toInt then none
    else
      let aIv0 : Int32 := rtnF (aBase * ms)
      let aIv : Int32 :=
        (aIv0 &&& -256) ||| Int32.ofNat (hdrCem11Qc level
          (band aIv0 255).toUInt32.toNat)
      let aF : Float32 := Float32.ofInt aIv.toInt * mr
      let cF : Float32 := fclamp (aF - c0.getD 0 0.0) 0.0 65535.0
      let cIv : Int32 := rtnF (cF * ms)
      if cIv >= cIc then none
      else
        let cLo0 : Int32 := bor (bor (band cIv 0x3F) (bshl (band mode 1) 7))
          (bshr (band aIv 0x100) 2)
        let cLo : Int32 := Int32.ofInt
          (hdrCem11Retain level 0xC0 cLo0.toUInt32.toNat)
        let b0F : Float32 := fclamp (aF - c1.getD 1 0.0) 0.0 65535.0
        let b1F : Float32 := fclamp (aF - c1.getD 2 0.0) 0.0 65535.0
        let b0Iv : Int32 := rtnF (b0F * ms)
        let b1Iv : Int32 := rtnF (b1F * ms)
        if b0Iv >= bIc || b1Iv >= bIc then none
        else
          let bit0 : Int32 :=
            if mode == 2 || mode == 5 || mode == 7 then band (bshr aIv 9) 1
            else band (bshr b0Iv 6) 1
          let bit1 : Int32 :=
            if mode == 2 then band (bshr cIv 6) 1
            else if mode == 5 || mode == 7 then band (bshr aIv 10) 1
            else band (bshr b1Iv 6) 1
          let b0Lo0 : Int32 := bor (bor (band b0Iv 0x3F) (bshl bit0 6))
            (bshl (band (bshr mode 1) 1) 7)
          let b1Lo0 : Int32 := bor (bor (band b1Iv 0x3F) (bshl bit1 6))
            (bshl (band (bshr mode 2) 1) 7)
          let b0Lo : Int32 := Int32.ofInt
            (hdrCem11Retain level 0xC0 b0Lo0.toUInt32.toNat)
          let b1Lo : Int32 := Int32.ofInt
            (hdrCem11Retain level 0xC0 b1Lo0.toUInt32.toNat)
          -- C re-quantizes c_f / b0_f / b1_f from the packed low bits before
          -- deriving the d (residual) values, so mirror that here.
          let cIvQ : Int32 := bor (band cIv (-64)) (band cLo 0x3F)
          let cFQ : Float32 := Float32.ofInt cIvQ.toInt * mr
          let b0IvQ : Int32 := bor (band b0Iv (-64)) (band b0Lo 0x3F)
          let b1IvQ : Int32 := bor (band b1Iv (-64)) (band b1Lo 0x3F)
          let b0FQ : Float32 := Float32.ofInt b0IvQ.toInt * mr
          let b1FQ : Float32 := Float32.ofInt b1IvQ.toInt * mr
          let d0F : Float32 := fclamp (aF - b0FQ - cFQ - c0.getD 1 0.0) (-65535.0) 65535.0
          let d1F : Float32 := fclamp (aF - b1FQ - cFQ - c0.getD 2 0.0) (-65535.0) 65535.0
          let d0Iv : Int32 := rtnF (d0F * ms)
          let d1Iv : Int32 := rtnF (d1F * ms)
          if iabs d0Iv >= dIc || iabs d1Iv >= dIc then none
          else
            let bit2 : Int32 :=
              if mode == 0 || mode == 2 then band (bshr d0Iv 6) 1
              else if mode == 1 || mode == 4 then band (bshr b0Iv 7) 1
              else if mode == 3 then band (bshr aIv 9) 1
              else if mode == 5 then band (bshr cIv 7) 1
              else band (bshr aIv 11) 1
            let bit3 : Int32 :=
              if mode == 0 || mode == 2 then band (bshr d1Iv 6) 1
              else if mode == 1 || mode == 4 then band (bshr b1Iv 7) 1
              else band (bshr cIv 6) 1
            let bit4 : Int32 :=
              if mode == 4 || mode == 6 then band (bshr aIv 9) 1 else band (bshr d0Iv 5) 1
            let bit5 : Int32 :=
              if mode == 4 || mode == 6 then band (bshr aIv 10) 1 else band (bshr d1Iv 5) 1
            let d0Lo0 : Int32 := bor (bor (bor (band d0Iv 0x1F) (bshl bit2 6))
              (bshl bit4 5)) (bshl (band majcomp 1) 7)
            let d1Lo0 : Int32 := bor (bor (bor (band d1Iv 0x1F) (bshl bit3 6))
              (bshl bit5 5)) (bshl (band (bshr majcomp 1) 1) 7)
            let d0Lo : Int32 := Int32.ofInt
              (hdrCem11Retain level 0xF0 d0Lo0.toUInt32.toNat)
            let d1Lo : Int32 := Int32.ofInt
              (hdrCem11Retain level 0xF0 d1Lo0.toUInt32.toNat)
            some (byteOf aIv, byteOf cLo, byteOf b0Lo, byteOf b1Lo,
                  byteOf d0Lo, byteOf d1Lo)
  let rec search (n : Nat) : Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
    match tryMode (Int32.ofNat n) with
    | some v => some v
    | none => match n with
      | 0 => none
      | k + 1 => search k
  match search 7 with
  | some v => v
  | none =>
    let qcF := fun (l : Nat) =>
      hdrCem11Qc level (rtnF (fclamp (Float32.ofNat l) 0.0 65020.0 / 256.0)).toUInt32.toNat
    let qbF := fun (l : Nat) =>
      rtnF (fclamp (Float32.ofNat l) 0.0 65020.0 / 512.0) + 128
    let qc := fun (l : Nat) => byteOf (Int32.ofNat (qcF l))
    let qb := fun (l : Nat) =>
      byteOf (Int32.ofNat (hdrCem11Retain level 0xC0 ((qbF l).toUInt32.toNat)))
    (qc (lns0.getD 0 0), qc (lns1.getD 0 0),
     qc (lns0.getD 1 0), qc (lns1.getD 1 0),
     qb (lns0.getD 2 0), qb (lns1.getD 2 0))

/-- `(int)(x + 0.5f)`: truncating cast after a half-up bias (the CEM 7
  pack uses this rather than `tc_rtn`). -/
def rtnHalfUp (x : Float32) : Int32 :=
  Int32.ofInt (Tocio.truncToIntF (x + 0.5))

/-- CEM 7 pack: two 3-channel LNS endpoint triples → 4 packed bytes
  (port of `tc_astc_cem7_pack`), identity colour-quant path. -/
def cem7Pack (e0 e1 : List Nat) (level : Nat) :
    Nat × Nat × Nat × Nat :=
  let _ := level
  let modeBits : List (Int32 × Int32 × Int32) :=
    [(11, 5, 7), (11, 6, 5), (10, 5, 8), (9, 6, 7), (8, 7, 6)]
  let modeCut : List (Int32 × Int32) :=
    [(1024, 4096), (2048, 1024), (2048, 16384), (8192, 16384), (32768, 16384)]
  let modeRscale : List Float32 := [32.0, 32.0, 64.0, 128.0, 256.0]
  let modeScale : List Float32 := [1.0 / 32, 1.0 / 32, 1.0 / 64, 1.0 / 128, 1.0 / 256]
  -- s = mean(e1 - e0), clamped at 0; color[c] = (e1[c] - s) + s.
  -- C subtracts in `int` and then casts each difference to float.
  let diffF (c : Nat) : Float32 :=
    Float32.ofInt ((e1.getD c 0 : Int) - (e0.getD c 0 : Int))
  let s0 : Float32 := (diffF 0 + diffF 1) + diffF 2
  let s1 : Float32 := s0 * (1.0 / 3)
  let s : Float32 := if s1 < 0.0 then 0.0 else s1
  let raw : List Float32 :=
    [((Float32.ofNat (e1.getD 0 0) - s) + s),
     ((Float32.ofNat (e1.getD 1 0) - s) + s),
     ((Float32.ofNat (e1.getD 2 0) - s) + s)]
  let color0 : List Float32 :=
    (raw ++ [s]).map (fun x => fclamp x 0.0 65535.0)
  let bak : List Float32 := color0
  let majcomp : Int32 :=
    if color0.getD 0 0.0 > color0.getD 1 0.0 && color0.getD 0 0.0 > color0.getD 2 0.0 then 0
    else if color0.getD 1 0.0 > color0.getD 2 0.0 then 1 else 2
  let color : List Float32 :=
    if majcomp == 1 then [color0.getD 1 0.0, color0.getD 0 0.0, color0.getD 2 0.0, color0.getD 3 0.0]
    else if majcomp == 2 then [color0.getD 2 0.0, color0.getD 1 0.0, color0.getD 0 0.0, color0.getD 3 0.0]
    else color0
  let rBase : Float32 := color.getD 0 0.0
  let gBase : Float32 := color.getD 0 0.0 - color.getD 1 0.0
  let bBase : Float32 := color.getD 0 0.0 - color.getD 2 0.0
  let sBase : Float32 := color.getD 3 0.0
  let tryMode (mode : Int32) : Option (Nat × Nat × Nat × Nat) :=
    let mBits : Int32 × Int32 × Int32 := modeBits.getD mode.toNatClampNeg (0, 0, 0)
    let mCut : Int32 × Int32 := modeCut.getD mode.toNatClampNeg (0, 0)
    let ms : Float32 := modeScale.getD mode.toNatClampNeg 0.0
    let mr : Float32 := modeRscale.getD mode.toNatClampNeg 0.0
    if gBase > Float32.ofInt mCut.1.toInt || bBase > Float32.ofInt mCut.1.toInt ||
       sBase > Float32.ofInt mCut.2.toInt then none
    else
      let modeEnc : Int32 := if mode < 4 then bor mode (bshl majcomp 2) else bor majcomp 0xC
      let gbIc : Int32 := bshl 1 mBits.2.1
      let sIc : Int32 := bshl 1 mBits.2.2
      let rInt0 : Int32 := rtnHalfUp (rBase * ms)
      let rLow0 : Int32 := bor (band rInt0 0x3F) (bshl (band modeEnc 3) 6)
      let rLow : Int32 := Int32.ofInt
        (hdrCem11Retain level 0xC0 rLow0.toUInt32.toNat)
      let rInt : Int32 := bor (band rInt0 (-64)) (band rLow 0x3F)
      let rF : Float32 := Float32.ofInt rInt.toInt * mr
      let gF : Float32 := fclamp (rF - color.getD 1 0.0) 0.0 65535.0
      let bF : Float32 := fclamp (rF - color.getD 2 0.0) 0.0 65535.0
      let gInt : Int32 := rtnHalfUp (gF * ms)
      let bInt : Int32 := rtnHalfUp (bF * ms)
      if gInt >= gbIc || bInt >= gbIc then none
      else
        let bit0 : Int32 :=
          if mode == 0 || mode == 2 then band (bshr rInt 9) 1
          else if mode == 1 || mode == 3 then band (bshr rInt 8) 1
          else band (bshr gInt 6) 1
        let bit2 : Int32 :=
          if mode == 1 || mode == 2 || mode == 3 then band (bshr rInt 7) 1
          else if mode == 4 then band (bshr bInt 6) 1
          else 0
        let bit1 : Int32 :=
          if mode == 0 || mode == 2 then band (bshr rInt 8) 1
          else band (bshr gInt 5) 1
        let bit3 : Int32 :=
          if mode == 0 then band (bshr rInt 10) 1
          else if mode == 2 then band (bshr rInt 6) 1
          else band (bshr bInt 5) 1
        let gLow0 : Int32 := bor (bor (band gInt 0x1F) (bshl (band modeEnc 4) 5))
          (bor (bshl bit0 6) (bshl bit1 5))
        let bLow0 : Int32 := bor (bor (band bInt 0x1F) (bshl (band modeEnc 8) 4))
          (bor (bshl bit2 6) (bshl bit3 5))
        let gIntQ : Int32 := bor (band gInt (-32)) (band gLow0 0x1F)
        let bIntQ : Int32 := bor (band bInt (-32)) (band bLow0 0x1F)
        let gFq : Float32 := Float32.ofInt gIntQ.toInt * mr
        let bFq : Float32 := Float32.ofInt bIntQ.toInt * mr
        let rgbErr : Float32 :=
          (rF - color.getD 0 0.0) + (rF - gFq - color.getD 1 0.0) +
            (rF - bFq - color.getD 2 0.0)
        let sF0 : Float32 := sBase + rgbErr * (1.0 / 3)
        let sF : Float32 := if sF0 < 0.0 then 0.0 else if sF0 > 1e9 then 1e9 else sF0
        let sInt : Int32 := rtnHalfUp (sF * ms)
        if sInt >= sIc then none
        else
          let bit6 : Int32 := if mode == 1 then band (bshr rInt 9) 1 else band (bshr sInt 5) 1
          let bit5 : Int32 :=
            if mode == 4 then band (bshr rInt 7) 1
            else if mode == 1 then band (bshr rInt 10) 1
            else band (bshr sInt 6) 1
          let bit4 : Int32 := if mode == 2 then band (bshr sInt 7) 1 else band (bshr rInt 6) 1
          let sLow : Int32 := bor (bor (band sInt 0x1F) (bshl bit6 5))
            (bor (bshl bit5 6) (bshl bit4 7))
          some (byteOf rLow, byteOf gLow0, byteOf bLow0, byteOf sLow)
  -- C tries modes 0..4 in ascending order and takes the first fit.
  let rec search : Nat → Option (Nat × Nat × Nat × Nat)
    | 0 => tryMode 0
    | k + 1 =>
      match search k with
      | some v => some v
      | none => tryMode (Int32.ofNat (k + 1))
  match search 4 with
  | some v => v
  | none =>
    -- fallback: mode 5 (absolute, 9-bit), derived from the pre-swap colors.
    -- C clamps vals[c] to [0, 65020] and then measures the error against the
    -- clamped value (not the original bak value).
    let vals3 : List Float32 :=
      (List.range 3).map (fun c => fclamp (bak.getD c 0.0) 0.0 65020.0)
    let ivals : List Int32 :=
      vals3.map (fun v => rtnHalfUp (v * (1.0 / 512)))
    let cvals : List Float32 := ivals.map (fun i => Float32.ofInt i.toInt * 512.0)
    let rgbErr : Float32 :=
      (cvals.getD 0 0.0 - vals3.getD 0 0.0) + (cvals.getD 1 0.0 - vals3.getD 1 0.0) +
        (cvals.getD 2 0.0 - vals3.getD 2 0.0)
    let sV0 : Float32 := bak.getD 3 0.0 + rgbErr * (1.0 / 3)
    let sV : Float32 := fclamp sV0 0.0 65020.0
    let sIv : Int32 := rtnHalfUp (sV * (1.0 / 512))
    let enc0 : Int32 := bor (band (ivals.getD 0 0) 0x3F) 0xC0
    let enc1 : Int32 := bor (band (ivals.getD 1 0) 0x7F) 0x80
    let enc2 : Int32 := bor (band (ivals.getD 2 0) 0x7F) 0x80
    let enc3 : Int32 := bor (band sIv 0x7F) (bshl (band (ivals.getD 0 0) 0x40) 1)
    (byteOf enc0, byteOf enc1, byteOf enc2, byteOf enc3)

/-- `tc_sclamp`. -/
def sclamp32 (v lo hi : Int32) : Int32 :=
  if v < lo then lo else if v > hi then hi else v

/-- `tc_astc_cem11_unpack` (encoder domain; the decoder-side
  `Texcomp.cem11Unpack` has the ISE scramble folded in): 6 packed bytes →
  two 3-channel 16-bit LNS endpoint triples. -/
def hdrEncCem11Unpack (vv : List Nat) : List Int × List Int :=
  let v0 : Int32 := Int32.ofNat (vv.getD 0 0)
  let v1 : Int32 := Int32.ofNat (vv.getD 1 0)
  let v2 : Int32 := Int32.ofNat (vv.getD 2 0)
  let v3 : Int32 := Int32.ofNat (vv.getD 3 0)
  let v4 : Int32 := Int32.ofNat (vv.getD 4 0)
  let v5 : Int32 := Int32.ofNat (vv.getD 5 0)
  let modeval : Int32 :=
    bor (bor (band (bshr v1 7) 1) (bshl (band (bshr v2 7) 1) 1))
      (bshl (band (bshr v3 7) 1) 2)
  let majcomp : Int32 :=
    bor (band (bshr v4 7) 1) (bshl (band (bshr v5 7) 1) 1)
  if majcomp == 3 then
    ([v0.toInt * 256, v2.toInt * 256, (band v4 0x7F).toInt * 512],
     [v1.toInt * 256, v3.toInt * 256, (band v5 0x7F).toInt * 512])
  else
    let a0 : Int32 := bor v0 (bshl (band v1 0x40) 2)
    let b00 : Int32 := band v2 0x3F
    let b10 : Int32 := band v3 0x3F
    let c0 : Int32 := band v1 0x3F
    let d00 : Int32 := band v4 0x7F
    let d10 : Int32 := band v5 0x7F
    let dbitsArr : List Int32 := [7, 6, 7, 6, 5, 6, 5, 6]
    let dbits : Int32 := dbitsArr.getD modeval.toNatClampNeg 0
    let bit0 : Int32 := band (bshr v2 6) 1
    let bit1 : Int32 := band (bshr v3 6) 1
    let bit2 : Int32 := band (bshr v4 6) 1
    let bit3 : Int32 := band (bshr v5 6) 1
    let bit4 : Int32 := band (bshr v4 5) 1
    let bit5 : Int32 := band (bshr v5 5) 1
    let ohmod : Int32 := bshl 1 modeval
    let a : Int32 :=
      (if ohmod &&& 0xA4 != 0 then bor a0 (bshl bit0 9) else a0) |>
      (fun x => if ohmod &&& 0x8 != 0 then bor x (bshl bit2 9) else x) |>
      (fun x => if ohmod &&& 0x50 != 0 then bor x (bshl bit4 9) else x) |>
      (fun x => if ohmod &&& 0x50 != 0 then bor x (bshl bit5 10) else x) |>
      (fun x => if ohmod &&& 0xA0 != 0 then bor x (bshl bit1 10) else x) |>
      (fun x => if ohmod &&& 0xC0 != 0 then bor x (bshl bit2 11) else x)
    let c : Int32 :=
      (if ohmod &&& 0x4 != 0 then bor c0 (bshl bit1 6) else c0) |>
      (fun x => if ohmod &&& 0xE8 != 0 then bor x (bshl bit3 6) else x) |>
      (fun x => if ohmod &&& 0x20 != 0 then bor x (bshl bit2 7) else x)
    let (b0, b1) : Int32 × Int32 :=
      ((if ohmod &&& 0x5B != 0 then bor b00 (bshl bit0 6) else b00),
       (if ohmod &&& 0x5B != 0 then bor b10 (bshl bit1 6) else b10)) |>
      (fun (x, y) =>
        ((if ohmod &&& 0x12 != 0 then bor x (bshl bit2 7) else x),
         (if ohmod &&& 0x12 != 0 then bor y (bshl bit3 7) else y)))
    let (d0, d1) : Int32 × Int32 :=
      ((if ohmod &&& 0xAF != 0 then bor d00 (bshl bit4 5) else d00),
       (if ohmod &&& 0xAF != 0 then bor d10 (bshl bit5 5) else d10)) |>
      (fun (x, y) =>
        ((if ohmod &&& 0x5 != 0 then bor x (bshl bit2 6) else x),
         (if ohmod &&& 0x5 != 0 then bor y (bshl bit3 6) else y)))
    -- sign-extend d0/d1 from dbits, then scale everything to 12-bit domain
    let sh : Int32 := 32 - dbits
    let sx (x : Int32) : Int32 := bshr (bshl x sh) sh
    let d0s : Int32 := sx d0
    let d1s : Int32 := sx d1
    let valsh : Int32 := 3 - (bshr modeval 1)
    let sc : Int32 := bshl 1 valsh
    let aS : Int32 := a * sc
    let b0S : Int32 := b0 * sc
    let b1S : Int32 := b1 * sc
    let cS : Int32 := c * sc
    let d0S : Int32 := d0s * sc
    let d1S : Int32 := d1s * sc
    let r1 : Int32 := sclamp32 aS 0 4095
    let g1 : Int32 := sclamp32 (aS - b0S) 0 4095
    let bl1 : Int32 := sclamp32 (aS - b1S) 0 4095
    let r0 : Int32 := sclamp32 (aS - cS) 0 4095
    let g0 : Int32 := sclamp32 (aS - b0S - cS - d0S) 0 4095
    let bl0 : Int32 := sclamp32 (aS - b1S - cS - d1S) 0 4095
    let (r0, g0, bl0, r1, g1, bl1) : Int32 × Int32 × Int32 × Int32 × Int32 × Int32 :=
      if majcomp == 1 then (g0, r0, bl0, g1, r1, bl1)
      else if majcomp == 2 then (bl0, g0, r0, bl1, g1, r1)
      else (r0, g0, bl0, r1, g1, bl1)
    let shl4 : Int32 → Int := fun x => (bshl x 4).toInt
    ([shl4 r0, shl4 g0, shl4 bl0], [shl4 r1, shl4 g1, shl4 bl1])

/-- `tc_astc_hdr_alpha_unpack` (encoder domain): 2 packed bytes → two
  16-bit LNS alphas. -/
def hdrEncAlphaUnpack (inb : List Nat) : Int × Int :=
  let v60 : Int32 := Int32.ofNat (inb.getD 0 0)
  let v70 : Int32 := Int32.ofNat (inb.getD 1 0)
  let modeval : Int32 :=
    bor (band (bshr v60 7) 1) (band (bshr v70 6) 2)
  let v6 : Int32 := band v60 0x7F
  let v7 : Int32 := band v70 0x7F
  if modeval == 3 then
    ((bshl v6 5).toInt * 16, (bshl v7 5).toInt * 16)
  else
    let v6a : Int32 := bor v6 (band (bshl v7 (modeval + 1)) 0x780)
    let v7a : Int32 := band v7 (bshr 0x3F modeval)
    let v7b : Int32 := v7a ^^^ (bshr 32 modeval)
    let v7c : Int32 := v7b - (bshr 32 modeval)
    let v6d : Int32 := bshl v6a (4 - modeval)
    -- signed left shift via unsigned to stay UB-free (v7 may be negative)
    let v7d : Int32 := bshl v7c (4 - modeval)
    let v7e : Int32 := sclamp32 (v6d + v7d) 0 0xFFF
    ((bshl v6d 4).toInt, (bshl v7e 4).toInt)

/-- `tc_astc_cem15_unpack`: CEM 11 RGB + HDR alpha. -/
def hdrEncCem15Unpack (v : List Nat) : List Int × List Int :=
  let (rgb0, rgb1) := hdrEncCem11Unpack v
  let (a0, a1) := hdrEncAlphaUnpack (v.drop 6)
  (rgb0 ++ [a0], rgb1 ++ [a1])

/-- `tc_astc_cem15_pack`: CEM 11 RGB pack + HDR alpha pack. -/
def hdrEncCem15Pack (lns0 lns1 : List Nat) (alns0 alns1 : Int) (level : Nat) :
    List Nat :=
  let (a, b, c, d, e, f) := cem11Pack lns0 lns1 level
  let (g, h) := hdrAlphaPack alns0 alns1
  [a, b, c, d, e, f, g, h]

/-- `tc_astc_cem7_unpack` (encoder domain): 4 packed bytes → two
  3-channel 16-bit LNS endpoint triples (hdr_rgbo). -/
def hdrEncCem7Unpack (vv : List Nat) : List Int × List Int :=
  let shamts : List Int32 := [1, 1, 2, 3, 4, 5]
  let v0 : Int32 := Int32.ofNat (vv.getD 0 0)
  let v1 : Int32 := Int32.ofNat (vv.getD 1 0)
  let v2 : Int32 := Int32.ofNat (vv.getD 2 0)
  let v3 : Int32 := Int32.ofNat (vv.getD 3 0)
  let modeval : Int32 :=
    bor (bor (band (bshr v0 6) 3) (bshl (band (bshr v1 7) 1) 2))
      (bshl (band (bshr v2 7) 1) 3)
  let (majcomp, mode) : Int32 × Int32 :=
    if (modeval &&& 0xC) != 0xC then (bshr modeval 2, band modeval 3)
    else if modeval != 0xF then (band modeval 3, 4)
    else (0, 5)
  let red0 : Int32 := band v0 0x3F
  let green0 : Int32 := band v1 0x1F
  let blue0 : Int32 := band v2 0x1F
  let scale0 : Int32 := band v3 0x1F
  let bit0 : Int32 := band (bshr v1 6) 1
  let bit1 : Int32 := band (bshr v1 5) 1
  let bit2 : Int32 := band (bshr v2 6) 1
  let bit3 : Int32 := band (bshr v2 5) 1
  let bit4 : Int32 := band (bshr v3 7) 1
  let bit5 : Int32 := band (bshr v3 6) 1
  let bit6 : Int32 := band (bshr v3 5) 1
  let oh : Int32 := bshl 1 mode
  let greenA : Int32 :=
    (if oh &&& 0x30 != 0 then bor green0 (bshl bit0 6) else green0) |>
    (fun x => if oh &&& 0x3A != 0 then bor x (bshl bit1 5) else x)
  let blueA : Int32 :=
    (if oh &&& 0x30 != 0 then bor blue0 (bshl bit2 6) else blue0) |>
    (fun x => if oh &&& 0x3A != 0 then bor x (bshl bit3 5) else x)
  let scaleA : Int32 :=
    (if oh &&& 0x3D != 0 then bor scale0 (bshl bit6 5) else scale0) |>
    (fun x => if oh &&& 0x2D != 0 then bor x (bshl bit5 6) else x) |>
    (fun x => if oh &&& 0x4 != 0 then bor x (bshl bit4 7) else x)
  let redA : Int32 :=
    (if oh &&& 0x3B != 0 then bor red0 (bshl bit4 6) else red0) |>
    (fun x => if oh &&& 0x4 != 0 then bor x (bshl bit3 6) else x) |>
    (fun x => if oh &&& 0x10 != 0 then bor x (bshl bit5 7) else x) |>
    (fun x => if oh &&& 0x0F != 0 then bor x (bshl bit2 7) else x) |>
    (fun x => if oh &&& 0x05 != 0 then bor x (bshl bit1 8) else x) |>
    (fun x => if oh &&& 0x0A != 0 then bor x (bshl bit0 8) else x) |>
    (fun x => if oh &&& 0x05 != 0 then bor x (bshl bit0 9) else x) |>
    (fun x => if oh &&& 0x02 != 0 then bor x (bshl bit6 9) else x) |>
    (fun x => if oh &&& 0x01 != 0 then bor x (bshl bit3 10) else x) |>
    (fun x => if oh &&& 0x02 != 0 then bor x (bshl bit5 10) else x)
  let sh : Int32 := shamts.getD mode.toNatClampNeg 0
  let redB : Int32 := bshl redA sh
  let greenB : Int32 := bshl greenA sh
  let blueB : Int32 := bshl blueA sh
  let scaleB : Int32 := bshl scaleA sh
  let redC : Int32 := if mode != 5 then redB else redB
  let greenC : Int32 := if mode != 5 then redB - greenB else greenB
  let blueC : Int32 := if mode != 5 then redB - blueB else blueB
  let (red, green, blue) : Int32 × Int32 × Int32 :=
    if majcomp == 1 then (greenC, redC, blueC)
    else if majcomp == 2 then (blueC, greenC, redC)
    else (redC, greenC, blueC)
  let cl : Int32 → Int32 := fun x => if x < 0 then 0 else x
  let r0 : Int32 := cl (red - scaleB)
  let g0 : Int32 := cl (green - scaleB)
  let b0 : Int32 := cl (blue - scaleB)
  let shl4 : Int32 → Int := fun x => (bshl x 4).toInt
  ([shl4 r0, shl4 g0, shl4 b0],
   [shl4 (cl red), shl4 (cl green), shl4 (cl blue)])

/-- `tc_astc_hdr_write_void_extent`: FP16 RGBA constant block. -/
def hdrWriteVoidExtent (r g b a : Nat) : List Nat :=
  [0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   r &&& 0xFF, r >>> 8, g &&& 0xFF, g >>> 8,
   b &&& 0xFF, b >>> 8, a &&& 0xFF, a >>> 8]

end Texcomp
