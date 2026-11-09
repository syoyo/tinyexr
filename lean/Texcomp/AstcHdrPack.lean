/-
  TinyEXR - Lean 4 formalization of the ASTC HDR endpoint packers
  (encoder side).

  Ports `tc_astc_cem11_pack`, `tc_astc_cem7_pack` and
  `tc_astc_hdr_alpha_pack` in `tools/texcomp/src/texcomp_astc_hdr.c`.
  The packers quantize endpoints through
  `tc_astc_hdr_color_roundtrip` (colour quant level); the block
  encoders always pass level 20, where that round trip is the identity,
  so these ports model the identity path (the sub-256 colour-roundtrip
  LUT is the documented boundary). Integer kernels use `Int32` (C
  `int`), floats use `Float32` with the C evaluation order and `rtn`
  (round half away from zero).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Math

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

/-- CEM 11 pack: two 3-channel LNS endpoint triples → 6 packed bytes
  (port of `tc_astc_cem11_pack`), identity colour-quant path. -/
def cem11Pack (lns0 lns1 : List Nat) (level : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  let _ := level
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
      let aIv : Int32 := rtnF (aBase * ms)
      let aF : Float32 := Float32.ofInt aIv.toInt * mr
      let cF : Float32 := fclamp (aF - c0.getD 0 0.0) 0.0 65535.0
      let cIv : Int32 := rtnF (cF * ms)
      if cIv >= cIc then none
      else
        let cLo : Int32 := bor (bor (band cIv 0x3F) (bshl (band mode 1) 7))
          (bshr (band aIv 0x100) 2)
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
          let b0Lo : Int32 := bor (bor (band b0Iv 0x3F) (bshl bit0 6))
            (bshl (band (bshr mode 1) 1) 7)
          let b1Lo : Int32 := bor (bor (band b1Iv 0x3F) (bshl bit1 6))
            (bshl (band (bshr mode 2) 1) 7)
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
            let d0Lo : Int32 := bor (bor (bor (band d0Iv 0x1F) (bshl bit2 6)) (bshl bit4 5))
              (bshl (band majcomp 1) 7)
            let d1Lo : Int32 := bor (bor (bor (band d1Iv 0x1F) (bshl bit3 6)) (bshl bit5 5))
              (bshl (band (bshr majcomp 1) 1) 7)
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
    let qc := fun (l : Nat) => rtnF (fclamp (Float32.ofNat l) 0.0 65020.0 / 256.0)
    let qb := fun (l : Nat) => rtnF (fclamp (Float32.ofNat l) 0.0 65020.0 / 512.0)
    (byteOf (qc (lns0.getD 0 0)), byteOf (qc (lns1.getD 0 0)),
     byteOf (qc (lns0.getD 1 0)), byteOf (qc (lns1.getD 1 0)),
     byteOf (qb (lns0.getD 2 0) + 128), byteOf (qb (lns1.getD 2 0) + 128))

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
      let rLow : Int32 := bor (band rInt0 0x3F) (bshl (band modeEnc 3) 6)
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

end Texcomp
