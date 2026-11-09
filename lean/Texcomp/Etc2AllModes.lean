/-
  TinyEXR - Lean 4 formalization of the ETC2/EAC decoders.

  Faithful ports of `tc_decode_etc2_rgb_block`, `tc_decode_eac_a8_block`
  and `tc_decode_eac_r11_block` in `tools/texcomp/src/texcomp_etc2_decode.c`
  (OpenGL ES 3.0 spec): all five RGB modes (individual, differential, T, H,
  planar), EAC alpha (8-bit) and EAC R11 (11-bit, standard unorm output).

  Texels are column-major in the block (texel i at x = i/4, y = i%4);
  output is row-major (y*4+x), matching the C decoders.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- Intensity modifier table `[codeword][selector]`. -/
def etcMod : List (List Int) :=
  [[2, 8, -2, -8], [5, 17, -5, -17], [9, 29, -9, -29],
   [13, 42, -13, -42], [18, 60, -18, -60], [24, 80, -24, -80],
   [33, 106, -33, -106], [47, 183, -47, -183]]

/-- T/H-mode distance table. -/
def etcDist : List Int := [3, 6, 11, 16, 23, 32, 41, 64]

/-- EAC modifier table `[table][selector]`. -/
def eacMod : List (List Int) :=
  [[-3,-6,-9,-15,2,5,8,14], [-3,-7,-10,-13,2,6,9,12],
   [-2,-5,-8,-13,1,4,7,12], [-2,-4,-6,-13,1,3,5,12],
   [-3,-6,-8,-12,2,5,7,11], [-3,-7,-9,-11,2,6,8,10],
   [-4,-7,-8,-11,3,6,7,10], [-3,-5,-8,-11,2,4,7,10],
   [-2,-6,-8,-10,1,5,7,9],  [-2,-5,-8,-10,1,4,7,9],
   [-2,-4,-8,-10,1,3,7,9],  [-2,-5,-7,-10,1,4,6,9],
   [-3,-4,-7,-10,2,3,6,9],  [-1,-2,-3,-10,0,1,2,9],
   [-4,-6,-8,-9,3,5,7,8],   [-3,-5,-7,-9,2,4,6,8]]

/-- Clamp to 0..255. -/
def clamp255E (v : Int) : Nat :=
  if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- Bit-replication extensions. -/
def ext4 (v : Nat) : Nat := (v <<< 4) ||| v
def ext5 (v : Nat) : Nat := (v <<< 3) ||| (v >>> 2)
def ext6 (v : Nat) : Nat := (v <<< 2) ||| (v >>> 4)
def ext7 (v : Nat) : Nat := (v <<< 1) ||| (v >>> 6)

/-- Sign-extend a 3-bit two's-complement field. -/
def s3 (v : Nat) : Int :=
  if (v &&& 4) != 0 then Int.ofNat v - 8 else Int.ofNat v

/-- 2-bit selector for column-major texel index `i` (caller passes `x*4+y`). -/
def byteAt (bytes : Fin 8 → UInt8) (i : Nat) : UInt8 :=
  bytes ⟨i % 8, Nat.mod_lt i (by decide)⟩

/-- 2-bit selector for column-major texel (x, y) as index. -/
def etcSel (bytes : Fin 8 → UInt8) (i : Nat) : Nat :=
  let lsb := ((byteAt bytes (7 - (i >>> 3))).toNat >>> (i &&& 7)) &&& 1
  let msb := ((byteAt bytes (5 - (i >>> 3))).toNat >>> (i &&& 7)) &&& 1
  (msb <<< 1) ||| lsb

/-- 3-bit EAC selector from the big-endian 48-bit field. -/
def eacSel (bytes : Fin 8 → UInt8) (i : Nat) : Nat :=
  let bit := 45 - 3 * i
  let w := ((byteAt bytes 2).toNat <<< 40) ||| ((byteAt bytes 3).toNat <<< 32) |||
           ((byteAt bytes 4).toNat <<< 24) ||| ((byteAt bytes 5).toNat <<< 16) |||
           ((byteAt bytes 6).toNat <<< 8) ||| (byteAt bytes 7).toNat
  (w >>> bit) &&& 7

/-- ETC2 RGB block (8 bytes) → 16 row-major RGBA8 texels. -/
def etc2RgbDecode (bytes : Fin 8 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let x := texel.val % 4
    let y := texel.val / 4
    let flip := (bytes 3).toNat &&& 1
    let differential := ((bytes 3).toNat >>> 1) &&& 1
    let r5 := ((bytes 0).toNat >>> 3)
    let dr := s3 ((bytes 0).toNat &&& 7)
    let g5 := ((bytes 1).toNat >>> 3)
    let dg := s3 ((bytes 1).toNat &&& 7)
    let b5 := ((bytes 2).toNat >>> 3)
    let db := s3 ((bytes 2).toNat &&& 7)
    let r := Int.ofNat r5
    let g := Int.ofNat g5
    let bl := Int.ofNat b5
    let base := fun k => match k with | 0 => r | 1 => g | _ => bl
    if differential != 0 && (r + dr < 0 || r + dr > 31) then
      -- T mode
      let r1 := (((bytes 0).toNat >>> 1) &&& 0xC) ||| ((bytes 0).toNat &&& 3)
      let c0 := [ext4 r1, ext4 ((bytes 1).toNat >>> 4), ext4 ((bytes 1).toNat &&& 0xF)]
      let c1 := [ext4 ((bytes 2).toNat >>> 4), ext4 ((bytes 2).toNat &&& 0xF),
                 ext4 ((bytes 3).toNat >>> 4)]
      let d := (((bytes 3).toNat >>> 1) &&& 6) ||| ((bytes 3).toNat &&& 1)
      let dist := etcDist.getD d 0
      let s := etcSel bytes (x * 4 + y)
      let pal := fun k => match s with
        | 0 => c0.getD k 0
        | 1 => clamp255E (Int.ofNat (c1.getD k 0) + dist)
        | 2 => c1.getD k 0
        | _ => clamp255E (Int.ofNat (c1.getD k 0) - dist)
      (UInt8.ofNat (pal 0), UInt8.ofNat (pal 1), UInt8.ofNat (pal 2), 255)
    else if differential != 0 && (g + dg < 0 || g + dg > 31) then
      -- H mode
      let r0 := ((bytes 0).toNat >>> 3) &&& 0xF
      let g0 := (((bytes 0).toNat &&& 7) <<< 1) ||| (((bytes 1).toNat >>> 4) &&& 1)
      let b0v := ((bytes 1).toNat &&& 8) ||| (((bytes 1).toNat &&& 3) <<< 1) |||
                 (((bytes 2).toNat >>> 7) &&& 1)
      let r1 := ((bytes 2).toNat >>> 3) &&& 0xF
      let g1 := (((bytes 2).toNat &&& 7) <<< 1) ||| ((bytes 3).toNat >>> 7)
      let b1v := ((bytes 3).toNat >>> 3) &&& 0xF
      let c0 := [ext4 r0, ext4 g0, ext4 b0v]
      let c1 := [ext4 r1, ext4 g1, ext4 b1v]
      let packed := fun c => (c.getD 0 0 <<< 16) ||| (c.getD 1 0 <<< 8) ||| (c.getD 2 0)
      let d0 := (((bytes 3).toNat &&& 4) ||| (((bytes 3).toNat &&& 1) <<< 1))
      let d := if packed c0 >= packed c1 then d0 ||| 1 else d0
      let dist := etcDist.getD d 0
      let s := etcSel bytes (x * 4 + y)
      let pal := fun k => match s with
        | 0 => clamp255E (Int.ofNat (c0.getD k 0) + dist)
        | 1 => clamp255E (Int.ofNat (c0.getD k 0) - dist)
        | 2 => clamp255E (Int.ofNat (c1.getD k 0) + dist)
        | _ => clamp255E (Int.ofNat (c1.getD k 0) - dist)
      (UInt8.ofNat (pal 0), UInt8.ofNat (pal 1), UInt8.ofNat (pal 2), 255)
    else if differential != 0 && (bl + db < 0 || bl + db > 31) then
      -- Planar mode
      let ro := ((bytes 0).toNat >>> 1) &&& 0x3F
      let go := (((bytes 0).toNat &&& 1) <<< 6) ||| (((bytes 1).toNat >>> 1) &&& 0x3F)
      let bo := (((bytes 1).toNat &&& 1) <<< 5) ||| ((bytes 2).toNat &&& 0x18) |||
                (((bytes 2).toNat &&& 3) <<< 1) ||| (((bytes 3).toNat >>> 7) &&& 1)
      let rh := (((bytes 3).toNat >>> 1) &&& 0x3E) ||| ((bytes 3).toNat &&& 1)
      let gh := (bytes 4).toNat >>> 1
      let bh := (((bytes 4).toNat &&& 1) <<< 5) ||| ((bytes 5).toNat >>> 3)
      let rv := (((bytes 5).toNat &&& 7) <<< 3) ||| ((bytes 6).toNat >>> 5)
      let gv := (((bytes 6).toNat &&& 0x1F) <<< 2) ||| ((bytes 7).toNat >>> 6)
      let bv := (bytes 7).toNat &&& 0x3F
      let r0 := Int.ofNat (ext6 ro)
      let g0 := Int.ofNat (ext7 go)
      let b0 := Int.ofNat (ext6 bo)
      let r1 := Int.ofNat (ext6 rh)
      let g1 := Int.ofNat (ext7 gh)
      let b1 := Int.ofNat (ext6 bh)
      let r2 := Int.ofNat (ext6 rv)
      let g2 := Int.ofNat (ext7 gv)
      let b2 := Int.ofNat (ext6 bv)
      let den := fun a0 a1 a2 =>
        clamp255E ((Int.ofNat x * (a1 - a0) + Int.ofNat y * (a2 - a0) + 4 * a0 + 2) / 4)
      (UInt8.ofNat (den r0 r1 r2), UInt8.ofNat (den g0 g1 g2), UInt8.ofNat (den b0 b1 b2), 255)
    else
      -- Individual / differential
      -- differential: 5-bit bases (r, r+dr); individual: 4-bit nibbles
      let base0 : List Nat := if differential != 0 then
        [ext5 r5, ext5 g5, ext5 b5]
        else
        [ext4 ((bytes 0).toNat >>> 4), ext4 ((bytes 1).toNat >>> 4), ext4 ((bytes 2).toNat >>> 4)]
      let base1 : List Nat := if differential != 0 then
        [ext5 (Int.toNat (r + dr)), ext5 (Int.toNat (g + dg)), ext5 (Int.toNat (bl + db))]
        else
        [ext4 ((bytes 0).toNat &&& 0xF), ext4 ((bytes 1).toNat &&& 0xF),
         ext4 ((bytes 2).toNat &&& 0xF)]
      let cw0 := ((bytes 3).toNat >>> 5) &&& 7
      let cw1 := ((bytes 3).toNat >>> 2) &&& 7
      let sub := if flip != 0 then y >>> 1 else x >>> 1
      let s := etcSel bytes (x * 4 + y)
      let row := etcMod.getD (if sub == 0 then cw0 else cw1) []
      let m := row.getD s 0
      let base := if sub == 0 then base0 else base1
      (UInt8.ofNat (clamp255E (Int.ofNat (base.getD 0 0) + m)),
       UInt8.ofNat (clamp255E (Int.ofNat (base.getD 1 0) + m)),
       UInt8.ofNat (clamp255E (Int.ofNat (base.getD 2 0) + m)), 255)

/-- EAC alpha (8-bit) block. -/
def eacAlphaDecode (bytes : Fin 8 → UInt8) : Fin 16 → UInt8 :=
  fun texel =>
    let x := texel.val % 4
    let y := texel.val / 4
    let base := Int.ofNat (bytes 0).toNat
    let mul := Int.ofNat ((bytes 1).toNat >>> 4)
    let tab := (bytes 1).toNat &&& 0xF
    let m := let tabRow := eacMod.getD tab []
    tabRow.getD (eacSel bytes (x * 4 + y)) 0
    UInt8.ofNat (clamp255E (base + m * mul))

/-- EAC R11 block, standard unorm output. -/
def eacR11Decode (bytes : Fin 8 → UInt8) : Fin 16 → UInt8 :=
  fun texel =>
    let x := texel.val % 4
    let y := texel.val / 4
    let base := Int.ofNat (bytes 0).toNat * 8 + 4
    let mul := Int.ofNat ((bytes 1).toNat >>> 4)
    let tab := (bytes 1).toNat &&& 0xF
    let m := let tabRow := eacMod.getD tab []
    tabRow.getD (eacSel bytes (x * 4 + y)) 0
    let r11 := if mul == 0 then base + m else base + m * mul * 8
    let clamped := if r11 < 0 then 0 else if r11 > 2047 then 2047 else r11
    UInt8.ofNat (((clamped.toNat * 255 + 1023) / 2047))

/-- ETC2 RGBA (16 bytes): EAC alpha + RGB. -/
def etc2RgbaDecode (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let alphaBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val, by omega⟩
    let rgbBlock : Fin 8 → UInt8 := fun i => bytes ⟨i.val + 8, by omega⟩
    let (r, g, b, _) := etc2RgbDecode rgbBlock texel
    (r, g, b, eacAlphaDecode alphaBlock texel)

/-- Totality by construction. -/
theorem etc2RgbDecode_total (_bytes : Fin 8 → UInt8) (_texel : Fin 16) : True :=
  trivial

/-- Modifier tables have the spec sizes. -/
theorem etcMod_count : etcMod.length = 8 := by native_decide
theorem eacMod_count : eacMod.length = 16 := by native_decide
theorem etcDist_count : etcDist.length = 8 := by native_decide

end Texcomp
