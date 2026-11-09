/-
  TinyEXR - Lean 4 formalization of the BC6H encoder's kernel layer.

  Ports the deterministic primitives every BC6H mode packer builds on
  (`tools/texcomp/src/texcomp_bc6h.c`):

  * `tc_float_to_half_bits` (bit-exact half rounding, modelled on the raw
    `uint32` pattern),
  * the magnitude/sign-magnitude quantisers and dequantisers
    (`tc_bc6h_quant_{u,s}f16`, `..._n`, `tc_bc6h_unquant_*`),
  * the 3-channel squared-error kernels (`tc_bc6h_err3_mag`,
    `tc_bc6h_err3_smag`),
  * `tc_bc6h_pack_signed_n` / `tc_bc6h_pack_signed10`,
  * the 16-entry palette builder and selector choice
    (`tc_bc6h_pal16_uf16`, `tc_bc6h_choose_selectors_uf16_scalar`), and
  * `tc_bc6h_rdiv` (the least-squares rounding division).

  The per-mode endpoint search and block layout are the remaining
  boundary; this module is the arithmetic core they share.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Encode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_float_to_half_bits`, applied to the raw float bit pattern. -/
def bc6hFloatToHalfBits (u : UInt32) : Nat :=
  let sign : Nat := (u.toNat >>> 16) &&& 0x8000
  let exp0 : Nat := (u.toNat >>> 23) &&& 0xFF
  let mant0 : Nat := u.toNat &&& 0x7FFFFF
  if exp0 == 255 then sign ||| 0x7C00 ||| (if mant0 != 0 then 0x200 else 0)
  else if exp0 > 142 then sign ||| 0x7C00
  else if exp0 < 113 then
    (if exp0 < 103 then sign
     else
       let m := ((mant0 ||| 0x800000) >>> (125 - exp0))
       sign ||| (((m + 0x1000) >>> 13) &&& 0x7FFF))
  else
    let exp1 := exp0 - 112
    let mant1 := (mant0 + 0x1000) >>> 13
    let (mant2, exp2) := if mant1 &&& 0x400 != 0 then (0, exp1 + 1) else (mant1, exp1)
    if exp2 ≥ 31 then sign ||| 0x7C00
    else sign ||| (exp2 <<< 10) ||| (mant2 &&& 0x3FF)

/-- IEEE `f > 0` computed from the bit pattern (NaN compares false). -/
def bc6hBitsGt0 (u : UInt32) : Bool :=
  let b := u.toNat
  (b >>> 31) == 0 && ((b >>> 23) &&& 0xFF) != 0xFF && (b &&& 0x7FFFFFFF) != 0

/-- IEEE `f == 0` computed from the bit pattern (`-0.0 == 0.0`). -/
def bc6hBitsEq0 (u : UInt32) : Bool := (u.toNat &&& 0x7FFFFFFF) == 0

/-- `tc_bc6h_quant_uf16`: float bits → 10-bit unsigned magnitude. -/
def bc6hQuantUf16 (u : UInt32) : Nat :=
  if !bc6hBitsGt0 u then 0
  else
    let mag := (bc6hFloatToHalfBits u) &&& 0x7FFF
    let mag := if mag > 0x7BFF then 0x7BFF else mag
    (mag * 1023 + 15871) / 31743

/-- `tc_bc6h_quant_sf16`: float bits → signed 10-bit magnitude. -/
def bc6hQuantSf16 (u : UInt32) : Int :=
  if bc6hBitsEq0 u then 0
  else
    let h := bc6hFloatToHalfBits u
    let mag := if (h &&& 0x7FFF) > 0x7BFF then 0x7BFF else h &&& 0x7FFF
    let q : Int := Int.ofNat ((mag * 511 + 15871) / 31743)
    let q := if q > 511 then 511 else q
    if h &&& 0x8000 != 0 then -q else q

/-- `tc_bc6h_unquant_uf16_to_mag`: 10-bit magnitude → 15-bit magnitude. -/
def bc6hUnquantUf16ToMag (q : Nat) : Nat :=
  let unq := if q == 0 then 0 else if q ≥ 1023 then 0xFFFF
             else ((q <<< 16) + 0x8000) >>> 10
  (unq * 31) >>> 6

/-- `tc_bc6h_unquant_sf16_to_smag`: signed 10-bit → signed magnitude. -/
def bc6hUnquantSf16ToSmag (q0 : Int) : Int :=
  let (sign, q) := if q0 < 0 then (-1, -q0) else (1, q0)
  let unq : Int :=
    if q == 0 then 0
    else if q ≥ 511 then 0x7FFF
    else Int.ofNat ((((q.toNat <<< 15) + 0x4000) >>> 9))
  let unq := if sign < 0 then -unq else unq
  if unq < 0 then -(((-unq) * 31) >>> 5) else (unq * 31) >>> 5

/-- `tc_bc6h_err3_mag`: squared error of three magnitudes. -/
def bc6hErr3Mag (a : List Nat) (r g b : Nat) : Nat :=
  let dr := (Int.ofNat (a.getD 0 0)) - (Int.ofNat r)
  let dg := (Int.ofNat (a.getD 1 0)) - (Int.ofNat g)
  let db := (Int.ofNat (a.getD 2 0)) - (Int.ofNat b)
  (dr * dr + dg * dg + db * db).toNat

/-- `tc_bc6h_err3_smag`: squared error of three signed magnitudes, saturated
  at `UINT_MAX`. -/
def bc6hErr3Smag (a : List Int) (r g b : Int) : Nat :=
  let dr := a.getD 0 0 - r
  let dg := a.getD 1 0 - g
  let db := a.getD 2 0 - b
  let e : Int := dr * dr + dg * dg + db * db
  if e > Int.ofNat 0xFFFFFFFF then 0xFFFFFFFF else e.toNat

/-- `tc_bc6h_pack_signed_n`: clamp to an N-bit signed range, 2's complement. -/
def bc6hPackSignedN (v : Int) (bits : Nat) : Nat :=
  let half : Int := Int.ofNat (1 <<< (bits - 1))
  let v := if v < -half then -half else if v > half - 1 then half - 1 else v
  (Int32.ofInt v).toUInt32.toNat &&& ((1 <<< bits) - 1)

/-- `tc_bc6h_pack_signed10`. -/
def bc6hPackSigned10 (q : Int) : Nat :=
  let q := if q < -512 then -512 else if q > 511 then 511 else q
  (Int32.ofInt q).toUInt32.toNat &&& 1023

/-- `tc_bc6h_pal16_uf16`: the 16 interpolated magnitudes. -/
def bc6hPal16Uf16 (lo hi : List Nat) : List (List Int) :=
  (List.range 16).map (fun s =>
    let w := bc7Weights4.getD s 0
    (List.range 3).map (fun c =>
      Int.ofNat (bc6hUnquantUf16ToMag
        ((((64 - w) * lo.getD c 0 + w * hi.getD c 0 + 32) >>> 6)))))

/-- `tc_bc6h_choose_selectors_uf16_scalar`: nearest palette entry per texel.
  Returns `(selectors, totalErr)`. -/
def bc6hChooseSelectorsUf16 (target : List (List Nat)) (lo hi : List Nat) :
    List Nat × Nat :=
  let pal := bc6hPal16Uf16 lo hi
  let acc := (List.range 16).foldl (fun (acc : List Nat × Nat) i =>
    let t := target.getD i [0, 0, 0]
    let best := (List.range 16).foldl (fun (bacc : Nat × Nat) s =>
      let p := pal.getD s [0, 0, 0]
      let e := bc6hErr3Mag t (p.getD 0 0).toNat (p.getD 1 0).toNat (p.getD 2 0).toNat
      if e < bacc.2 then (s, e) else bacc) (0, 0xFFFFFFFF)
    (acc.1 ++ [best.1], acc.2 + best.2)) ([], 0)
  acc

/-- `tc_bc6h_quant_uf16_n`: float bits → N-bit unsigned magnitude. -/
def bc6hQuantUf16N (u : UInt32) (bits : Nat) : Nat :=
  if !bc6hBitsGt0 u then 0
  else
    let mag := (bc6hFloatToHalfBits u) &&& 0x7FFF
    let mag := if mag > 0x7BFF then 0x7BFF else mag
    (mag * ((1 <<< bits) - 1) + 15871) / 31743

/-- `tc_bc6h_unquant_n_to_mag`. -/
def bc6hUnquantNToMag (q bits : Nat) : Nat :=
  let unq := if q == 0 then 0 else if q ≥ (1 <<< bits) - 1 then 0xFFFF
             else ((q <<< 16) + 0x8000) >>> bits
  (unq * 31) >>> 6

/-- `tc_bc6h_quant_sf16_n`. -/
def bc6hQuantSf16N (u : UInt32) (bits : Nat) : Int :=
  let maxq : Int := Int.ofNat ((1 <<< (bits - 1)) - 1)
  if bc6hBitsEq0 u then 0
  else
    let h := bc6hFloatToHalfBits u
    let mag := if (h &&& 0x7FFF) > 0x7BFF then 0x7BFF else h &&& 0x7FFF
    let q : Int := Int.ofNat ((mag * maxq.toNat + 15871) / 31743)
    let q := if q > maxq then maxq else q
    if h &&& 0x8000 != 0 then -q else q

/-- `tc_bc6h_unquant_n_to_smag`. -/
def bc6hUnquantNToSmag (q0 : Int) (bits : Nat) : Int :=
  let maxq : Int := Int.ofNat ((1 <<< (bits - 1)) - 1)
  let (sign, q) := if q0 < 0 then (-1, -q0) else (1, q0)
  let unq : Int :=
    if q == 0 then 0
    else if q ≥ maxq then 0x7FFF
    else Int.ofNat ((((q.toNat <<< 15) + 0x4000) >>> (bits - 1)))
  let unq := if sign < 0 then -unq else unq
  if unq < 0 then -(((-unq) * 31) >>> 5) else (unq * 31) >>> 5

/-- `tc_bc6h_rdiv`: round-to-nearest division (halves away from zero). -/
def bc6hRdiv (num den : Int) : Int :=
  if num ≥ 0 then (num + den / 2) / den else -((-num + den / 2) / den)

end Texcomp
