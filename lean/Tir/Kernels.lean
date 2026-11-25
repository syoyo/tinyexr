/-
  TinyEXR - Lean 4 model of the tir scalar resampling kernels.

  The Float32 definitions mirror `tir_kernels_scalar.c` / `tir_convert.c`
  operation for operation and are checked bit-exactly by `tir-kernel-diff`.
  The algebraic laws are proved on the corresponding rational model, where
  IEEE rounding cannot get in the way; the Float32 versions are pinned by
  the gate.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic
import Tir.Table
import Math.F32

namespace Tir

set_option linter.unusedVariables false

/-- Total list read with the C zero-padding convention. -/
def getF (a : List Float32) (i : Nat) : Float32 := a.getD i 0

/-- `tir__h_dot{1..4}_sc` for one output pixel row `x = 0`. -/
def hDot (wc start count : Nat) (src w : List Float32) : List Float32 :=
  let nblk := ((count + 3) / 4) * 4
  (List.range wc).map (fun c =>
    (List.range nblk).foldl (fun acc t => acc + getF w t * getF src ((start + t) * wc + c)) 0)

/-- Rational idealisation of `hDot` (first `count` taps only). -/
def hDotQ (count : Nat) (src w : List ℚ) : ℚ :=
  (List.range count).foldl (fun acc t => acc + w.getD t 0 * src.getD t 0) 0

/-- Weighted-sum scaling identity over `ℚ`. -/
theorem hDotQ_scale (count : Nat) (src w : List ℚ) (c : ℚ)
    (hs : ∀ t, t < count → src.getD t 0 = c) :
    hDotQ count src w =
      c * ((List.range count).foldl (fun acc t => acc + w.getD t 0) 0) := by
  unfold hDotQ
  induction count with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (fun t ht => hs t (by omega))]
      rw [hs n (by omega)]
      ring

/-- A normalised kernel preserves a constant image. -/
theorem hDotQ_const (count : Nat) (src w : List ℚ) (c : ℚ)
    (hs : ∀ t, t < count → src.getD t 0 = c)
    (hw : (List.range count).foldl (fun acc t => acc + w.getD t 0) 0 = 1) :
    hDotQ count src w = c := by
  rw [hDotQ_scale count src w c hs, hw, mul_one]

/-- The one-tap identity kernel reproduces the source sample. -/
theorem hDotQ_identity (src w : List ℚ) (h0 : w.getD 0 0 = 1) :
    hDotQ 1 src w = src.getD 0 0 := by
  unfold hDotQ
  simp only [List.range_one, List.foldl_cons, List.foldl_nil]
  rw [h0, one_mul]
  simp

/-- Generic sequential weighted sum (the vertical pass). -/
def vWeighted (n : Nat) (w : List Float32) (rows : List Float32) (c : Nat) : Float32 :=
  (List.range n).foldl (fun acc t => acc + getF w t * getF rows (t + c)) 0

/-- `tir__h_minmax_sc` for one output pixel. -/
def hMinMax (start count : Nat) (src : List Float32) (c : Nat) : Float32 × Float32 :=
  let v0 := getF src (start * 1 + c)
  (List.range (count - 1)).foldl (fun (mn, mx) k =>
    let v := getF src ((start + k + 1) + c)
    (if v < mn then v else mn, if v > mx then v else mx)) (v0, v0)

/-- `tir__antiring_apply_sc` on one value. -/
def antiringApply (v mn mx s : Float32) : Float32 :=
  let c := if v < mn then mn else if v > mx then mx else v
  v + s * (c - v)

/-- Rational idealisation of the anti-ring clamp. -/
def antiringApplyQ (v mn mx s : ℚ) : ℚ :=
  let c := if v < mn then mn else if v > mx then mx else v
  v + s * (c - v)

/-- Anti-ringing never pushes a value outside `[min v mn, max v mx]` for a
  strength in `[0,1]` (rational model; the f32 version is gate-pinned). -/
theorem antiring_within (v mn mx s : ℚ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hmn : mn ≤ mx) :
    min v mn ≤ antiringApplyQ v mn mx s ∧ antiringApplyQ v mn mx s ≤ max v mx := by
  unfold antiringApplyQ
  dsimp only
  by_cases hvmn : v < mn
  · have hd : 0 ≤ mn - v := by linarith
    have h0 : 0 ≤ s * (mn - v) := mul_nonneg hs0 hd
    have h1 : s * (mn - v) ≤ mn - v := mul_le_of_le_one_left hd hs1
    rw [itePos hvmn, min_eq_left (le_of_lt hvmn),
      max_eq_right (le_trans (le_of_lt hvmn) hmn)]
    constructor
    · linarith
    · linarith
  · by_cases hmxv : mx < v
    · have hd : mx - v ≤ 0 := by linarith
      have h0 : s * (mx - v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 hd
      have h1 : mx - v ≤ s * (mx - v) := by
        nlinarith [mul_le_mul_of_nonpos_right hs1 hd]
      rw [iteNeg hvmn, itePos hmxv, max_eq_left (le_of_lt hmxv), min_eq_right (le_of_not_gt hvmn)]
      constructor
      · linarith
      · linarith
    · have hmnv : mn ≤ v := le_of_not_gt hvmn
      have hvmx : v ≤ mx := le_of_not_gt hmxv
      rw [iteNeg hvmn, iteNeg hmxv, min_eq_right hmnv, max_eq_right hvmx]
      constructor <;> (ring_nf; linarith)

/-- `tir__clamp_range_sc` on one value. -/
def clampOne (v lo hi : Float32) : Float32 :=
  let v := if v < lo then lo else v
  if v > hi then hi else v

/-- Clamping to `[0,hi]` cannot produce a negative value (rational model). -/
def clampQ (v lo hi : ℚ) : ℚ :=
  let v := if v < lo then lo else v
  if v > hi then hi else v

theorem clamp_nonneg (v hi : ℚ) (h : 0 ≤ hi) : 0 ≤ clampQ v 0 hi := by
  unfold clampQ
  by_cases hlt : v < 0
  · rw [itePos hlt]
    by_cases hhi : (0 : ℚ) > hi
    · rw [itePos hhi]; linarith
    · rw [iteNeg hhi]
  · rw [iteNeg hlt]
    by_cases hhi : v > hi
    · rw [itePos hhi]; linarith
    · rw [iteNeg hhi]; linarith

/-- `tir__normalize3_sc` on one pixel. -/
def normalize3 (x y z : Float32) : Float32 × Float32 × Float32 :=
  let l2 := x * x + y * y + z * z
  if h : l2 > 1e-8 then
    let inv := 1 / ExrMath.sqrtfExact l2
    (x * inv, y * inv, z * inv)
  else (0, 0, 1)

theorem normal_degenerate_fallback (x y z : Float32) (h : ¬ x * x + y * y + z * z > 1e-8) :
    normalize3 x y z = (0, 0, 1) := by
  simp [normalize3, h]

/-- `tir__premult4_sc` / `tir__unpremult4_sc` on one pixel. -/
def premult4 (r g b a : Float32) : Float32 × Float32 × Float32 × Float32 :=
  (r * a, g * a, b * a, a)

def unpremult4 (r g b a : Float32) : Float32 × Float32 × Float32 × Float32 :=
  if a == 0 then (r, g, b, a) else
    let inv : Float32 := 1 / a
    (r * inv, g * inv, b * inv, a)

/-- Range compression / expansion (`tir_domain.c`), single channel. -/
def rangeCompress (x : Float32) : Float32 :=
  let ax := if x < 0 then -x else x
  if ax <= (0.18 : Float32) then x else
    let y : Float32 := (-0.54576885700225830078 : Float32) +
      (0.18351669609546661377 : Float32) *
        ExrMath.logf ((284.3577880859375 : Float32) * ax + 1)
    if x < 0 then -y else y

def rangeExpand (y : Float32) : Float32 :=
  let ay := if y < 0 then -y else y
  if ay <= (0.18 : Float32) then y else
    let x : Float32 :=
      (ExrMath.expf ((ay - (-0.54576885700225830078 : Float32)) /
        (0.18351669609546661377 : Float32)) - 1) /
        (284.3577880859375 : Float32)
    if y < 0 then -x else x

/-! ## Pixel-type conversions (bit-exact ports of tir_convert.c) -/

theorem f32Bits : Float32.toBits (Float32.ofBits 0x3f800000) = 0x3f800000 := by decide

/-- `tir__f16_to_f32_sc` on one half. All bit arithmetic is done in `Nat`
  (the bit patterns are non-negative), then packed into the f32 bit pattern. -/
def f16ToF32 (h : UInt16) : Float32 :=
  let hu := h.toNat
  let sign := (hu &&& 0x8000) <<< 16
  let exp := (hu >>> 10) &&& 0x1f
  let man := hu &&& 0x3ff
  Float32.ofBits (UInt32.ofNat <|
    if exp == 0 then
      if man == 0 then sign
      else
        let e := (List.range 11).find? (fun k => ((man <<< (k + 1)) &&& 0x400) != 0) |>.getD 0
        let m := (man <<< (e + 1)) &&& 0x3ff
        sign ||| ((127 - 15 - e) <<< 23) ||| (m <<< 13)
    else if exp == 31 then sign ||| 0x7f800000 ||| (man <<< 13)
    else sign ||| ((exp + 112) <<< 23) ||| (man <<< 13))

/-- `tir__f32_to_f16_sc` on one float. -/
def f32ToF16 (x : Float32) : UInt16 :=
  let bits := (Float32.toBits x).toNat
  let sign := (bits >>> 16) &&& 0x8000
  let exp := (bits >>> 23) &&& 0xff
  let man := bits &&& 0x7fffff
  UInt16.ofNat <|
    if exp == 0xff then
      sign ||| 0x7c00 ||| (if man != 0 then 0x200 ||| (man >>> 13) else 0)
    else
      let e : Int := (exp : Int) - 127 + 15
      if e >= 31 then sign ||| 0x7c00
      else if e <= 0 then
        if e < -10 then sign
        else
          let shift := (14 - e).toNat
          let m := man ||| 0x800000
          let hm := m >>> shift
          let rem := m &&& ((1 <<< shift) - 1)
          let half := 1 <<< (shift - 1)
          let hm' := if rem > half || (rem == half && (hm &&& 1) != 0) then hm + 1 else hm
          sign ||| hm'
      else
        let hm := man >>> 13
        let rem := man &&& 0x1fff
        if rem > 0x1000 || (rem == 0x1000 && (hm &&& 1) != 0) then
          let hm' := hm + 1
          if hm' == 0x400 then
            let e' := e + 1
            if e' >= 31 then sign ||| 0x7c00
            else sign ||| (e'.toNat <<< 10)
          else sign ||| (e.toNat <<< 10) ||| hm'
        else sign ||| (e.toNat <<< 10) ||| hm

/-- `tir__u8_to_f32_sc` / `tir__u16_to_f32_sc`. -/
def u8ToF32 (v : UInt8) : Float32 := Float32.ofNat v.toNat * (1 / 255 : Float32)
def u16ToF32 (v : UInt16) : Float32 := Float32.ofNat v.toNat * (1 / 65535 : Float32)

/-- `tir__f32_to_u8_sc` (clamp + RNE). -/
def f32ToU8 (x : Float32) : UInt8 :=
  let v := if x > 0 then x else 0
  let v := if v > 1 then 1 else v
  (Float32.round (v * 255)).toUInt8

/-- `tir__f32_to_u16_sc`. -/
def f32ToU16 (x : Float32) : UInt16 :=
  let v := if x > 0 then x else 0
  let v := if v > 1 then 1 else v
  (Float32.round (v * 65535)).toUInt16

end Tir
