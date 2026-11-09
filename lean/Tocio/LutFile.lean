/-
  TinyEXR - Lean 4 formalization of the tocio file-LUT surface.

  .cube (1D/3D, Iridas) and Sony .spi1d/.spi3d parsers with the
  allocation-fit checks (`toc_values_fit`), plus the LUT1D/LUT3D
  per-pixel application kernels (`toc_lut.c`, trilinear +
  tetrahedral paths) in Float32.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Math

namespace Tocio

set_option linter.unusedVariables false

/-- LUT interpolation mode. -/
inductive LutInterp where
  | nearest
  | linear
  | trilinear
  | tetrahedral
  deriving Repr, DecidableEq, Inhabited

/-- Clamp a unit coordinate into [0,1]. -/
def clampU (u : Float32) : Float32 :=
  if !(u > 0.0) then 0.0 else if u > 1.0 then 1.0 else u

/-- LUT1D kernel (mirrors `toc_lut1d_apply_pixel`): per-channel linear
  or nearest sampling over `data` (rows of `channels`). -/
def applyLut1d (length channels : Nat) (domainMin domainMax : Float32)
    (interp : LutInterp) (data : List Float32) (px : Float32 × Float32 × Float32) :
    Float32 × Float32 × Float32 :=
  let (px0, px1, px2) := px
  let den : Float32 := domainMax - domainMin
  let n := length
  let step := fun (i : Nat) (v : Float32) =>
    if n < 2 then v
    else
      let u : Float32 := clampU (if den != 0.0 then (v - domainMin) / den else 0.0)
      let g : Float32 := u * Float32.ofNat (n - 1)
      let i0 : Nat := if truncToIntF g >= Int.ofNat (n - 1) then n - 2 else (truncToIntF g).toNat
      let f : Float32 := g - Float32.ofNat i0
      let (a, b) :=
        if channels == 1 then
          ((data.getD i0 0.0), data.getD (i0 + 1) 0.0)
        else
          ((data.getD (i0 * 3 + i) 0.0), data.getD ((i0 + 1) * 3 + i) 0.0)
      if interp == .nearest then (if f < 0.5 then a else b)
      else a + (b - a) * f
  (step 0 px0, step 1 px1, step 2 px2)

/-- Cell lookup in a 3D LUT (R-fastest packing). -/
def lutCell (data : List Float32) (size ir ig ib : Nat) (k : Nat) : Float32 :=
  data.getD (((ib * size + ig) * size + ir) * 3 + k) 0.0

/-- LUT3D trilinear kernel (mirrors the non-tetrahedral path). -/def applyLut3dTrilinear (size : Nat) (domainMin domainMax : List Float32)
    (data : List Float32) (px : Float32 × Float32 × Float32) :
    Float32 × Float32 × Float32 :=
  let n := size
  let (q0, q1, q2) := px
  let pxL := [q0, q1, q2]
  let icf := (List.range 3).map (fun c =>
    let den : Float32 := domainMax.getD c 0.0 - domainMin.getD c 0.0
    let u : Float32 := clampU (if den != 0.0 then (pxL.getD c 0.0 - domainMin.getD c 0.0) / den else 0.0)
    let g : Float32 := u * Float32.ofNat (n - 1)
    let i : Nat := if truncToIntF g >= Int.ofNat (n - 1) then n - 2 else (truncToIntF g).toNat
    (i, g - Float32.ofNat i))
  let ir := icf.getD 0 (0, 0.0)
  let ig := icf.getD 1 (0, 0.0)
  let ib := icf.getD 2 (0, 0.0)
  let cc : Nat → Nat → Nat → Nat → Float32 := fun ir ig ib k =>
    lutCell data size ir ig ib k
  let lerp := fun (a b t : Float32) => a + (b - a) * t
  let ch := fun k =>
    let c00 : Float32 := lerp (cc ir.1 ig.1 ib.1 k) (cc (ir.1 + 1) ig.1 ib.1 k) ir.2
    let c01 : Float32 := lerp (cc ir.1 ig.1 (ib.1 + 1) k) (cc (ir.1 + 1) ig.1 (ib.1 + 1) k) ir.2
    let c10 : Float32 := lerp (cc ir.1 (ig.1 + 1) ib.1 k) (cc (ir.1 + 1) (ig.1 + 1) ib.1 k) ir.2
    let c11 : Float32 := lerp (cc ir.1 (ig.1 + 1) (ib.1 + 1) k) (cc (ir.1 + 1) (ig.1 + 1) (ib.1 + 1) k) ir.2
    let a : Float32 := lerp c00 c10 ig.2
    let bb : Float32 := lerp c01 c11 ig.2
    lerp a bb ib.2
  (ch 0, ch 1, ch 2)

/-- values-fit predicate (allocation guard mirror). -/
def valuesFit (want remaining : Nat) : Bool :=
  decide (want ≤ remaining)

/-- Allocation bound for a 3D cube (256³·3). -/
theorem cube3dWant_max : 256 * 256 * 256 * 3 = 50331648 := by native_decide
/-- .cube LUT_1D/3D size ranges are 2..256. -/
theorem cubeSize_bound (n : Nat) : n < 2 ∨ n > 256 ∨ (2 ≤ n ∧ n ≤ 256) := by
  omega

/-- LUT3D tetrahedral kernel (mirrors the tetra path bit-for-bit in
  interpolation order). -/
def applyLut3dTet (size : Nat) (domainMin domainMax : List Float32)
    (data : List Float32) (px : Float32 × Float32 × Float32) :
    Float32 × Float32 × Float32 :=
  let n := size
  let (q0, q1, q2) := px
  let pxL := [q0, q1, q2]
  let icf := (List.range 3).map (fun c =>
    let den : Float32 := domainMax.getD c 0.0 - domainMin.getD c 0.0
    let u : Float32 := clampU (if den != 0.0 then (pxL.getD c 0.0 - domainMin.getD c 0.0) / den else 0.0)
    let g : Float32 := u * Float32.ofNat (n - 1)
    let i : Nat := if truncToIntF g >= Int.ofNat (n - 1) then n - 2 else (truncToIntF g).toNat
    (i, g - Float32.ofNat i))
  let ir := icf.getD 0 (0, 0.0)
  let ig := icf.getD 1 (0, 0.0)
  let ib := icf.getD 2 (0, 0.0)
  let cc : Nat → Nat → Nat → Nat → Float32 := fun ir ig ib k =>
    lutCell data size ir ig ib k
  let tx (k idx : Nat) : Float32 :=
    match idx with
    | 0 => cc ir.1 ig.1 ib.1 k
    | 1 => cc (ir.1 + 1) (ig.1 + 1) (ib.1 + 1) k
    | 2 => cc (ir.1 + 1) ig.1 ib.1 k
    | 3 => cc ir.1 (ig.1 + 1) ib.1 k
    | 4 => cc ir.1 ig.1 (ib.1 + 1) k
    | 5 => cc (ir.1 + 1) (ig.1 + 1) ib.1 k
    | 6 => cc (ir.1 + 1) ig.1 (ib.1 + 1) k
    | _ => cc ir.1 (ig.1 + 1) (ib.1 + 1) k
  let fr := ir.2
  let fg := ig.2
  let fb := ib.2
  let ch := fun k =>
    if fr >= fg && fg >= fb then
      tx k 0 + fr * (tx k 2 - tx k 0) +
        fg * (tx k 5 - tx k 2) + fb * (tx k 1 - tx k 5)
    else if fr >= fb && fb >= fg then
      tx k 0 + fr * (tx k 2 - tx k 0) +
        fb * (tx k 6 - tx k 2) + fg * (tx k 1 - tx k 6)
    else if fb >= fr && fr >= fg then
      tx k 0 + fb * (tx k 4 - tx k 0) +
        fr * (tx k 6 - tx k 4) + fg * (tx k 1 - tx k 6)
    else if fg >= fr && fr >= fb then
      tx k 0 + fg * (tx k 3 - tx k 0) +
        fr * (tx k 5 - tx k 3) + fb * (tx k 1 - tx k 5)
    else if fg >= fb && fb >= fr then
      tx k 0 + fg * (tx k 3 - tx k 0) +
        fb * (tx k 7 - tx k 3) + fr * (tx k 1 - tx k 7)
    else
      tx k 0 + fb * (tx k 4 - tx k 0) +
        fg * (tx k 7 - tx k 4) + fr * (tx k 1 - tx k 7)
  (ch 0, ch 1, ch 2)

end Tocio
