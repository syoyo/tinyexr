/-
  TinyEXR - Lean 4 formalization of the tocio op kernels. Faithful
  Float32 ports of the scalar kernels in `sandbox/tocio/src/toc_interp.c`
  (matrix, range, exponent, exp-linear, log, log-camera, CDL), including
  evaluation order and per-channel extent (`ch` = 3 or 4).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Math

namespace Tocio

set_option linter.unusedVariables false

/-- RGB(A) pixel as four Float32 lanes. -/
abbrev Pixel := Float32 × Float32 × Float32 × Float32

/-- `k_matrix` kernel (ch = 3 ⇒ alpha defaults to 1.0). -/
def applyMatrix (m : List Float32) (off : List Float32) (px : Pixel) :
    Float32 × Float32 × Float32 × Float32 :=
  let r := px.1
  let g := px.2.1
  let b := px.2.2.1
  let a := px.2.2.2
  let m0 := m.getD 0 0.0
  let m1 := m.getD 1 0.0
  let m2 := m.getD 2 0.0
  let m3 := m.getD 3 0.0
  let m4 := m.getD 4 0.0
  let m5 := m.getD 5 0.0
  let m6 := m.getD 6 0.0
  let m7 := m.getD 7 0.0
  let m8 := m.getD 8 0.0
  let m9 := m.getD 9 0.0
  let m10 := m.getD 10 0.0
  let m11 := m.getD 11 0.0
  let m12 := m.getD 12 0.0
  let m13 := m.getD 13 0.0
  let m14 := m.getD 14 0.0
  let m15 := m.getD 15 0.0
  (m0 * r + m4 * g + m8 * b + m12 * a + off.getD 0 0.0,
   m1 * r + m5 * g + m9 * b + m13 * a + off.getD 1 0.0,
   m2 * r + m6 * g + m10 * b + m14 * a + off.getD 2 0.0,
   m3 * r + m7 * g + m11 * b + m15 * a + off.getD 3 0.0)

/-- `k_range` kernel over all four lanes. -/
def applyRange (scale offset vmin vmax : List Float32) (clampLo clampHi : Bool)
    (px : Pixel) : Pixel :=
  let step := fun (i : Nat) (v : Float32) =>
    let t := v * scale.getD i 0.0 + offset.getD i 0.0
    let t := if clampLo && t < vmin.getD i 0.0 then vmin.getD i 0.0 else t
    if clampHi && t > vmax.getD i 0.0 then vmax.getD i 0.0 else t
  (step 0 px.1, step 1 px.2.1, step 2 px.2.2.1, step 3 px.2.2.2)



/-- `k_exponent` kernel over the first `ch` lanes. -/
def applyExponent (e : List Float32) (mirror : Bool) (ch : Nat) (px : Pixel) :
    Pixel :=
  let step := fun (i : Nat) (v : Float32) =>
    if i >= ch then v
    else if mirror then
      let s : Float32 := if v < 0.0 then -1.0 else 1.0
      s * powf (if v < 0.0 then -v else v) (e.getD i 0.0)
    else powf (if v > 0.0 then v else 0.0) (e.getD i 0.0)
  (step 0 px.1, step 1 px.2.1, step 2 px.2.2.1, step 3 px.2.2.2)

/-- `k_exp_linear` kernel (always RGB extent). -/
def applyExpLinear (scale offset gamma brk slope : List Float32)
    (inverse mirror : Bool) (ch : Nat) (px : Pixel) : Pixel :=
  let n := if ch < 3 then ch else 3
  let step := fun (i : Nat) (v : Float32) =>
    if i >= n then v
    else
      let s : Float32 := 1.0
      let x := v
      let (s, x) := if mirror && x < 0.0 then ((-1.0 : Float32), -x) else (s, x)
      if !inverse then
        s * (if x > brk.getD i 0.0 then powf (x * scale.getD i 0.0 + offset.getD i 0.0) (gamma.getD i 0.0)
             else x * slope.getD i 0.0)
      else
        let ybrk := brk.getD i 0.0 * slope.getD i 0.0
        s * (if x > ybrk then (powf x (1.0 / gamma.getD i 0.0) - offset.getD i 0.0) / scale.getD i 0.0
             else x / slope.getD i 0.0)
  (step 0 px.1, step 1 px.2.1, step 2 px.2.2.1, step 3 px.2.2.2)

/-- `k_log` kernel (RGB extent). -/
def applyLog (base : Float32) (logSlope logOffset linSlope linOffset : List Float32)
    (inverse : Bool) (ch : Nat) (px : Pixel) : Pixel :=
  let n := if ch < 3 then ch else 3
  let lb := log2f base
  let step := fun (i : Nat) (v : Float32) =>
    if i >= n then v
    else
      if !inverse then
        let a := linSlope.getD i 0.0 * v + linOffset.getD i 0.0
        let l := log2f (if a > 0.0 then a else 1.1754944e-38) / lb
        logSlope.getD i 0.0 * l + logOffset.getD i 0.0
      else
        let e := (v - logOffset.getD i 0.0) / logSlope.getD i 0.0
        let p := raisef base e
        (p - linOffset.getD i 0.0) / linSlope.getD i 0.0
  (step 0 px.1, step 1 px.2.1, step 2 px.2.2.1, step 3 px.2.2.2)

/-- `k_logcam` kernel (RGB extent). -/
def applyLogCam (base : Float32) (logSlope logOffset linSlope linOffset : List Float32)
    (linBreak linearSlope linearOffset : List Float32)
    (inverse : Bool) (ch : Nat) (px : Pixel) : Pixel :=
  let n := if ch < 3 then ch else 3
  let lb := log2f base
  let step := fun (i : Nat) (v : Float32) =>
    if i >= n then v
    else
      if !inverse then
        if v <= linBreak.getD i 0.0 then
          linearSlope.getD i 0.0 * v + linearOffset.getD i 0.0
        else
          let a := linSlope.getD i 0.0 * v + linOffset.getD i 0.0
          let l := log2f (if a > 0.0 then a else 1.1754944e-38) / lb
          logSlope.getD i 0.0 * l + logOffset.getD i 0.0
      else
        let ybrk := linearSlope.getD i 0.0 * linBreak.getD i 0.0 + linearOffset.getD i 0.0
        if v <= ybrk then
          (v - linearOffset.getD i 0.0) / linearSlope.getD i 0.0
        else
          let e := (v - logOffset.getD i 0.0) / logSlope.getD i 0.0
          let p := raisef base e
          (p - linOffset.getD i 0.0) / linSlope.getD i 0.0
  (step 0 px.1, step 1 px.2.1, step 2 px.2.2.1, step 3 px.2.2.2)

/-- `k_cdl` kernel (RGB only; alpha passes through). -/
def applyCdl (slope offset power : List Float32) (saturation : Float32)
    (luma : List Float32) (clamp : Bool) (inverse : Bool) (px : Pixel) : Pixel :=
  let lr0 := luma.getD 0 0.0
  let lg0 := luma.getD 1 0.0
  let lb0 := luma.getD 2 0.0
  let (lr, lg, lb) :=
    if lr0 == 0.0 && lg0 == 0.0 && lb0 == 0.0 then
      ((0.2126 : Float32), 0.7152, 0.0722)
    else (lr0, lg0, lb0)
  let clampf := fun x =>
    if clamp && x < 0.0 then 0.0 else if clamp && x > 1.0 then 1.0 else x
  if !inverse then
    let v0 := clampf (let x0 := px.1 * slope.getD 0 0.0 + offset.getD 0 0.0
      if x0 >= 0.0 then powf x0 (power.getD 0 0.0) else x0)
    let v1 := clampf (let x1 := px.2.1 * slope.getD 1 0.0 + offset.getD 1 0.0
      if x1 >= 0.0 then powf x1 (power.getD 1 0.0) else x1)
    let v2 := clampf (let x2 := px.2.2.1 * slope.getD 2 0.0 + offset.getD 2 0.0
      if x2 >= 0.0 then powf x2 (power.getD 2 0.0) else x2)
    let lumaV := lr * v0 + lg * v1 + lb * v2
    (clampf (lumaV + saturation * (v0 - lumaV)),
     clampf (lumaV + saturation * (v1 - lumaV)),
     clampf (lumaV + saturation * (v2 - lumaV)),
     px.2.2.2)
  else
    let sat := saturation
    let lumaV := lr * px.1 + lg * px.2.1 + lb * px.2.2.1
    let undo := fun (i : Nat) (v : Float32) =>
      let x := lumaV + (if sat != 0.0 then (v - lumaV) / sat else 0.0)
      let s := slope.getD i 0.0
      let x := clampf x
      let x := if x >= 0.0 then powf x (1.0 / power.getD i 0.0) else x
      (x - offset.getD i 0.0) / (if s != 0.0 then s else 1.0)
    (undo 0 px.1, undo 1 px.2.1, undo 2 px.2.2.1, px.2.2.2)



end Tocio
