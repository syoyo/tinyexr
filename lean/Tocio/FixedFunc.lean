/-
  TinyEXR - Lean 4 formalization of the tocio FixedFunction kernels.

  Float32 ports of the per-style helpers and the switch in
  `toc_fixedfunc_apply_pixel` (`sandbox/tocio/src/toc_builtins.c`),
  reusing `Tocio.Math` (`powf`/`sqrtf`/`log2f`/`exp2f`).

  STYLE NOTE (toolchain quirk): long infix Float32 chains break
  elaboration in this toolchain version (the literal instances degrade
  to `Float32.Model`). Reliable idiom used throughout: destructure
  tuples at entry and use direct `Float32.add/mul/sub/div` calls.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Math
import Tocio.Op

namespace Tocio

set_option linter.unusedVariables false

/-- Absolute value. -/
def fabsf (x : Float32) : Float32 :=
  Float32.ofBits (Float32.toBits x &&& 0x7fffffff)

/-- Copy the sign of `y` onto `x`. -/
def copysignf (x y : Float32) : Float32 :=
  Float32.ofBits ((Float32.toBits x &&& 0x7fffffff) ||| (Float32.toBits y &&& 0x80000000))

/-- C-branch max/min semantics. -/
def fmaxf (a b : Float32) : Float32 := if a > b then a else b
def fminf (a b : Float32) : Float32 := if a < b then a else b
def clampf32 (x lo hi : Float32) : Float32 :=
  let l1 : Float32 := if x < lo then lo else x
  if l1 > hi then hi else l1

/-- Floor via the bit-decoding truncation plus the one-step correction. -/
def floorf (x : Float32) : Float32 :=
  let r : Float32 := smallIntToF32 (truncToIntF x)
  if r > x then r - (1.0 : Float32) else r

/-- Freestanding atan2 (minimax polynomial). -/
def atan2f (y x : Float32) : Float32 :=
  let ax : Float32 := if x < 0.0 then -x else x
  let ay : Float32 := if y < 0.0 then -y else y
  if ax + ay == 0.0 then 0.0
  else
    let a : Float32 := if ay < ax then y / x else x / y
    let q0 : Nat := if ay < ax then 0 else 2
    let q1 : Nat := if x < 0.0 && ay < ax then 1 else q0
    let q : Nat := if y < 0.0 && ay >= ax then 3 else q1
    let a2 : Float32 := a * a
    let d1 : Float32 := (Float32.ofBits 0x3eaaaaab)
    let d2 : Float32 := (Float32.ofBits 0x3e4ccccd)
    let d3 : Float32 := (Float32.ofBits 0x3e124925)
    let d4 : Float32 := (Float32.ofBits 0x3de38e39)
    let h0 : Float32 := d3 - a2 * d4
    let h1 : Float32 := d2 - a2 * h0
    let h2 : Float32 := d1 - a2 * h1
    let h3 : Float32 := (1.0 : Float32) - a2 * h2
    let r : Float32 := a * h3
    match q with
    | 1 => (if r < 0.0 then -3.141592653589793 else 3.141592653589793) + r
    | 2 => 1.5707963267948966 - r
    | 3 => -1.5707963267948966 - r
    | _ => r

/-- Hue weight (quadratic B-spline). -/
def redmodHueWeight (red grn blu invWidth : Float32) : Float32 :=
  let a : Float32 := 2.0 * red - (grn + blu)
  let b : Float32 := 1.7320508075688772 * (grn - blu)
  let hue : Float32 := atan2f b a
  let knot : Float32 := hue * invWidth + 2.0
  let j : Int := truncToIntF knot
  if j < 0 || j >= 4 then 0.0
  else
    let q : Float32 := (Float32.ofBits 0x3e800000)
    let wn25 : Float32 := (Float32.ofBits 0xbe800000)
    let w75 : Float32 := (Float32.ofBits 0x3f400000)
    let w75n : Float32 := (Float32.ofBits 0xbf400000)
    let w150 : Float32 := (Float32.ofBits 0xbfc00000)
    let c0 : Float32 := if j == 0 then q else if j == 1 then w75n
                        else if j == 2 then w75 else wn25
    let c1 : Float32 := if j == 0 then 0.0 else if j == 1 then w75
                        else if j == 2 then w150 else w75
    let c2 : Float32 := if j == 0 then 0.0 else if j == 1 then w75
                        else if j == 2 then 0.0 else w75n
    let c3 : Float32 := if j == 0 then 0.0 else if j == 1 then q
                        else if j == 2 then 1.0 else q
    let t : Float32 := knot - smallIntToF32 j
    let w0 : Float32 := c1 + t * c0
    let w1 : Float32 := c2 + t * w0
    c3 + t * w1

/-- Saturation weight. -/
def redmodSatWeight (red grn blu : Float32) : Float32 :=
  let mn : Float32 := fminf red (fminf grn blu)
  let mx : Float32 := fmaxf red (fmaxf grn blu)
  let sNum : Float32 := fmaxf (Float32.ofBits 0x2edbe6ff) mx - fmaxf (Float32.ofBits 0x2edbe6ff) mn
  let sDen : Float32 := fmaxf (Float32.ofBits 0x3c23d70a) mx
  sNum / sDen

/-- Red Mod forward. -/
def applyRedModFwd (red0 grn0 blu0 scale pivot invWidth : Float32) :
    Float32 × Float32 × Float32 :=
  let fH : Float32 := redmodHueWeight red0 grn0 blu0 invWidth
  if fH > 0.0 then
    let fS : Float32 := redmodSatWeight red0 grn0 blu0
    let oneMinusScale : Float32 := (1.0 : Float32) - scale
    let t0 : Float32 := fH * fS
    let t1 : Float32 := t0 * (pivot - red0)
    let t2 : Float32 := t1 * oneMinusScale
    let newRed : Float32 := red0 + t2
    if grn0 >= blu0 then
      let hueFac : Float32 := (grn0 - blu0) / fmaxf (Float32.ofBits 0x2edbe6ff) (red0 - blu0)
      let t : Float32 := newRed - blu0
      (newRed, hueFac * t + blu0, blu0)
    else
      let hueFac : Float32 := (blu0 - grn0) / fmaxf (Float32.ofBits 0x2edbe6ff) (red0 - grn0)
      let t : Float32 := newRed - grn0
      (newRed, grn0, hueFac * t + grn0)
  else (red0, grn0, blu0)

/-- Red Mod inverse. -/
def applyRedModInv (red0 grn0 blu0 scale pivot invWidth : Float32) :
    Float32 × Float32 × Float32 :=
  let fH : Float32 := redmodHueWeight red0 grn0 blu0 invWidth
  if fH > 0.0 then
    let oneMinusScale : Float32 := (1.0 : Float32) - scale
    let minChan : Float32 := fminf grn0 blu0
    let a : Float32 := fH * oneMinusScale - 1.0
    let t : Float32 := fH * (pivot + minChan)
    let b : Float32 := red0 - t * oneMinusScale
    let u : Float32 := fH * pivot * minChan
    let cVal : Float32 := u * oneMinusScale
    let d1 : Float32 := b * b
    let d2 : Float32 := 4.0 * a * cVal
    let disc : Float32 := d1 - d2
    let newRed : Float32 := if disc >= 0.0 then (-b - sqrtf disc) / (2.0 * a) else red0
    if grn0 >= blu0 then
      let hueFac : Float32 := (grn0 - blu0) / fmaxf (Float32.ofBits 0x2edbe6ff) (red0 - blu0)
      let t : Float32 := newRed - blu0
      (newRed, hueFac * t + blu0, blu0)
    else
      let hueFac : Float32 := (blu0 - grn0) / fmaxf (Float32.ofBits 0x2edbe6ff) (red0 - grn0)
      let t : Float32 := newRed - grn0
      (newRed, grn0, hueFac * t + grn0)
  else (red0, grn0, blu0)

/-- Glow luminance-weighted value. -/
def glowYc (red grn blu : Float32) : Float32 :=
  let d0 : Float32 := blu - grn
  let d1 : Float32 := grn - red
  let d2 : Float32 := red - blu
  let t0 : Float32 := blu * d0
  let t1 : Float32 := grn * d1
  let t2 : Float32 := red * d2
  let c : Float32 := t0 + t1 + t2
  let chroma : Float32 := if c > 0.0 then sqrtf c else 0.0
  let s : Float32 := blu + grn + red
  let t : Float32 := 1.75 * chroma
  (s + t) / 3.0

/-- Glow sigmoid. -/
def glowSigmoid (sat : Float32) : Float32 :=
  let x : Float32 := (sat - 0.4) * 5.0
  let sign : Float32 := copysignf 1.0 x
  let t0 : Float32 := sign * x
  let t : Float32 := 1.0 - 0.5 * t0
  let t : Float32 := fmaxf 0.0 t
  let u : Float32 := 1.0 - t * t
  let v : Float32 := sign * u
  (1.0 + v) * 0.5

/-- Glow forward. -/
def applyGlowFwd (r0 g0 b0 glowGain glowMid : Float32) :
    Float32 × Float32 × Float32 :=
  let yc : Float32 := glowYc r0 g0 b0
  let s : Float32 := glowSigmoid (redmodSatWeight r0 g0 b0)
  let gg : Float32 := glowGain * s
  let gm := glowMid
  let glowGainOut : Float32 :=
    if yc >= gm * 2.0 then 0.0
    else if yc <= gm * 2.0 / 3.0 then gg
    else
      let t : Float32 := gm / yc - 0.5
      gg * t
  let added : Float32 := 1.0 + glowGainOut
  (r0 * added, g0 * added, b0 * added)

/-- Glow inverse. -/
def applyGlowInv (r0 g0 b0 glowGain glowMid : Float32) :
    Float32 × Float32 × Float32 :=
  let yc : Float32 := glowYc r0 g0 b0
  let s : Float32 := glowSigmoid (redmodSatWeight r0 g0 b0)
  let gg : Float32 := glowGain * s
  let gm := glowMid
  let glowGainOut : Float32 :=
    if yc >= gm * 2.0 then 0.0
    else if yc <= (1.0 + gg) * gm * 2.0 / 3.0 then -gg / (1.0 + gg)
    else
      let t : Float32 := gm / yc - 0.5
      gg * t / (gg * 0.5 - 1.0)
  let reduced : Float32 := 1.0 + glowGainOut
  (r0 * reduced, g0 * reduced, b0 * reduced)

/-- Dark-to-Dim shared applier. -/
def applyDarkToDim (r0 g0 b0 w1 w2 w3 eps gammaMinusOne : Float32) :
    Float32 × Float32 × Float32 :=
  let t1 : Float32 := w1 * r0
  let t2 : Float32 := w2 * g0
  let t3 : Float32 := w3 * b0
  let y : Float32 := fmaxf eps (t1 + t2 + t3)
  let s : Float32 := powf y gammaMinusOne
  (r0 * s, g0 * s, b0 * s)

/-- Gamut compression forward kernel. -/
def gcCompress (dist thr scale power : Float32) : Float32 :=
  let nd : Float32 := (dist - thr) / scale
  let p : Float32 := powf nd power
  let ip : Float32 := 1.0 / power
  let t : Float32 := 1.0 + p
  let q : Float32 := powf t ip
  let u : Float32 := scale * nd
  thr + u / q

/-- Gamut compression inverse kernel. -/
def gcUncompress (dist thr scale power : Float32) : Float32 :=
  if dist >= thr + scale then dist
  else
    let nd : Float32 := (dist - thr) / scale
    let p : Float32 := powf nd power
    let ip : Float32 := 1.0 / power
    let t : Float32 := p / (p - 1.0)
    let q : Float32 := powf (-t) ip
    thr + scale * q

/-- Gamut compression scale. -/
def gcScale (lim thr power : Float32) : Float32 :=
  if lim <= 1.0 || thr >= 1.0 || power == 0.0 || power != power then 1.0
  else
    let ip : Float32 := 1.0 / power
    let t : Float32 := (lim - thr) / (1.0 - thr)
    let u : Float32 := powf t power - 1.0
    let d : Float32 := powf u ip
    if d != 0.0 then (lim - thr) / d else 1.0

/-- Per-axis gamut compression. -/
def gcApply (val ach thr scale power : Float32) (invert : Bool) : Float32 :=
  if ach == 0.0 then 0.0
  else
    let dist : Float32 := (ach - val) / fabsf ach
    if dist < thr then val
    else
      let compr : Float32 := if invert then gcUncompress dist thr scale power
                             else gcCompress dist thr scale power
      let t : Float32 := compr * fabsf ach
      ach - t

/-- RGB → HSV (extended range). -/
def rgbToHsv (r g b : Float32) : Float32 × Float32 × Float32 :=
  let mn : Float32 := fminf r (fminf g b)
  let mx : Float32 := fmaxf r (fmaxf g b)
  let val0 : Float32 := mx
  let (sat0, hue0) :=
    if mn != mx then
      let delta : Float32 := mx - mn
      let sat : Float32 := if mx != 0.0 then delta / mx else 0.0
      let h0 : Float32 := if r == mx then (g - b) / delta
                  else if g == mx then 2.0 + (b - r) / delta
                  else 4.0 + (r - g) / delta
      let hue : Float32 := if h0 < 0.0 then h0 + 6.0 else h0
      (sat, hue * (Float32.ofBits 0x3e2aaaab))
    else ((0.0 : Float32), 0.0)
  let val : Float32 := if mn < 0.0 then val0 + mn else val0
  let sat : Float32 := if -mn > mx then (mx - mn) / -mn else sat0
  (hue0, sat, val)

/-- HSV → RGB. -/
def hsvToRgb (h0 s0 v : Float32) : Float32 × Float32 × Float32 :=
  let h : Float32 := (h0 - floorf h0) * 6.0
  let s : Float32 := clampf32 s0 0.0 1.999
  let r : Float32 := clampf32 (fabsf (h - 3.0) - 1.0) 0.0 1.0
  let g : Float32 := clampf32 (2.0 - fabsf (h - 2.0)) 0.0 1.0
  let b : Float32 := clampf32 (2.0 - fabsf (h - 4.0)) 0.0 1.0
  let rgbMin0 : Float32 := v * (1.0 - s)
  let den : Float32 := 2.0 - s
  let (rgbMin, rgbMax) :=
    if s > 1.0 then
      let rgbMin : Float32 := v * (1.0 - s) / den
      (rgbMin, v - rgbMin)
    else
      (rgbMin0, v)
  let (rgbMin, rgbMax) :=
    if v < 0.0 then
      let rgbMin : Float32 := v / den
      (rgbMin, v - rgbMin)
    else (rgbMin, rgbMax)
  let delta : Float32 := rgbMax - rgbMin
  (r * delta + rgbMin, g * delta + rgbMin, b * delta + rgbMin)

/-- XYZ → xyY. -/
def xyzToXyy (xx yy zz : Float32) : Float32 × Float32 × Float32 :=
  let d0 : Float32 := xx + yy + zz
  let d : Float32 := if d0 == 0.0 then 0.0 else 1.0 / d0
  (xx * d, yy * d, yy)

/-- xyY → XYZ. -/
def xyyToXyz (x y yy : Float32) : Float32 × Float32 × Float32 :=
  let d : Float32 := if y == 0.0 then 0.0 else 1.0 / y
  let o1 : Float32 := yy * x
  let o2 : Float32 := o1 * d
  let o3 : Float32 := 1.0 - x - y
  let o4 : Float32 := yy * o3
  (o2, yy, o4 * d)

/-- XYZ → uvY. -/
def xyzToUvy (xx yy zz : Float32) : Float32 × Float32 × Float32 :=
  let t1 : Float32 := 15.0 * yy
  let t2 : Float32 := 3.0 * zz
  let d0 : Float32 := xx + t1 + t2
  let d : Float32 := if d0 == 0.0 then 0.0 else 1.0 / d0
  (4.0 * xx * d, 9.0 * yy * d, yy)

/-- uvY → XYZ. -/
def uvyToXyz (u v yy : Float32) : Float32 × Float32 × Float32 :=
  let d : Float32 := if v == 0.0 then 0.0 else 1.0 / v
  let x0 : Float32 := (9.0 / 4.0) * yy
  let xx : Float32 := x0 * u * d
  let w : Float32 := 4.0 - u - (Float32.ofBits 0x40d55555) * v
  let z0 : Float32 := (3.0 / 4.0) * yy
  let zz : Float32 := z0 * w * d
  (xx, yy, zz)

/-- XYZ → LUV (D65 white). -/
def xyzToLuv (xx yy zz : Float32) : Float32 × Float32 × Float32 :=
  let d0 : Float32 := xx + 15.0 * yy + 3.0 * zz
  let d : Float32 := if d0 == 0.0 then 0.0 else 1.0 / d0
  let u : Float32 := 4.0 * xx * d
  let v : Float32 := 9.0 * yy * d
  let lstar : Float32 :=
    if yy <= (Float32.ofBits 0x3c111aa7) then (Float32.ofBits 0x41108704) * yy
    else 1.16 * powf yy 0.333333333 - 0.16
  let t0 : Float32 := 13.0 * lstar
  (lstar, t0 * (u - (Float32.ofBits 0x3e4a93f3)), t0 * (v - (Float32.ofBits 0x3eefc7a3)))

/-- LUV → XYZ. -/
def luvToXyz (lstar ustar vstar : Float32) : Float32 × Float32 × Float32 :=
  let d : Float32 := if lstar == 0.0 then 0.0 else (Float32.ofBits 0x3d9d89d9) / lstar
  let u : Float32 := ustar * d + (Float32.ofBits 0x3e4a93f3)
  let v : Float32 := vstar * d + (Float32.ofBits 0x3eefc7a3)
  let tmp : Float32 := (lstar + 0.16) * (Float32.ofBits 0x3f5cb08d)
  let yy : Float32 := if lstar <= 0.08 then (Float32.ofBits 0x3de2b9a4) * lstar else tmp * tmp * tmp
  let dd : Float32 := if v == 0.0 then 0.0 else 0.25 / v
  let t0 : Float32 := 9.0 * yy
  let t1 : Float32 := t0 * u
  let w0 : Float32 := 3.0 * u
  let w1 : Float32 := 20.0 * v
  let w : Float32 := 12.0 - w0 - w1
  let t2 : Float32 := yy * w
  (t1 * dd, yy, t2 * dd)

/-- PQ (ST 2084) encode. -/
def pqEncode (l : Float32) : Float32 :=
  let m1 : Float32 := 0.1593017578125
  let m2 : Float32 := 78.84375
  let c1 : Float32 := 0.8359375
  let c2 : Float32 := 18.8515625
  let c3 : Float32 := 18.6875
  if l <= 0.0 then 0.0
  else
    let t0 : Float32 := l * 0.01
    let lm : Float32 := powf t0 m1
    let t1 : Float32 := c2 * lm
    let t2 : Float32 := c1 + t1
    let t3 : Float32 := c3 * lm
    let t4 : Float32 := 1.0 + t3
    let t5 : Float32 := t2 / t4
    powf t5 m2

/-- PQ decode. -/
def pqDecode (n : Float32) : Float32 :=
  let m1 : Float32 := 0.1593017578125
  let m2 : Float32 := 78.84375
  let c1 : Float32 := 0.8359375
  let c2 : Float32 := 18.8515625
  let c3 : Float32 := 18.6875
  if n <= 0.0 then 0.0
  else
    let np : Float32 := powf n (1.0 / m2)
    let num : Float32 := if np - c1 < 0.0 then 0.0 else np - c1
    let den : Float32 := c2 - c3 * np
    if den <= 0.0 then 0.0
    else
      let t : Float32 := num / den
      powf t (1.0 / m1) * 100.0

/-- HLG OETF encode. -/
def hlgEncode (e : Float32) : Float32 :=
  let a : Float32 := 0.17883277
  let b : Float32 := 0.28466892
  let c : Float32 := 0.55991073
  if e <= 0.0 then 0.0
  else if e <= 1.0 / 12.0 then sqrtf (3.0 * e)
  else
    let t : Float32 := 12.0 * e - b
    let l : Float32 := log2f t
    let u : Float32 := l * 0.6931471805599453
    a * u + c

/-- HLG decode. -/
def hlgDecode (ep : Float32) : Float32 :=
  let a : Float32 := 0.17883277
  let b : Float32 := 0.28466892
  let c : Float32 := 0.55991073
  if ep <= 0.0 then 0.0
  else if ep <= 0.5 then ep * ep / 3.0
  else
    let t : Float32 := (ep - c) / a
    let u : Float32 := t * 1.4426950408889634
    let v : Float32 := exp2f u
    (v + b) / 12.0

/-- Per-channel transfer dispatch. -/
def applyTransfer (style : FfStyle) (px : Float32 × Float32 × Float32) :
    Float32 × Float32 × Float32 :=
  match style with
  | .linToPq => let (r, g, b) := px
                (pqEncode r, pqEncode g, pqEncode b)
  | .pqToLin => let (r, g, b) := px
                (pqDecode r, pqDecode g, pqDecode b)
  | .linToHlg => let (r, g, b) := px
                (hlgEncode r, hlgEncode g, hlgEncode b)
  | .hlgToLin => let (r, g, b) := px
                (hlgDecode r, hlgDecode g, hlgDecode b)
  | _ => px

/-- Rec.2100 surround matrix application (scale luminance by g^e). -/
def applySurround (px : Float32 × Float32 × Float32) (g : Float32) (invert : Bool) :
    Float32 × Float32 × Float32 :=
  let (r, gg, b) := px
  let t0 : Float32 := 0.2627 * r
  let t1 : Float32 := 0.6780 * gg
  let t2 : Float32 := 0.0593 * b
  let y : Float32 := t0 + t1 + t2
  if y <= 0.0 then px
  else
    let e : Float32 := if invert then 1.0 / g - 1.0 else g - 1.0
    let yy : Float32 := powf y e
    (r * yy, gg * yy, b * yy)
/-- Gamut compression over RGB with achromatic point = pixel max. -/
def gamutComp (limC limM limY thrC thrM thrY power : Float32) (invert : Bool)
    (px : Float32 × Float32 × Float32) : Float32 × Float32 × Float32 :=
  let (r0, g0, b0) := px
  let sc := gcScale limC thrC power
  let sm := gcScale limM thrM power
  let sy := gcScale limY thrY power
  let ach := fmaxf r0 (fmaxf g0 b0)
  (gcApply r0 ach thrC sc power invert,
   gcApply g0 ach thrM sm power invert,
   gcApply b0 ach thrY sy power invert)

/-- FixedFunction dispatch: apply one style with its params to RGB (alpha
  untouched). Mirrors `toc_fixedfunc_apply_pixel`. -/
def applyFixedFunc (style : FfStyle) (params : List Float32)
    (px : Float32 × Float32 × Float32) : Float32 × Float32 × Float32 :=
  let (r0, g0, b0) := px
  match style with
  | .linToPq => (pqEncode r0, pqEncode g0, pqEncode b0)
  | .pqToLin => (pqDecode r0, pqDecode g0, pqDecode b0)
  | .linToHlg => (hlgEncode r0, hlgEncode g0, hlgEncode b0)
  | .hlgToLin => (hlgDecode r0, hlgDecode g0, hlgDecode b0)
  | .rgbToHsv => rgbToHsv r0 g0 b0
  | .hsvToRgb => hsvToRgb r0 g0 b0
  | .xyzToXyY => xyzToXyy r0 g0 b0
  | .xyYToXyz => xyyToXyz r0 g0 b0
  | .xyzToUvY => xyzToUvy r0 g0 b0
  | .uvYToXyz => uvyToXyz r0 g0 b0
  | .xyzToLuv => xyzToLuv r0 g0 b0
  | .luvToXyz => luvToXyz r0 g0 b0
  | .acesGlow03 => applyGlowFwd r0 g0 b0 (params.getD 0 0.0) (params.getD 1 0.0)
  | .acesGlow03Inv => applyGlowInv r0 g0 b0 (params.getD 0 0.0) (params.getD 1 0.0)
  | .acesGlow10 => applyGlowFwd r0 g0 b0 (params.getD 0 0.0) (params.getD 1 0.0)
  | .acesGlow10Inv => applyGlowInv r0 g0 b0 (params.getD 0 0.0) (params.getD 1 0.0)
  | .acesRedMod03 => applyRedModFwd r0 g0 b0 0.85 0.03 1.9098593
  | .acesRedMod03Inv => applyRedModInv r0 g0 b0 0.85 0.03 1.9098593
  | .acesRedMod10 => applyRedModFwd r0 g0 b0 0.82 0.03 1.6976527
  | .acesRedMod10Inv => applyRedModInv r0 g0 b0 0.82 0.03 1.6976527
  | .acesDarkToDim10 => applyDarkToDim r0 g0 b0 0.27222871678091454 0.67408176581114831 0.053689517407937051 0.0000000001 (params.getD 0 0.0 - 1.0)
  | .acesDarkToDim10Inv => applyDarkToDim r0 g0 b0 0.27222871678091454 0.67408176581114831 0.053689517407937051 0.0000000001 (1.0 / params.getD 0 0.0 - 1.0)
  | .acesGamutComp13 =>
    let limC := params.getD 0 0.0
    let limM := params.getD 1 0.0
    let limY := params.getD 2 0.0
    let thrC := params.getD 3 0.0
    let thrM := params.getD 4 0.0
    let thrY := params.getD 5 0.0
    let power := params.getD 6 (3.0 : Float32)
    gamutComp limC limM limY thrC thrM thrY power false (r0, g0, b0)
  | .acesGamutComp13Inv =>
    let limC := params.getD 0 0.0
    let limM := params.getD 1 0.0
    let limY := params.getD 2 0.0
    let thrC := params.getD 3 0.0
    let thrM := params.getD 4 0.0
    let thrY := params.getD 5 0.0
    let power := params.getD 6 (3.0 : Float32)
    gamutComp limC limM limY thrC thrM thrY power true (r0, g0, b0)
  | .rec2100Surround => applySurround px (params.getD 0 (1.0 : Float32)) false
  | .rec2100SurroundInv => applySurround px (params.getD 0 (1.0 : Float32)) true

end Tocio
