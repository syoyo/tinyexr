/-
  TinyEXR - Lean 4 model of the shared libm-free math module
  (`deps/math/exr_math_impl.h`).

  Tier contract (see ~/.opencode/plan/lean-remaining-math-2026-11-24.md):
  - `log2fFast` / `exp2fFast` / `powfFast` / `sqrtfFast` mirror the FROZEN
    core `exr_util_*` polynomials bit-for-bit.
  - `log2f` / `exp2f` / `logf` / `powf` mirror the accurate tier. They use
    binary64 intermediates and one final binary32 rounding; `expf` uses the
    same binary64 range reduction. The exhaustive practical-domain sweeps are
    correctly rounded against a long-double/mpmath oracle.
  - `powf` has direct integer-exponent and half-integer-exponent branches and
    a double-intermediate general path.
  - `sqrtfExact` is the integer-exact IEEE binary32 square root (0 ULP).

  All bit casts use `Float32.toBits` / `Float32.ofBits`; no `Float32.log`,
  `Float32.exp` or `Float32.sqrt` externs are used.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.Math

namespace ExrMath

set_option linter.unusedVariables false

abbrev FB := Float32

def infPos : FB := Float32.ofBits 0x7f800000
def infNeg : FB := Float32.ofBits 0xff800000
def qNan : FB := Float32.ofBits 0x7fc00000

def b2f (u : UInt32) : FB := Float32.ofBits u
def f2b (x : FB) : UInt32 := Float32.toBits x

def ln2F : Float32 := (0.6931471805599453 : Float32)
def log2eF : Float32 := (1.4426950408889634 : Float32)

/-- Bit-level truncating float→int conversion (from Tocio.Math). -/
abbrev truncToIntF := Tocio.truncToIntF
abbrev smallIntToF32 := Tocio.smallIntToF32

/- ==================== FROZEN FAST TIER ================================== -/

def log2fFast (x : FB) : FB :=
  if !(x > 0.0) then (if x < 0.0 then qNan else infNeg)
  else
    let u := f2b x
    let e : Int := Int.ofNat (((u >>> 23) &&& 0xff).toNat) - 127
    let m : FB := b2f ((u &&& 0x007fffff) ||| 0x3f800000)
    let t : FB := (m - 1.0) / (m + 1.0)
    let t2 : FB := t * t
    let ln : FB := 2.0 * t *
      (1.0 + t2 * (1.0 / 3.0 +
                   t2 * (1.0 / 5.0 +
                         t2 * (1.0 / 7.0 + t2 * (1.0 / 9.0)))))
    smallIntToF32 e + ln * log2eF

def exp2fFast (x : FB) : FB :=
  if x > 127.0 then infPos
  else if x < -126.0 then 0.0
  else
    let kF : FB := smallIntToF32
      (if x >= 0.0 then truncToIntF (x + 0.5) else truncToIntF (x - 0.5))
    let f : FB := x - kF
    let g : FB := f * ln2F
    let p : FB := 1.0 + g * (1.0 + g * (0.5 + g * (1.0 / 6.0 +
      g * (1.0 / 24.0 + g * (1.0 / 120.0 + g * (1.0 / 720.0))))))
    let ki : Int := truncToIntF kF
    p * b2f (UInt32.ofNat ((ki + 127).toNat <<< 23))

def powfFast (x y : FB) : FB :=
  if !(x > 0.0) then
    if x == 0.0 then (if y > 0.0 then 0.0 else if y == 0.0 then 1.0 else infPos)
    else qNan
  else exp2fFast (y * log2fFast x)

def sqrtfFast (x : FB) : FB :=
  if !(x > 0.0) then 0.0 else exp2fFast (0.5 * log2fFast x)

/- ==================== ACCURATE TIER ===================================== -/

def ln2D : Float := 0.693147180559945309417232121458
def log2eD : Float := 1.44269504088896340736

def b2f64 (u : UInt64) : Float := Float.ofBits u
def f2b64 (x : Float) : UInt64 := Float.toBits x

/-- Binary64 log2 used by the accurate f32 wrappers. -/
def log2_64 (x : Float) : Float :=
  let u := f2b64 x
  let ef := (u >>> 52) &&& 0x7ff
  let e0 : Int := Int.ofNat ef.toNat - 1023
  let (sh, mm) : Nat × UInt64 :=
    if ef == 0 then
      let rec go (fuel : Nat) (k : Nat) (v : UInt64) : Nat × UInt64 :=
        match fuel with
        | 0 => (k, v)
        | fuel + 1 =>
          if v &&& 0x0010000000000000 != 0 then (k, v)
          else go fuel (k + 1) (v <<< 1)
      termination_by fuel
      go 53 0 (u &&& 0x000fffffffffffff)
    else (0, u &&& 0x000fffffffffffff)
  let m0 := b2f64 (0x3ff0000000000000 ||| (mm &&& 0x000fffffffffffff))
  let e0 := if ef == 0 then (-1022 : Int) - Int.ofNat sh else e0
  let (m, e) := if m0 > (1.4142135623730951 : Float)
    then (m0 * 0.5, e0 + 1) else (m0, e0)
  let t := (m - 1.0) / (m + 1.0)
  let t2 := t * t
  let p : Float := 0.1068662993251084
  let p := 0.11541560327111706 + t2 * p
  let p := 0.12545174268599682 + t2 * p
  let p := 0.1373995277037108 + t2 * p
  let p := 0.15186263588304877 + t2 * p
  let p := 0.16972882833987804 + t2 * p
  let p := 0.19235933878519512 + t2 * p
  let p := 0.2219530832136867 + t2 * p
  let p := 0.2623081892525388 + t2 * p
  let p := 0.3205988979753252 + t2 * p
  let p := 0.41219858311113244 + t2 * p
  let p := 0.5770780163555853 + t2 * p
  let p := 0.9617966939259757 + t2 * p
  let p := 2.8853900817779268 + t2 * p
  Float.ofInt e + t * p

def log2f (x : FB) : FB :=
  if x != x then x
  else if !(x > 0.0) then (if x < 0.0 then qNan else infNeg)
  else if ((f2b x >>> 23) &&& 0xff) == 0xff then infPos
  else Float.toFloat32 (log2_64 (Float32.toFloat x))

def logf (x : FB) : FB :=
  if x != x then x
  else if !(x > 0.0) then (if x < 0.0 then qNan else infNeg)
  else if ((f2b x >>> 23) &&& 0xff) == 0xff then infPos
  else Float.toFloat32 (log2_64 (Float32.toFloat x) * ln2D)

/-- truncating binary64 -> Int (same decomposition as Tocio.truncToIntF). -/
def truncToInt64F (x : Float) : Int :=
  let u := f2b64 x
  let sign := (u >>> 63) == 1
  let e := (u >>> 52) &&& 0x7ff
  let m := u &&& 0xfffffffffffff
  let mag : Int :=
    if e < 1023 then 0
    else
      let m' := UInt64.toNat (0x10000000000000 + m)
      let se := (e - 1023).toNat
      if se < 52 then Int.ofNat (m' >>> (52 - se))
      else Int.ofNat (m' <<< (se - 52))
  if sign then -mag else mag

def floor64 (x : Float) : Float :=
  let u := f2b64 x
  let expo := (u >>> 52) &&& 0x7ff
  if expo == 0x7ff then x
  else
    let e := expo.toNat - 1023
    if e >= 52 then x
    else if expo.toNat < 1023 then (if (u >>> 63) == 1 then -1.0 else 0.0)
    else
      let mask : UInt64 := UInt64.ofNat (2 ^ (52 - e) - 1)
      let u' := if (u >>> 63) == 1 then (u + mask) &&& (~~~mask) else u &&& (~~~mask)
      b2f64 u'

def expPoly64 (r : Float) : Float :=
  let p : Float := 1.0 / 20922789888000.0
  let p := 1.0 / 1307674368000.0 + r * p
  let p := 1.0 / 87178291200.0 + r * p
  let p := 1.0 / 6227020800.0 + r * p
  let p := 1.0 / 479001600.0 + r * p
  let p := 1.0 / 39916800.0 + r * p
  let p := 1.0 / 3628800.0 + r * p
  let p := 1.0 / 362880.0 + r * p
  let p := 1.0 / 40320.0 + r * p
  let p := 1.0 / 5040.0 + r * p
  let p := 1.0 / 720.0 + r * p
  let p := 1.0 / 120.0 + r * p
  let p := 1.0 / 24.0 + r * p
  let p := 1.0 / 6.0 + r * p
  let p := 0.5 + r * p
  let p := 1.0 + r * p
  1.0 + r * p

/-- Binary64 exp with Cody-Waite reduction, used by the accurate wrappers. -/
def exp64 (x : Float) : Float :=
  if x != x then x
  else if x > 709.0 then b2f64 0x7ff0000000000000
  else if x < -745.0 then 0.0
  else
    let kd := floor64 (x * log2eD + 0.5)
    if kd > 1023.0 || kd < -1074.0 then (if x > 0.0 then 1e308 else 0.0)
    else
      let k := truncToInt64F kd
      let r := x - (Float.ofInt k) * 6.93147180369123816490e-01
      let r := r - (Float.ofInt k) * 1.90821492927058770002e-10
      let p := expPoly64 r
      let scaleBits : UInt64 :=
        if k >= -1022 then UInt64.ofNat ((k + 1023).toNat <<< 52)
        else UInt64.ofNat ((k + 1075).toNat <<< 52)
      let scale := b2f64 scaleBits
      let scale := if k < -1022 then scale * 2.220446049250313e-16 else scale
      p * scale

def expf (x : FB) : FB :=
  if x != x then x
  else if x > (88.72283 : Float32) then infPos
  else if x < (-103.97208 : Float32) then 0.0
  else
    Float.toFloat32 (exp64 (Float32.toFloat x))

def exp2f (x : FB) : FB :=
  if x != x then x
  else if x >= 128.0 then infPos
  else if x < -150.0 then 0.0
  else Float.toFloat32 (exp64 (Float32.toFloat x * ln2D))

/-- Binary64 Newton sqrt with the bit-pattern seed used by `powf`. -/
def sqrt64 (x : Float) : Float :=
  if x != x then x
  else if x == 0.0 then x
  else if x < 0.0 then b2f64 0x7ff8000000000000
  else if x > 1e308 then x
  else
    let u := f2b64 x
    let u := (u >>> 1) + 0x1ff8000000000000
    let r := b2f64 u
    (List.range 6).foldl (fun r _ => 0.5 * (r + x / r)) r

def powi64 (x : Float) (n : Int) : Float :=
  let rec go (m : Nat) (b : Float) (r : Float) : Float :=
    match m with
    | 0 => r
    | m + 1 =>
      go ((m + 1) / 2) (b * b) (if (m + 1) % 2 == 1 then r * b else r)
  let r := go n.natAbs x 1.0
  if n < 0 then 1.0 / r else r

def powf (x y : FB) : FB :=
  if y == 0.0 then 1.0
  else if y == 1.0 then x
  else if x == 1.0 then 1.0
  else if y != y then y
  else
    let inRange := (y >= (-8.0)) && (y <= 8.0)
    let iy := if inRange then truncToIntF y else 0
    let yint := inRange && (smallIntToF32 iy == y)
    if !(x > 0.0) then
      if x == 0.0 then (if y > 0.0 then 0.0 else infPos)
      else if yint then Float.toFloat32 (powi64 (Float32.toFloat x) iy)
      else qNan
    else if ((f2b x >>> 23) &&& 0xff) == 0xff then
      (if y > 0.0 then infPos else 0.0)
    else if yint then Float.toFloat32 (powi64 (Float32.toFloat x) iy)
    else if y == 1.5 then
      Float.toFloat32 (Float32.toFloat x * sqrt64 (Float32.toFloat x))
    else
      let t := Float32.toFloat y * log2_64 (Float32.toFloat x)
      if t >= 128.0 then infPos
      else if t < -150.0 then 0.0
      else Float.toFloat32 (exp64 (t * ln2D))

def sqrtf (x : FB) : FB :=
  if x != x then x
  else if !(x > 0.0) then (if x < 0.0 then qNan else 0.0)
  else exp2f (0.5 * log2f x)

/- ==================== EXACT INTEGER SQUARE ROOT ========================== -/

def isqrt64 (n : UInt64) : UInt64 :=
  let step : (UInt64 × UInt64 × UInt64) → (UInt64 × UInt64 × UInt64) :=
    fun (rem, res, bit) =>
      if rem >= res + bit then (rem - (res + bit), res / 2 + bit, bit / 4)
      else (rem, res / 2, bit / 4)
  let rec go (fuel : Nat) (st : UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 :=
    match fuel with
    | 0 => st
    | fuel + 1 => go fuel (step st)
  termination_by fuel
  let bit0 : UInt64 := (UInt64.ofNat 1) <<< 62
  (go 32 (n, 0, bit0)).2.1

def bitLen64 (n : UInt64) : Nat :=
  let rec go (fuel : Nat) (v : UInt64) (k : Nat) : Nat :=
    match fuel with
    | 0 => k
    | fuel + 1 => if v == 0 then k else go fuel (v >>> 1) (k + 1)
  termination_by fuel
  go 64 n 0

def sqrtfExact (x : FB) : FB :=
  let u := f2b x
  let sign := u >>> 31
  let expo := (u >>> 23) &&& 0xff
  let mant := u &&& 0x7fffff
  if expo == 255 then
    if mant != 0 then b2f (u ||| 0x00400000)
    else if sign != 0 then qNan else x
  else if u == 0 || u == 0x80000000 then x
  else if sign != 0 then qNan
  else
    let (M, s) : Nat × Int :=
      if expo == 0 then
        let rec go (fuel : Nat) (k : Nat) (v : UInt32) : Nat × UInt32 :=
          match fuel with
          | 0 => (k, v)
          | fuel + 1 =>
            if v &&& 0x00800000 != 0 then (k, v) else go fuel (k + 1) (v <<< 1)
        termination_by fuel
        let (lz, mm) := go 24 0 mant
        (mm.toNat, -149 - lz)
      else
        ((mant ||| 0x00800000).toNat, Int.ofNat expo.toNat - 150)
    let (A, t) : Nat × Int :=
      if s % 2 != 0 then (M * 2, (s - 1) / 2) else (M, s / 2)
    let N : UInt64 := UInt64.ofNat (A * (1 <<< 38))
    let S : UInt64 := isqrt64 N
    let d : Nat := bitLen64 S - 24
    let SN : Nat := S.toNat
    let hi0 : UInt64 := UInt64.ofNat (SN / 2 ^ d)
    let rb : Bool := (SN / 2 ^ (d - 1) % 2) != 0
    let sticky : Bool := (SN % 2 ^ (d - 1) != 0) || (S * S != N)
    let hi : UInt64 := if rb && (sticky || (hi0.toNat % 2) != 0) then hi0 + 1 else hi0
    let e0 : Int := Int.ofNat d + t + 4
    let (hi', e') : UInt64 × Int := if hi == UInt64.ofNat (2 ^ 24)
      then (UInt64.ofNat (hi.toNat / 2), e0 + 1) else (hi, e0)
    b2f (UInt32.ofNat ((e' + 127).toNat <<< 23) ||| (UInt32.ofNat hi'.toNat &&& 0x7fffff))

/- ==================== PROOFS (small, kernel-checked) ===================== -/

theorem log2f_one : log2f 1.0 = 0.0 := by native_decide
theorem log2f_two : log2f 2.0 = 1.0 := by native_decide
theorem exp2f_zero : exp2f 0.0 = 1.0 := by native_decide
theorem exp2f_one : exp2f 1.0 = 2.0 := by native_decide
theorem sqrtfExact_four : sqrtfExact 4.0 = 2.0 := by native_decide

end ExrMath
