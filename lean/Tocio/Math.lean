/-
  TinyEXR - Lean 4 formalization of the tocio vendored libm-free math
  (`sandbox/tocio/src/toc_math.c`).

  Faithful Float32 ports of `toc_log2f`, `toc_exp2f`, `toc_powf`,
  `toc_sqrtf`, `toc_raisef`, plus a bit-level float→int truncating
  conversion (`truncToIntF`) used by the exp2f rounding step (Lean
  core has no float→int cast, so it is decoded from `Float32` bits).
  All arithmetic is Float32 IEEE, matching the C `float` ops compiled
  with `-ffp-contract=off` (no FMA contraction).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

set_option linter.unusedVariables false

/-- Positive infinity bit pattern. -/
def infPos : Float32 := Float32.ofBits 0x7f800000

/-- Negative infinity bit pattern. -/
def infNeg : Float32 := Float32.ofBits 0xff800000

/-- Quiet NaN bit pattern. -/
def qNan : Float32 := Float32.ofBits 0x7fc00000

/-- Bit-level truncating float→int conversion (toward zero), for the
  `exp2f` rounding step. Domain here is |x| ≤ 128 (C guards larger
  values to Inf/0 before this runs); larger values saturate the same
  way a C int cast would observably differ — kept total regardless. -/
def truncToIntF (x : Float32) : Int :=
  let u := Float32.toBits x
  let sign := (u >>> 31) == 1
  let e := (u >>> 23) &&& 0xff
  let m := u &&& 0x7fffff
  let mag : Int :=
    if e < 127 then 0
    else
      let m' := (UInt32.ofNat 8388608 + m).toNat
      let se := (e - 127).toNat
      if se < 23 then Int.ofNat (m' >>> (23 - se))
      else Int.ofNat (m' <<< (se - 23))
  if sign then -mag else mag

/-- Convert a small Int (-128..127) back to the exactly-equal Float32
  via its bit pattern (used for the `exp2f` kernel offset). -/
def smallIntToF32 (i : Int) : Float32 :=
  if i == 0 then 0.0
  else
    let sign : UInt32 := if i < 0 then 0x80000000 else 0
    let a : Nat := if i < 0 then (-i).toNat else i.toNat
    let e : Nat := match (List.range 8).find? (fun k => a < (2 ^ (k + 1))) with
      | some k => k
      | none => 0
    let mant : UInt32 := UInt32.ofNat (a <<< (23 - e))
    let bits : UInt32 := sign ||| (UInt32.ofNat ((e + 127) <<< 23)) |||
      (mant &&& 0x7fffff)
    Float32.ofBits bits

/-- `toc_log2f`: 2–1 range polynomial (exact op sequence). -/
def log2f (x : Float32) : Float32 :=
  if x != x then x
  else if !(x > 0.0) then (if x < 0.0 then qNan else infNeg)
  else
    let u := Float32.toBits x
    let e : Int := Int.ofNat (((u >>> 23) &&& 0xff).toNat) - 127
    let mBits : UInt32 := (u &&& 0x007fffff) ||| 0x3f800000
    let m : Float32 := Float32.ofBits mBits
    let t : Float32 := (m - 1.0) / (m + 1.0)
    let t2 : Float32 := t * t
    let ln : Float32 := 2.0 * t *
      (1.0 + t2 * (1.0 / 3.0 +
                   t2 * (1.0 / 5.0 +
                         t2 * (1.0 / 7.0 + t2 * (1.0 / 9.0)))))
    smallIntToF32 e + ln * 1.4426950408889634

/-- `toc_exp2f`. -/
def exp2f (x : Float32) : Float32 :=
  if x != x then x
  else if x > 127.0 then infPos
  else if x < -126.0 then 0.0
  else
    let ki : Int := truncToIntF (if x >= 0.0 then x + 0.5 else x - 0.5)
    let k : Float32 := smallIntToF32 ki
    let f : Float32 := x - k
    let g : Float32 := f * 0.6931471805599453
    let p : Float32 := 1.0 +
      g * (1.0 +
        g * (0.5 +
          g * (1.0 / 6.0 +
            g * (1.0 / 24.0 +
              g * (1.0 / 120.0 + g * (1.0 / 720.0))))))
    let bits : UInt32 := UInt32.ofNat ((ki + 127).toNat <<< 23)
    p * Float32.ofBits bits

/-- `toc_powf`. -/
def powf (x y : Float32) : Float32 :=
  if !(x > 0.0) then
    if x == 0.0 then (if y > 0.0 then 0.0 else if y == 0.0 then 1.0 else infPos)
    else qNan
  else exp2f (y * log2f x)

/-- `toc_sqrtf`. -/
def sqrtf (x : Float32) : Float32 :=
  if x != x then x
  else if !(x > 0.0) then (if x < 0.0 then qNan else 0.0)
  else exp2f (0.5 * log2f x)

/-- `toc_raisef` (base^x with early-out for non-positive base). -/
def raisef (base x : Float32) : Float32 :=
  if !(base > 0.0) then 0.0
  else exp2f (x * log2f base)

/-- Number of significant bits in `n > 0` (`floor(log2 n) + 1`). -/
def bitLen (n : Nat) : Nat :=
  let rec go (fuel n k : Nat) : Nat :=
    match fuel with
    | 0 => k
    | fuel + 1 => if n == 0 then k else go fuel (n >>> 1) (k + 1)
  go 64 n 0

/-- Correctly-rounded IEEE-754 binary32 square root, on the raw bit pattern.

  Mirrors `toc_sqrtf_exact` in `sandbox/tocio/src/toc_math.c`: write
  `x = M * 2^s` with `M ∈ [2^23, 2^24)` (normalising subnormals), set
  `A = M` or `2M` so `s` halves exactly, take `S = isqrt(A << 38)`, and
  round the top 24 bits of `S` with one guard bit and an exact sticky bit
  (including `S*S != N`), i.e. round-to-nearest-even. This matches a
  hardware/libm `sqrtf` bit-for-bit for every input, including the
  signalling-NaN quieting and the negative-operand NaN. -/
def sqrtfExactBits (u0 : UInt32) : UInt32 :=
  let u := u0.toNat
  let sign := u >>> 31
  let expo := (u >>> 23) &&& 0xFF
  let mant := u &&& 0x7FFFFF
  if expo == 255 then
    if mant != 0 then UInt32.ofNat (u ||| 0x00400000)
    else if sign == 1 then UInt32.ofNat 0xFFC00000
    else UInt32.ofNat u
  else if u == 0 || u == 0x80000000 then UInt32.ofNat u
  else if sign == 1 then UInt32.ofNat 0xFFC00000
  else
    let (M, s) : Nat × Int :=
      if expo == 0 then
        let rec norm (fuel mm lz : Nat) : Nat × Nat :=
          match fuel with
          | 0 => (mm, lz)
          | fuel + 1 => if mm &&& 0x800000 != 0 then (mm, lz) else norm fuel (mm <<< 1) (lz + 1)
        let (mm, lz) := norm 24 mant 0
        (mm, -149 - (lz : Int))
      else (mant ||| 0x800000, (expo : Int) - 127 - 23)
    let (A, t) : Nat × Int :=
      if Int.emod s 2 != 0 then (M <<< 1, (s - 1) / 2) else (M, s / 2)
    let N : Nat := A <<< 38
    let S := Nat.sqrt N
    let d := bitLen S - 24
    let hi0 := S >>> d
    let roundBit := (S >>> (d - 1)) &&& 1
    let sticky := ((S &&& ((1 <<< (d - 1)) - 1)) != 0) || (S * S != N)
    let hi1 := if roundBit == 1 && (sticky || hi0 &&& 1 == 1) then hi0 + 1 else hi0
    let e0 : Int := (d : Int) + t + 4
    let (hi, e) : Nat × Int := if hi1 == (1 <<< 24) then (hi1 >>> 1, e0 + 1) else (hi1, e0)
    UInt32.ofNat ((((e + 127).toNat) <<< 23) ||| (hi &&& 0x7FFFFF))

/-- Correctly-rounded `sqrtf` (libm/hardware-identical). -/
def sqrtfExact (x : Float32) : Float32 := Float32.ofBits (sqrtfExactBits (Float32.toBits x))


end Tocio
