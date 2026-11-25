/-
   TinyEXR - bit-distance (ULP) metric and exactness/witness theorems for the
   accurate libm-free math tier.

   The exhaustive normal-domain sweeps live in `test/v3/math_ulp.c`:
   `make math-ulp-full` checks all normal `log2f` inputs and all in-range
   `exp2f` inputs; `make math-pow-one-ulp` checks all positive normal inputs
   for `powf(x, 1)`.  This module pins the model's dyadic exactness and the
   direct `powf(x,1)=x` branch.  Executable exhaustive sweeps, not a universal
   analytic proof, provide the remaining correctly-rounded evidence.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Math.F32
import Mathlib.Tactic

namespace ExrMath

set_option linter.unusedVariables false

/-- Absolute distance between binary32 bit patterns.  On positive finite
values this is the usual ULP distance. -/
def bitDist (x y : FB) : Nat :=
  let a := (f2b x).toNat
  let b := (f2b y).toNat
  if a >= b then a - b else b - a

theorem bitDist_self (x : FB) : bitDist x x = 0 := by
  simp [bitDist]

theorem bitDist_comm (x y : FB) : bitDist x y = bitDist y x := by
  simp only [bitDist]
  split <;> split <;> omega

theorem bitDist_triangle (x y z : FB) :
    bitDist x z ≤ bitDist x y + bitDist y z := by
  simp only [bitDist]
  split <;> split <;> split <;> omega

/-- Bit pattern of the normal power of two with exponent field `k+1`. -/
def pow2Bits (k : Nat) : UInt32 := UInt32.ofNat ((k + 1) <<< 23)

/-- Integer represented by exponent field `k+1`. -/
def pow2Exp (k : Nat) : Int := Int.ofNat (k + 1) - 127

set_option maxHeartbeats 0 in
/-- `log2f` is exact on every normal power of two. -/
theorem log2f_pow2_exact :
    (List.range 254).all (fun k =>
      bitDist (log2f (b2f (pow2Bits k))) (smallIntToF32 (pow2Exp k)) = 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
/-- `exp2f` is exact on every integer exponent with a normal power-of-two
result. -/
theorem exp2f_int_exact :
    (List.range 254).all (fun k =>
      bitDist (exp2f (smallIntToF32 (pow2Exp k))) (b2f (pow2Bits k)) = 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
/-- The new accurate `powf` has a direct branch for exponent one. -/
theorem powf_one_eq (x : FB) : powf x 1.0 = x := by
  have h0 : ((1.0 : FB) == 0.0) = false := by decide
  have h1 : ((1.0 : FB) == 1.0) = true := by decide
  simp [powf, h0, h1]

/-- Consequently `powf (2^n) 1 = 2^n` on the full normal dyadic skeleton. -/
theorem powf_pow2_one_exact :
    (List.range 254).all (fun k =>
      bitDist (powf (b2f (pow2Bits k)) 1.0) (b2f (pow2Bits k)) = 0) = true := by
  simp [powf_one_eq, bitDist_self]

end ExrMath
