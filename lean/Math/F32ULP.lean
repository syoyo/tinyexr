/-
   TinyEXR - bit-distance (ULP) metric and exactness/witness theorems for the
   accurate libm-free math tier.

   The exhaustive normal-domain sweeps live in `test/v3/math_ulp.c`:
   `make math-ulp-full` checks all normal `log2f` inputs and all in-range
   `exp2f` inputs; `make math-pow-one-ulp` checks all positive normal inputs
   for `powf(x, 1)`.  This module pins the model's dyadic exactness and the
   worst-bit witnesses used to show why a uniform 16-ULP `powf(x,1)` bound is
   false.  The witnesses are native compilation checks, not universal bounds.

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
/-- `powf (2^n) 1` is exact on the full normal dyadic skeleton. -/
theorem powf_pow2_one_exact :
    (List.range 254).all (fun k =>
      bitDist (powf (b2f (pow2Bits k)) 1.0) (b2f (pow2Bits k)) = 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
/-- Exact worst-bit witness from the exhaustive normal-domain sweep: `log2f`
is 3 ULP from the libm reference at `0x3f351233`. -/
theorem log2f_3ulp_witness :
    bitDist (log2f (b2f 0x3f351233)) (b2f 0xbeffc9f2) = 3 := by
  native_decide

set_option maxHeartbeats 0 in
/-- Exact worst-bit witness from the exhaustive in-range sweep: `exp2f` is
1 ULP from the libm reference at `0x33b8aa3b`. -/
theorem exp2f_1ulp_witness :
    bitDist (exp2f (b2f 0x33b8aa3b)) (b2f 0x3f800001) = 1 := by
  native_decide

set_option maxHeartbeats 0 in
/-- Exact worst-bit witness from the exhaustive normal-domain sweep:
`powf x 1` is 44 ULP from `x` at the smallest normal binade. -/
theorem powf_one_44ulp_witness :
    bitDist (powf (b2f 0x00fafc0a) 1.0) (b2f 0x00fafc0a) = 44 := by
  native_decide

/-- A uniform 16-ULP bound for `powf x 1` over positive normals is false. -/
theorem powf_one_uniform_16_ulp_false :
    ¬ (∀ bits : UInt32,
        ((bits >>> 23) &&& 0xFF) ≠ 0 →
        bitDist (powf (b2f bits) 1.0) (b2f bits) ≤ 16) := by
  have h0 : bitDist (powf (b2f 0x00fafc0a) 1.0) (b2f 0x00fafc0a) = 44 := by
    native_decide
  intro h
  have hle := h 0x00fafc0a (by decide)
  rw [h0] at hle
  omega

end ExrMath
