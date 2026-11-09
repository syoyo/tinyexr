/-
  TinyEXR - Lean 4 formalization of the tocio LUT ops.

  First slice: 1D LUT linear interpolation and 3D LUT trilinear interpolation
  (scalar). Full op lowering and codegen come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- 1D LUT linear interpolation. -/
def lut1dLinear (data : Nat → Float) (n : Nat) (domainMin domainMax x : Float) : Float :=
  if n = 0 then 0.0
  else
    let t := (x - domainMin) / (domainMax - domainMin)
    let idx := t * (Float.ofNat (n - 1))
    let i0 := if idx < 0.0 then 0 else if idx.toUInt64.toNat ≥ n - 1 then n - 2 else idx.toUInt64.toNat
    let frac := idx - Float.ofNat i0
    data i0 * (1.0 - frac) + data (i0 + 1) * frac

/-- Clamp a float to [0,1]. -/
def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

end Tocio