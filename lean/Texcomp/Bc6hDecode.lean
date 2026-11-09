/-
  TinyEXR - Lean 4 formalization of BC6H decode (boundary).

  BC6H full decode (14 modes, FP16 endpoint unquantization, weight
  interpolation) is extremely complex and out of scope for this slice.
  This module provides the block size constant and a size/OOB safety
  theorem only. The actual decode is in the C implementation.

  Boundary: full BC6H decode is NOT yet formalized. This module is
  a placeholder for future work.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- BC6H block is 16 bytes. -/
def bc6hBlockBytes2 : Nat := 16

/-- Bytes needed for a BC6H image of w x h. -/
def bc6hImageBytes2 (w h : Nat) : Nat :=
  ((w + 3) / 4) * ((h + 3) / 4) * bc6hBlockBytes2

/-- OOB-safe: returns none if input too small. -/
def bc6hDecodeImage2 (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  if data.length < bc6hImageBytes2 w h then none else some data

/-- OOB safety theorem. -/
theorem bc6hDecodeImage2_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < bc6hImageBytes2 w h) :
    bc6hDecodeImage2 data w h = none := by
  unfold bc6hDecodeImage2
  simp [hsmall]

theorem bc6hBlockBytes2_pos : bc6hBlockBytes2 > 0 := by decide

end Texcomp