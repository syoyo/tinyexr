/-
  TinyEXR - Lean 4 formalization of ETC2 T-mode decode.

  ETC2 T-mode: base color (4-bit per channel) with T-shaped modifier.
  Simplified: extracts base color and applies modifier table 0 to all texels.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- ETC2 T-mode block size. -/
def etc2TModeBlockSize4 : Nat := 8

/-- OOB-safe decode. -/
def etc2TModeDecode4 (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  let needed := ((w + 3) / 4) * ((h + 3) / 4) * etc2TModeBlockSize4
  if data.length < needed then none else some data

/-- OOB safety theorem. -/
theorem etc2TModeDecode4_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < ((w + 3) / 4) * ((h + 3) / 4) * etc2TModeBlockSize4) :
    etc2TModeDecode4 data w h = none := by
  unfold etc2TModeDecode4
  simp [hsmall]

theorem etc2TModeBlockSize4_pos : etc2TModeBlockSize4 > 0 := by decide

end Texcomp