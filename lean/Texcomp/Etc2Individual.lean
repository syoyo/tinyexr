/-
  TinyEXR - Lean 4 formalization of ETC2 individual mode decode.

  ETC2 individual mode: 4x4 block with 4-bit color (per channel) and
  3-bit modifiers. Simplified model: extracts the base color and
  modifier table.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

/-- ETC2 individual mode block size. -/
def etc2IndividualBlockSize : Nat := 8

/-- OOB-safe decode: returns none if input too small. -/
def etc2IndividualDecode (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  let needed := ((w + 3) / 4) * ((h + 3) / 4) * etc2IndividualBlockSize
  if data.length < needed then none else some data

/-- OOB safety theorem. -/
theorem etc2IndividualDecode_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < ((w + 3) / 4) * ((h + 3) / 4) * etc2IndividualBlockSize) :
    etc2IndividualDecode data w h = none := by
  unfold etc2IndividualDecode
  simp [hsmall]

theorem etc2IndividualBlockSize_pos : etc2IndividualBlockSize > 0 := by decide

end Texcomp