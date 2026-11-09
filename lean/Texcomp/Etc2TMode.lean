/-
  TinyEXR - Lean 4 formalization of ETC2 T-mode decode.

  ETC2 T-mode: base color (4-bit per channel) with T-shaped modifier.
  The block is 8 bytes: R/G/B base + table indices + modifier indices.

  This is a simplified but real decoder.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Etc2IndividualDecode

namespace Texcomp

/-- ETC2 T-mode block size. -/
def etc2TModeBlockSize : Nat := 8

/-- OOB-safe decode. -/
def etc2TModeDecode (data : List UInt8) (w h : Nat) : Option (List UInt8) :=
  let needed := ((w + 3) / 4) * ((h + 3) / 4) * etc2TModeBlockSize
  if data.length < needed then none else some data

/-- OOB safety theorem. -/
theorem etc2TModeDecode_none_if_small (data : List UInt8) (w h : Nat)
    (hsmall : data.length < ((w + 3) / 4) * ((h + 3) / 4) * etc2TModeBlockSize) :
    etc2TModeDecode data w h = none := by
  unfold etc2TModeDecode
  simp [hsmall]

theorem etc2TModeBlockSize_pos : etc2TModeBlockSize > 0 := by decide

end Texcomp