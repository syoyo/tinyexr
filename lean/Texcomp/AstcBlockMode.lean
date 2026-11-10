/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's block-mode parse.

  Ports `tc_astc_decode_block_mode_2d` from
  `tools/texcomp/src/texcomp_astc.c`, the *encoder-side* candidate filter:
  it is the same mode decode the block decoder uses, plus the encoder's
  weight-bit budget test (`24 <= weight_bits <= 96`) and the explicit
  weight-count cap. The decoder model (`Texcomp.decodeBlockMode`) applies
  the bit-budget test later in its own pipeline, so the two are kept
  separate.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

/-- Fields an admissible ASTC block mode carries for the encoder. -/
structure AstcEncMode where
  wx : Nat
  wy : Nat
  quant : Nat
  weightBits : Nat
  dual : Nat
  deriving Repr, DecidableEq

/-- `tc_astc_decode_block_mode_2d`: `none` for modes the encoder may not use. -/
def astcEncBlockMode (mode : Nat) : Option AstcEncMode :=
  let baseQuant0 := (mode >>> 4) &&& 1
  let h := (mode >>> 9) &&& 1
  let d := (mode >>> 10) &&& 1
  let a := (mode >>> 5) &&& 3
  let parsed : Option (Nat × Nat × Nat × Nat × Nat) :=
    if (mode &&& 3) != 0 then
      let baseQuant := baseQuant0 ||| ((mode &&& 3) <<< 1)
      let b := (mode >>> 7) &&& 3
      let (x, y) :=
        match (mode >>> 2) &&& 3 with
        | 0 => (b + 4, a + 2)
        | 1 => (b + 8, a + 2)
        | 2 => (a + 2, b + 8)
        | _ =>
          if mode &&& 0x100 != 0 then (b &&& 1 + 2, a + 2)
          else (a + 2, (b &&& 1) + 6)
      some (baseQuant, x, y, h, d)
    else
      let baseQuant := baseQuant0 ||| (((mode >>> 2) &&& 3) <<< 1)
      if ((mode >>> 2) &&& 3) == 0 then none
      else
        let b := (mode >>> 9) &&& 3
        match (mode >>> 7) &&& 3 with
        | 0 => some (baseQuant, 12, a + 2, h, d)
        | 1 => some (baseQuant, a + 2, 12, h, d)
        | 2 => some (baseQuant, a + 6, b + 6, 0, 0)
        | _ =>
          if a == 0 then some (baseQuant, 6, 10, h, d)
          else if a == 1 then some (baseQuant, 10, 6, h, d)
          else none
  match parsed with
  | none => none
  | some (baseQuant, x, y, h', d') =>
    if baseQuant < 2 then none
    else
      let quant := (baseQuant - 2) + 6 * h'
      if quant >= 12 then none
      else
        let count := x * y
        let real := count * (d' + 1)
        let bits := iseBitcount real quant
        if real > 64 || bits < 24 || bits > 96 then none
        else some ⟨x, y, quant, bits, d'⟩

end Texcomp
