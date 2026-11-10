/-
  TinyEXR - Lean 4 formalization of the ASTC const-colour block encoder.

  Ports `tc_encode_astc_const_block` / `tc_astc_write_const_from_sum`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

def astcWriteConstFromSum (sum : List Nat) (count : Nat) : List Nat :=
  [0xfc, 0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ++
    ((List.range 4).map (fun c =>
      let avg := (sum.getD c 0 + count / 2) / count
      let v16 := avg * 257
      [v16 % 256, v16 / 256])).flatten

def astcEncodeConstBlock (block : List (List Nat)) (count : Nat) : List Nat :=
  let sum := (List.range 4).map (fun c =>
    (List.range count).foldl (fun acc i => acc + (block.getD i [0,0,0,0]).getD c 0) 0)
  astcWriteConstFromSum sum count

end Texcomp
