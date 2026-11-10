/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's endpoint plumbing.

  Ports `tc_astc_partition_endpoint_type_code`,
  `tc_astc_partition_endpoint_value_count`,
  `tc_astc_emit_partition_endpoint_values`, `tc_astc_choose_color_quant`,
  the `color_quant_lut` built in `tc_astc_ctx_init` and
  `tc_astc_lut_color_quant` from `tools/texcomp/src/texcomp_astc.c`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcColorQuant
import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_partition_endpoint_type_code`: the packed 6-bit-ish endpoint
  type field. Note the C folds class 3 down to class 2 before encoding. -/
def astcPartitionEndpointTypeCode (partitionCount : Nat) (formats : List Nat) : Nat :=
  let classes := (List.range partitionCount).map (fun i => (formats.getD i 0) >>> 2)
  let lowClass :=
    let m := classes.foldl (fun (acc : Nat) c => if c < acc then c else acc) 4
    if m == 3 then 2 else m
  let encoded0 := lowClass + 1
  let (a1, p1) := (List.range partitionCount).foldl (fun (acc : Nat × Nat) i =>
    let c := classes.getD i 0
    (acc.1 ||| ((c - lowClass) <<< acc.2), acc.2 + 1)) (encoded0, 2)
  (List.range partitionCount).foldl (fun (acc : Nat × Nat) i =>
    let f := formats.getD i 0
    (acc.1 ||| ((f &&& 3) <<< acc.2), acc.2 + 2)) (a1, p1) |>.1

/-- `tc_astc_partition_endpoint_value_count`. -/
def astcPartitionEndpointValueCount (partitionCount : Nat) (formats : List Nat) : Nat :=
  (List.range partitionCount).foldl (fun acc i =>
    acc + ((((formats.getD i 0) >>> 2) + 1) * 2)) 0

/-- `tc_astc_choose_color_quant`: the highest supported quant method whose
  ISE bit count fits the budget, scanning 20 down to 4. -/
def astcChooseColorQuant (valueCount bitBudget : Nat) : Option Nat :=
  let step (acc : Option Nat) (k : Nat) :=
    match acc with
    | some _ => acc
    | none =>
      let qm := 20 - k
      if !colorQuantSupported qm then none
      else if iseBitcount valueCount qm ≤ bitBudget then some qm else none
  (List.range 17).foldl step none

/-- The `color_quant_lut[value_count][bit_budget]` table (0xFF = none). -/
def astcColorQuantLut (valueCount bitBudget : Nat) : Nat :=
  match astcChooseColorQuant valueCount bitBudget with
  | some qm => qm
  | none => 0xFF

/-- `tc_astc_lut_color_quant` (budget clamped to 111). -/
def astcLutColorQuant (valueCount bitBudget : Nat) : Option Nat :=
  let b := min bitBudget 111
  if valueCount ≥ 1 && valueCount < 19 then
    let m := astcColorQuantLut valueCount b
    if m == 0xFF then none else some m
  else none

/-- `tc_astc_emit_partition_endpoint_values`: per-partition quantised colour
  symbols, in the C's format-dependent order. -/
def astcEmitPartitionEndpointValues (quantMethod partitionCount : Nat)
    (formats : List Nat) (partLo partHi : List (List Nat)) : List Nat :=
  let emit (acc : List Nat) (v : Nat) := acc ++ [colorPquantLut quantMethod v]
  (List.range partitionCount).foldl (fun (acc : List Nat) i =>
    let form := formats.getD i 0
    let lo := partLo.getD i [0, 0, 0, 0]
    let hi := partHi.getD i [0, 0, 0, 0]
    let sumLo := lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0
    let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
    let scale0 := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
    let scale := min scale0 255
    if form == 6 then
      emit (emit (emit (emit acc (hi.getD 0 0)) (hi.getD 1 0)) (hi.getD 2 0)) scale
    else if form == 10 then
      emit (emit (emit (emit (emit (emit acc (hi.getD 0 0)) (hi.getD 1 0))
        (hi.getD 2 0)) scale) (lo.getD 3 0)) (hi.getD 3 0)
    else if form == 12 then
      (List.range 4).foldl (fun a c => emit (emit a (lo.getD c 0)) (hi.getD c 0)) acc
    else
      emit (emit (emit (emit (emit (emit acc (lo.getD 0 0)) (hi.getD 0 0))
        (lo.getD 1 0)) (hi.getD 1 0)) (lo.getD 2 0)) (hi.getD 2 0)) []

end Texcomp
