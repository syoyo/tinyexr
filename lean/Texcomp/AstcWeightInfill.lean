/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's weight infill.

  Ports the weight-quantisation LUT built in `tc_astc_ctx_init`
  (`wq_q`/`wq_wt`/`wq_err`), `tc_astc_infill_weights` (unquantise the
  weight grid, then a four-tap fixed-point blend per texel) and
  `tc_astc_infill_weights_grid` (same blend for an already-unquantised
  grid) from `tools/texcomp/src/texcomp_astc.c`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcDecim

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_quant_levels`: the number of quantisation levels per method. -/
def astcQuantLevels : List Nat :=
  [2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 160, 192, 256]

/-- `tc_astc_weight_unquant`'s table: quantised index → weight value. This is
  the *encoder's* value table; it differs from the decoder's
  `weightUnquant`, which is already in decoded-symbol order (the ISE symbol
  scramble is folded in there). -/
def astcWeightUnquantEnc : List (List Nat) :=
  [[0, 64],
   [0, 32, 64],
   [0, 21, 43, 64],
   [0, 16, 32, 48, 64],
   [0, 12, 25, 39, 52, 64],
   [0, 9, 18, 27, 37, 46, 55, 64],
   [0, 7, 14, 21, 28, 36, 43, 50, 57, 64],
   [0, 5, 11, 17, 23, 28, 36, 41, 47, 53, 59, 64],
   [0, 4, 8, 12, 17, 21, 25, 29, 35, 39, 43, 47, 52, 56, 60, 64],
   [0, 3, 6, 9, 13, 16, 19, 23, 26, 29, 35, 38, 41, 45, 48, 51, 55, 58, 61, 64],
   [0, 2, 5, 8, 11, 13, 16, 19, 22, 24, 27, 30, 34, 37, 40, 42, 45, 48, 51, 53,
    56, 59, 62, 64],
   [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 34, 36, 38, 40,
    42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64]]

/-- `wq_q`: ideal weight in `[0, 64]` → quantised index. -/
def astcWqQ (qm ideal : Nat) : Nat :=
  let maxq := astcQuantLevels.getD qm 2 - 1
  let q := (ideal * maxq + 32) / 64
  if q > maxq then maxq else q

/-- `wq_wt`: ideal weight → unquantised reconstruction. -/
def astcWqWt (qm ideal : Nat) : Nat :=
  (astcWeightUnquantEnc.getD qm []).getD (astcWqQ qm ideal) 0

/-- `wq_err`: squared error of the reconstruction, saturated at 16 bits. -/
def astcWqErr (qm ideal : Nat) : Nat :=
  let d := Int.ofNat (astcWqWt qm ideal) - Int.ofNat ideal
  min (d * d).toNat 0xFFFF

/-- The four-tap fixed-point blend shared by both infill entry points. -/
def astcInfillBlend (grid : List Nat) (taps : List (Nat × Nat)) : Nat :=
  (8 + taps.foldl (fun acc (q, w) => acc + (grid.getD q 0) * w) 0) >>> 4

/-- `tc_astc_infill_weights`: unquantise the quantised weight grid, then
  blend per texel. Takes the quantised weights (as the C encoder does). -/
def astcInfillWeights (weights : List Nat) (blockX blockY weightX weightY qm : Nat) :
    List Nat :=
  let count := blockX * blockY
  let (taps, _, direct) := astcDecimEntry blockX blockY weightX weightY
  let uq := astcWeightUnquantEnc.getD qm []
  if direct then
    (List.range count).map (fun i => uq.getD (weights.getD i 0) 0)
  else
    let grid := (List.range (weightX * weightY)).map (fun i =>
      uq.getD (weights.getD i 0) 0)
    (List.range count).map (fun i => astcInfillBlend grid (taps.getD i []))

/-- `tc_astc_infill_weights_grid`: the same blend on an already-unquantised
  weight grid. -/
def astcInfillWeightsGrid (grid : List Nat) (blockX blockY weightX weightY : Nat) :
    List Nat :=
  let count := blockX * blockY
  let (taps, _, _) := astcDecimEntry blockX blockY weightX weightY
  (List.range count).map (fun i => astcInfillBlend grid (taps.getD i []))

end Texcomp
