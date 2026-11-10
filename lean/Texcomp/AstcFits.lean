/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's weight/endpoint fits.

  Ports the scalar reference paths of `tc_luma_u8`, `tc_astc_axis_extremes`,
  `tc_astc_project_weight` / `TC_ASTC_PROJ_RECIP`,
  `tc_astc_partition_project`, `tc_astc_weight_scramble`,
  `tc_astc_scramble_weights`, `tc_astc_invert_weights`,
  `tc_astc_weights_from_ideal{,_pt}`, `tc_astc_fit_from_ideal{,_pt}`,
  `tc_astc_recon_sse{,_pt}` and `tc_astc_rgb_sse_from_stats` from
  `tools/texcomp/src/texcomp_astc.c` / `texcomp.c`.

  The SIMD reconstruction/accumulation kernels are bit-identical to these
  scalar loops by construction and are exercised by the same gate (the C
  side runs its normal runtime dispatch).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcWeightInfill

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_luma_u8`: the encoder's 38/76/14 luma key. -/
def astcLumaU8 (p : List Nat) : Nat :=
  p.getD 0 0 * 38 + p.getD 1 0 * 76 + p.getD 2 0 * 14

/-- `tc_astc_axis_extremes`: texel indices of the min/max key along an axis
  (0-3 channels, 4 = luma). First minimum wins, last maximum wins. -/
def astcAxisExtremes (block : List (List Nat)) (count axis : Nat) : Nat × Nat :=
  let key := fun (i : Nat) =>
    if axis < 4 then (block.getD i []).getD axis 0 else astcLumaU8 (block.getD i [])
  let step (st : Nat × Nat × Nat × Nat) (i : Nat) :=
    let k := key i
    let (loKey, loI, hiKey, hiI) := st
    let loI := if k < loKey then i else loI
    let loKey := if k < loKey then k else loKey
    let hiI := if k > hiKey then i else hiI
    let hiKey := if k > hiKey then k else hiKey
    (loKey, loI, hiKey, hiI)
  let (_, loI, _, hiI) := (List.range count).foldl step (0xFFFFFFFF, 0, 0, 0)
  (loI, hiI)

/-- `TC_ASTC_PROJ_RECIP`: fixed-point reciprocal. -/
def astcProjectRecip (d : Nat) : Nat := ((1 <<< 31) + d / 2) / d

/-- `tc_astc_project_weight`: fixed-point projection, clamped to 64. -/
def astcProjectWeight (dot64 recip : Nat) : Nat :=
  let w := (dot64 * recip + (1 <<< 30)) >>> 31
  if w > 64 then 64 else w

/-- `tc_astc_partition_project`: per-texel ideal weight onto the texel's own
  partition line, the `active` guard, and (optionally) the per-texel
  endpoint arrays. Returns
  `(ideal, active, allActive, e0t, e1t)`. -/
def astcPartitionProject (block : List (List Nat)) (count : Nat)
    (partOf : List Nat) (partLo partHi : List (List Nat)) (partitionCount : Nat)
    (wantEndpoints : Bool) :
    List Nat × List Nat × Bool × List (List Nat) × List (List Nat) :=
  -- `range = hi - lo` and the sum of squares are uint32 in C: when a
  -- channel's LSQ pair comes out inverted the difference (and its square)
  -- wraps. Keep the wraparound so the model matches the reference.
  let denom : List Nat := (List.range partitionCount).map (fun p =>
    (List.range 4).foldl (fun (acc : Nat) c =>
      let r := ((Int.ofNat ((partHi.getD p []).getD c 0) -
                 Int.ofNat ((partLo.getD p []).getD c 0)).emod 0x100000000).toNat
      (acc + (r * r) % 0x100000000) % 0x100000000) 0)
  let recip := denom.map (fun d => if d == 0 then 0 else astcProjectRecip d)
  let e0t :=
    if wantEndpoints then
      (List.range count).map (fun i =>
        (List.range 4).map (fun c => (partLo.getD (partOf.getD i 0) []).getD c 0))
    else []
  let e1t :=
    if wantEndpoints then
      (List.range count).map (fun i =>
        (List.range 4).map (fun c => (partHi.getD (partOf.getD i 0) []).getD c 0))
    else []
  let step (st : List Nat × List Nat × Bool) (i : Nat) :=
    let (ideal, active, allAct) := st
    let part := partOf.getD i 0
    if denom.getD part 0 == 0 then
      (ideal ++ [0], active ++ [0], false)
    else
      let px := block.getD i [0, 0, 0, 0]
      let dot : Int := (List.range 4).foldl (fun acc c =>
        let lo := Int.ofNat ((partLo.getD part []).getD c 0)
        acc + (Int.ofNat (px.getD c 0) - lo) *
              (Int.ofNat ((partHi.getD part []).getD c 0) - lo)) 0
      let idealI :=
        if dot ≤ 0 then 0
        else astcProjectWeight (dot.toNat * 64) (recip.getD part 0)
      (ideal ++ [idealI], active ++ [1], allAct)
  let (ideal, active, allAct) := (List.range count).foldl step ([], [], true)
  (ideal, active, allAct, e0t, e1t)

/-- `tc_astc_recon_sse_scalar`: interpolate a single endpoint pair. -/
def astcReconSse (block : List (List Nat)) (count : Nat) (e0 e1 : List Nat)
    (wt : List Nat) : Nat :=
  (List.range count).foldl (fun (acc : Nat) i =>
    let w := wt.getD i 0
    (List.range 4).foldl (fun (a : Nat) c =>
      let recon := ((e0.getD c 0) * (64 - w) + (e1.getD c 0) * w + 32) >>> 6
      let d := Int.ofNat ((block.getD i [0, 0, 0, 0]).getD c 0) - Int.ofNat recon
      a + (d * d).toNat) acc) 0

/-- `tc_astc_recon_sse_pt_scalar`: per-texel endpoint pairs. -/
def astcReconSsePt (block : List (List Nat)) (count : Nat)
    (e0t e1t : List (List Nat)) (wt : List Nat) : Nat :=
  (List.range count).foldl (fun (acc : Nat) i =>
    let w := wt.getD i 0
    let a0 := e0t.getD i [0, 0, 0, 0]
    let a1 := e1t.getD i [0, 0, 0, 0]
    (List.range 4).foldl (fun (a : Nat) c =>
      let recon := ((a0.getD c 0) * (64 - w) + (a1.getD c 0) * w + 32) >>> 6
      let d := Int.ofNat ((block.getD i [0, 0, 0, 0]).getD c 0) - Int.ofNat recon
      a + (d * d).toNat) acc) 0

/-- `tc_astc_weight_scramble` (table form). -/
def astcWeightScrambleTable : List (List Nat) :=
  [[0, 1],
   [0, 1, 2],
   [0, 1, 2, 3],
   [0, 1, 2, 3, 4],
   [0, 2, 4, 5, 3, 1],
   [0, 1, 2, 3, 4, 5, 6, 7],
   [0, 2, 4, 6, 8, 9, 7, 5, 3, 1],
   [0, 4, 8, 2, 6, 10, 11, 7, 3, 9, 5, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [0, 4, 8, 12, 16, 2, 6, 10, 14, 18, 19, 15, 11, 7, 3, 17, 13, 9, 5, 1],
   [0, 8, 16, 2, 10, 18, 4, 12, 20, 6, 14, 22, 23, 15, 7, 21, 13, 5, 19, 11, 3,
    17, 9, 1],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]

/-- `tc_astc_weight_scramble`. -/
def astcWeightScramble (q quantMethod : Nat) : Nat :=
  (astcWeightScrambleTable.getD quantMethod []).getD q 0

/-- `tc_astc_scramble_weights`. -/
def astcScrambleWeights (weights : List Nat) (count qm : Nat) : List Nat :=
  (List.range count).map (fun i => astcWeightScramble (weights.getD i 0) qm)

/-- `tc_astc_invert_weights`. -/
def astcInvertWeights (weights : List Nat) (count qm : Nat) : List Nat :=
  let maxq := astcQuantLevels.getD qm 2 - 1
  (List.range count).map (fun i => maxq - weights.getD i 0)

/-- `tc_astc_weights_from_ideal`: quantise the hoisted ideal weights onto a
  candidate grid. With `active = none` every texel constrains the grid (the
  `tc_astc_weights_from_ideal` path); with `some flags` only flagged texels
  do (`tc_astc_weights_from_ideal_pt`). Returns `(out_weights, wt)`. -/
def astcWeightsFromIdeal (blockX blockY weightX weightY qm : Nat)
    (ideal : List Nat) (active : Option (List Nat)) (count : Nat) :
    List Nat × List Nat :=
  let (taps, entryContribs, direct) := astcDecimEntry blockX blockY weightX weightY
  let weightCount := weightX * weightY
  if direct then
    ((List.range count).map (fun i => astcWqQ qm (ideal.getD i 0)),
     (List.range count).map (fun i => astcWqWt qm (ideal.getD i 0)))
  else
    let (accum, contrib) := (List.range count).foldl
      (fun (st : List Nat × List Nat) i =>
        let use := match active with
          | none => true
          | some a => a.getD i 0 != 0
        if !use then st
        else
          (taps.getD i []).foldl (fun (s : List Nat × List Nat) (q, w) =>
            (s.1.set q (s.1.getD q 0 + ideal.getD i 0 * w),
             s.2.set q (s.2.getD q 0 + w))) st)
      ((List.range weightCount).map (fun _ => 0), (List.range weightCount).map (fun _ => 0))
    let contribs := match active with
      | none => entryContribs
      | some _ => contrib
    let v := (List.range weightCount).map (fun k =>
      let c := contribs.getD k 0
      if c == 0 then 0 else (accum.getD k 0 + c / 2) / c)
    (v.map (astcWqQ qm), astcInfillWeightsGrid (v.map (astcWqWt qm)) blockX blockY weightX weightY)

/-- `tc_astc_fit_from_ideal`. -/
def astcFitFromIdeal (blockX blockY weightX weightY qm count : Nat)
    (block : List (List Nat)) (ideal : List Nat) (lo hi : List Nat) : Nat :=
  let (_, wt) := astcWeightsFromIdeal blockX blockY weightX weightY qm ideal none count
  astcReconSse block count lo hi wt

/-- `tc_astc_fit_from_ideal_pt`. -/
def astcFitFromIdealPt (blockX blockY weightX weightY qm count : Nat)
    (block : List (List Nat)) (ideal active : List Nat)
    (e0t e1t : List (List Nat)) : Nat :=
  let (_, wt) := astcWeightsFromIdeal blockX blockY weightX weightY qm ideal
    (some active) count
  astcReconSsePt block count e0t e1t wt

/-- `tc_astc_rgb_sse_from_stats`. -/
def astcRgbSseFromStats (sum sumsq : List Nat) (count : Nat) : Option Nat :=
  if count == 0 then none
  else
    some ((List.range 3).foldl (fun acc c =>
      let s := sum.getD c 0
      acc + (sumsq.getD c 0 - (s * s + count / 2) / count)) 0)

end Texcomp
