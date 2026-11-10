/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's endpoint solves and
  reconstruction scoring.

  Ports the scalar reference paths of `tc_div_round_s64`,
  `tc_astc_lsq_endpoints`, `tc_astc_lsq_endpoints_partition`,
  `tc_astc_eval_single_sse`, `tc_astc_eval_partition_sse`,
  `tc_astc_eval_dual_sse`, `tc_astc_block_has_rgb_clusters` and
  `tc_astc_partition_rgb_scale_ok` from
  `tools/texcomp/src/texcomp_astc.c`.

  The C side dispatches to SSE2/AVX2/NEON accumulation and reconstruction
  kernels; those are integer-exact copies of the scalar loops below, and
  the gate runs the C's normal runtime dispatch against these models.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcFits
import Texcomp.AstcColorQuant

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_div_round_s64`: rounded division, `den > 0`, symmetric around zero. -/
def astcDivRoundS64 (num den : Int) : Int :=
  let half := den / 2
  if num ≥ 0 then (num + half) / den else -(((-num) + half) / den)

/-- Accumulate the least-squares normal equations over the texels selected by
  `keep` (all when `none`). Returns `(saa, sab, sbb, sap, sbp)`. -/
def astcLsqSums (block : List (List Nat)) (count : Nat) (wt : List Nat)
    (keep : Option (Nat × List Nat)) :
    Int × Int × Int × List Int × List Int :=
  let step (acc : Int × Int × Int × List Int × List Int) (i : Nat) :=
    let use := match keep with
      | none => true
      | some (p, partOf) => partOf.getD i 0 == p
    if !use then acc
    else
      let a : Int := 64 - Int.ofNat (wt.getD i 0)
      let b : Int := Int.ofNat (wt.getD i 0)
      let row := block.getD i [0, 0, 0, 0]
      (acc.1 + a * a, acc.2.1 + a * b, acc.2.2.1 + b * b,
       (List.range 4).map (fun c => acc.2.2.2.1.getD c 0 + a * Int.ofNat (row.getD c 0)),
       (List.range 4).map (fun c => acc.2.2.2.2.getD c 0 + b * Int.ofNat (row.getD c 0)))
  (List.range count).foldl step (0, 0, 0, [0, 0, 0, 0], [0, 0, 0, 0])

/-- The 2x2 normal-equation solve shared by both endpoint fits. `none` when
  the system is degenerate. -/
def astcLsqSolve (block : List (List Nat)) (count : Nat) (wt : List Nat)
    (keep : Option (Nat × List Nat)) : Option (List Nat × List Nat) :=
  let (saa, sab, sbb, sap, sbp) := astcLsqSums block count wt keep
  let det := saa * sbb - sab * sab
  if det ≤ 0 then none
  else
    let cl := fun (x : Int) => if x < 0 then 0 else if x > 255 then 255 else x.toNat
    some ((List.range 4).map (fun c =>
            cl (astcDivRoundS64 ((sap.getD c 0 * sbb - sbp.getD c 0 * sab) * 64) det)),
          (List.range 4).map (fun c =>
            cl (astcDivRoundS64 ((sbp.getD c 0 * saa - sap.getD c 0 * sab) * 64) det)))

/-- `tc_astc_lsq_endpoints`. -/
def astcLsqEndpoints (block : List (List Nat)) (count : Nat) (wt : List Nat) :
    Option (List Nat × List Nat) :=
  astcLsqSolve block count wt none

/-- `tc_astc_lsq_endpoints_partition`. -/
def astcLsqEndpointsPartition (block : List (List Nat)) (count : Nat)
    (partOf : List Nat) (part : Nat) (wt : List Nat) :
    Option (List Nat × List Nat) :=
  astcLsqSolve block count wt (some (part, partOf))

/-- `tc_astc_eval_single_sse`: round-trip the endpoint pair through the colour
  quantiser with `endpoint_format` semantics, then score. -/
def astcEvalSingleSse (block : List (List Nat)) (count : Nat) (wt : List Nat)
    (endpointFormat qm : Nat) (lo hi : List Nat) : Nat :=
  let rt := fun (v : Nat) => colorRoundtrip qm v
  let (e0, e1) : List Nat × List Nat :=
    if endpointFormat == 0 then
      let g0 := rt (lo.getD 0 0)
      let g1 := rt (hi.getD 0 0)
      ([g0, g0, g0, 255], [g1, g1, g1, 255])
    else if endpointFormat == 4 then
      let g0 := rt (lo.getD 0 0)
      let g1 := rt (hi.getD 0 0)
      ([g0, g0, g0, rt (lo.getD 3 0)], [g1, g1, g1, rt (hi.getD 3 0)])
    else if endpointFormat == 6 || endpointFormat == 10 then
      let sumLo := lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0
      let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
      let scale0 := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
      let scale := rt (min scale0 255)
      let e1c := (List.range 3).map (fun c => rt (hi.getD c 0))
      let e0c := e1c.map (fun v => (v * scale) >>> 8)
      let (a0, a1) :=
        if endpointFormat == 10 then (rt (lo.getD 3 0), rt (hi.getD 3 0)) else (255, 255)
      (e0c ++ [a0], e1c ++ [a1])
    else
      let e0c := (List.range 3).map (fun c => rt (lo.getD c 0))
      let e1c := (List.range 3).map (fun c => rt (hi.getD c 0))
      let (a0, a1) :=
        if endpointFormat == 12 then (rt (lo.getD 3 0), rt (hi.getD 3 0)) else (255, 255)
      (e0c ++ [a0], e1c ++ [a1])
  astcReconSse block count e0 e1 wt

/-- `tc_astc_eval_partition_sse`: per-partition CEM semantics with shared
  weights. `none` is C's `UINT64_MAX` (a CEM 8/12 pair that would decode
  swapped). -/
def astcEvalPartitionSse (block : List (List Nat)) (count : Nat) (partOf : List Nat)
    (partitionCount : Nat) (formats : List Nat) (partLo partHi : List (List Nat))
    (qm : Nat) (wt : List Nat) : Option Nat :=
  let rt := fun (v : Nat) => colorRoundtrip qm v
  let e0s := (List.range partitionCount).map (fun p =>
    (List.range 4).map (fun c => (partLo.getD p []).getD c 0))
  let e1s := (List.range partitionCount).map (fun p =>
    (List.range 4).map (fun c => (partHi.getD p []).getD c 0))
  -- Compute the reconstructed endpoints per partition, bailing out on a
  -- swapped CEM 8/12 pair.
  let step (acc : Option (List (List Nat) × List (List Nat))) (p : Nat) :=
    match acc with
    | none => none
    | some (e0acc, e1acc) =>
      let form := formats.getD p 0
      let lo := e0s.getD p [0, 0, 0, 0]
      let hi := e1s.getD p [0, 0, 0, 0]
      if form == 6 || form == 10 then
        let sumLo := lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0
        let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
        let scale0 := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
        let scale := rt (min scale0 255)
        let e1c := (List.range 3).map (fun c => rt (hi.getD c 0))
        let e0c := e1c.map (fun v => (v * scale) >>> 8)
        let (a0, a1) :=
          if form == 10 then (rt (lo.getD 3 0), rt (hi.getD 3 0)) else (255, 255)
        some (e0acc ++ [e0c ++ [a0]], e1acc ++ [e1c ++ [a1]])
      else
        let e0c := (List.range 3).map (fun c => rt (lo.getD c 0))
        let e1c := (List.range 3).map (fun c => rt (hi.getD c 0))
        if e0c.foldl (· + ·) 0 > e1c.foldl (· + ·) 0 then none
        else
          let (a0, a1) :=
            if form == 12 then (rt (lo.getD 3 0), rt (hi.getD 3 0)) else (255, 255)
          some (e0acc ++ [e0c ++ [a0]], e1acc ++ [e1c ++ [a1]])
  match (List.range partitionCount).foldl step (some ([], [])) with
  | none => none
  | some (e0s2, e1s2) =>
    let e0t := (List.range count).map (fun i => e0s2.getD (partOf.getD i 0) [0, 0, 0, 0])
    let e1t := (List.range count).map (fun i => e1s2.getD (partOf.getD i 0) [0, 0, 0, 0])
    some (astcReconSsePt block count e0t e1t wt)

/-- `tc_astc_eval_dual_sse`: RGB uses the colour weights, alpha the alpha
  weights; CEM 10 only. -/
def astcEvalDualSse (block : List (List Nat)) (count : Nat) (wtc wta : List Nat)
    (endpointFormat qm : Nat) (lo hi : List Nat) : Nat :=
  let rt := fun (v : Nat) => colorRoundtrip qm v
  let (e0, e1) : List Nat × List Nat :=
    if endpointFormat == 10 then
      let sumLo := lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0
      let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
      let scale0 := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
      let scale := rt (min scale0 255)
      let e1c := (List.range 3).map (fun c => rt (hi.getD c 0))
      let e0c := e1c.map (fun v => (v * scale) >>> 8)
      (e0c ++ [rt (lo.getD 3 0)], e1c ++ [rt (hi.getD 3 0)])
    else
      (((List.range 3).map (fun c => rt (lo.getD c 0))) ++ [rt (lo.getD 3 0)],
       ((List.range 3).map (fun c => rt (hi.getD c 0))) ++ [rt (hi.getD 3 0)])
  (List.range count).foldl (fun (acc : Nat) i =>
    (List.range 4).foldl (fun (a : Nat) c =>
      let w := if c == 3 then wta.getD i 0 else wtc.getD i 0
      let recon := ((e0.getD c 0) * (64 - w) + (e1.getD c 0) * w + 32) >>> 6
      let d := Int.ofNat ((block.getD i [0, 0, 0, 0]).getD c 0) - Int.ofNat recon
      a + (d * d).toNat) acc) 0

/-- `tc_astc_block_has_rgb_clusters`: greedy 3-channel clustering with a
  4096 squared-distance radius. -/
def astcBlockHasRgbClusters (block : List (List Nat)) (count wanted : Nat) : Bool :=
  let step (st : List (List Nat) × Nat) (i : Nat) :=
    let (centers, clusterCount) := st
    let px := block.getD i [0, 0, 0, 0]
    let bestDist := (List.range clusterCount).foldl (fun (acc : Nat) c =>
      let ct := centers.getD c [0, 0, 0]
      let dr := Int.ofNat (px.getD 0 0) - Int.ofNat (ct.getD 0 0)
      let dg := Int.ofNat (px.getD 1 0) - Int.ofNat (ct.getD 1 0)
      let db := Int.ofNat (px.getD 2 0) - Int.ofNat (ct.getD 2 0)
      let dist := (dr * dr + dg * dg + db * db).toNat
      if dist < acc then dist else acc) 0xFFFFFFFF
    if clusterCount == 0 || bestDist > 4096 then
      if clusterCount ≥ wanted then (centers, clusterCount)
      else (centers ++ [[px.getD 0 0, px.getD 1 0, px.getD 2 0]], clusterCount + 1)
    else (centers, clusterCount)
  let (_, clusterCount) := (List.range count).foldl step ([], 0)
  clusterCount ≥ wanted

/-- `tc_astc_partition_rgb_scale_ok`: whether the CEM 6/10 scale transform can
  represent the pair within 24 code values. -/
def astcPartitionRgbScaleOk (lo hi : List Nat) : Bool :=
  -- `range` is a uint32 sum of the (possibly negative) channel differences,
  -- so an inverted channel wraps in C rather than truncating.
  let diff := fun (c : Nat) =>
    (Int.ofNat (hi.getD c 0) - Int.ofNat (lo.getD c 0)).emod 0x100000000
  let range := ((diff 0 + diff 1 + diff 2) % 0x100000000).toNat
  let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
  if range ≤ 24 then true
  else if sumHi == 0 then false
  else
    let scale0 := ((lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0) * 256 + sumHi / 2) / sumHi
    let scale := min scale0 255
    (List.range 3).all (fun c =>
      let recon := ((hi.getD c 0) * scale + 128) >>> 8
      let l := lo.getD c 0
      let diff := if recon > l then recon - l else l - recon
      diff ≤ 24)

end Texcomp
