/-
  TinyEXR - Lean 4 formalization of the ASTC partition RGB block encoder.

  Ports `tc_encode_astc_partition_rgb_block` from
  `tools/texcomp/src/texcomp_astc.c`. Uses the gated pack tail
  (`astcPackPartitionRgb`) for the final bit-packing.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEval
import Texcomp.AstcFits
import Texcomp.AstcPack
import Texcomp.AstcBlockMode
import Texcomp.AstcCandidates
import Texcomp.AstcEndpoints
import Texcomp.AstcColorQuant
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_encode_astc_partition_rgb_block`. Returns `some (bytes, err)` on
  success, `none` on any early-out. Quality selects the scoring path
  (<=1 batched, >1 per-candidate). -/
def astcEncodePartitionRgbBlock (block : List (List Nat)) (count partitionCount : Nat)
    (quality : Nat) (bx by_ : Nat) : Option (List Nat × Nat) :=
  let isOpaque := astcBlockIsOpaque block count
  let isLuminance := astcBlockIsLuminance block count
  let isRgbScale := astcBlockIsRgbScale block count
  -- cluster check for 3/4 partitions
  let clusterOk :=
    if partitionCount == 4 then astcBlockHasRgbClusters block count 4
    else if partitionCount == 3 then astcBlockHasRgbClusters block count 3
    else true
  if !clusterOk then none
  else if isLuminance then none
  else if !isOpaque && (partitionCount != 2 || count < 25) then none
  else
    match astcFindBestPartition block bx by_ partitionCount with
    | none => none
    | some (piIdx, accepted) =>
      if !accepted then none
      else
        let cache := astcBuildPartitionCache bx by_ partitionCount
        let piEntry := cache.getD piIdx (0, [], [], [])
        let piMap := piEntry.2.1
        let piSeed := piEntry.1
        -- part_lo / part_hi
        let partLo0 := (List.range partitionCount).map (fun _ => [255, 255, 255, 255])
        let partHi0 := (List.range partitionCount).map (fun _ => [0, 0, 0, 0])
        let partLo := (List.range count).foldl (fun (acc : List (List Nat)) i =>
          let part := piMap.getD i 0
          let row := block.getD i [0, 0, 0, 0]
          let cur := acc.getD part [255, 255, 255, 255]
          acc.set part ((List.range 4).map (fun c => min (cur.getD c 255) (row.getD c 0)))) partLo0
        let partHi := (List.range count).foldl (fun (acc : List (List Nat)) i =>
          let part := piMap.getD i 0
          let row := block.getD i [0, 0, 0, 0]
          let cur := acc.getD part [0, 0, 0, 0]
          acc.set part ((List.range 4).map (fun c => max (cur.getD c 0) (row.getD c 0)))) partHi0
        -- partition_project
        let (fitIdeal, fitActive, fitAllActive, fitE0t, fitE1t) :=
          astcPartitionProject block count piMap partLo partHi partitionCount (quality > 1)
        let endpointFormat0 := if partitionCount == 4 then 6 else 8
        -- candidates
        let candidates := astcBuildBlockModeCandidates bx by_ 29 quality
        if candidates.isEmpty then none
        else
          -- scoring
          let best := candidates.foldl (fun (st : Option (Nat × Nat × List Nat)) (ci : AstcEncMode) =>
            let (bestIdx, bestErr, bestWeights) := match st with
              | none => (0, 0xFFFFFFFFFFFFFFFF, [])
              | some (bi, be, bw) => (bi, be, bw)
            let colorBitsAvailable := 99 - ci.weightBits
            let endpointValuesPerPartition := if endpointFormat0 == 6 then 4 else 6
            let endpointValueCount := partitionCount * endpointValuesPerPartition
            match astcLutColorQuant endpointValueCount colorBitsAvailable with
            | none => st
            | some _ =>
              let decim := astcDecimEntry ci.wx ci.wy ci.wx ci.wy
              let weightCount := ci.wx * ci.wy
              let (candWeights, _) := astcWeightsFromIdeal ci.wx ci.wy ci.wx ci.wy
                ci.quant fitIdeal (if fitAllActive then none else some fitActive) count
              let err := astcFitFromIdealPt ci.wx ci.wy ci.wx ci.wy ci.quant count
                block fitIdeal (if fitAllActive then List.replicate count 1 else fitActive)
                (if quality > 1 then fitE0t else []) (if quality > 1 then fitE1t else [])
              if err < bestErr then
                some (ci.blockMode, err, candWeights)
              else st) (none : Option (Nat × Nat × List Nat))
          match best with
          | none => none
          | some (bestBlockMode, bestErr, bestWeights) =>
            let ci := candidates.find? (fun c => c.blockMode == bestBlockMode) |>.getD (candidates.getD 0 (AstcEncMode.mk 0 0 0 0 0 0))
            -- format selection
            let endpointFormat :=
              if isOpaque && (partitionCount == 2 || partitionCount == 3) then
                if astcBlockIsRgbScale block count then 10 else 12
              else endpointFormat0
            let scaleCount := if isOpaque && (partitionCount == 2 || partitionCount == 3) then
              (List.range partitionCount).foldl (fun acc p =>
                acc + (if astcPartitionRgbScaleOk (partLo.getD p [0,0,0,0]) (partHi.getD p [0,0,0,0]) then 1 else 0)) 0
              else 0
            let endpointFormatsMatched :=
              if isOpaque && (partitionCount == 2 || partitionCount == 3) then
                if scaleCount != 0 && scaleCount != partitionCount then 0 else 1
              else 1
            let endpointFormats := if endpointFormatsMatched == 0 then
              (List.range partitionCount).map (fun _ => endpointFormat0)
              else (List.range partitionCount).map (fun _ => endpointFormat)
            let endpointHighpartSize := if endpointFormatsMatched == 0 then 3 * partitionCount - 4 else 0
            let epvp := fun (f : Nat) =>
              if f == 6 then 4 else if f == 10 then 6 else if f == 12 then 8 else 6
            let endpointValueCount0 := (List.range partitionCount).foldl (fun acc p =>
              acc + epvp (endpointFormats.getD p endpointFormat)) 0
            let colorBitsAvailable := 99 - ci.weightBits - endpointHighpartSize
            let colorQuantMethodOpt := astcLutColorQuant endpointValueCount0 colorBitsAvailable
            let colorQuantMethodOpt := match colorQuantMethodOpt with
              | some m => some m
              | none => astcChooseColorQuant endpointValueCount0 colorBitsAvailable
            let (endpointFormats, endpointFormatsMatched, endpointHighpartSize, endpointValueCount, colorQuantMethod) :=
              match colorQuantMethodOpt with
              | some m => (endpointFormats, endpointFormatsMatched, endpointHighpartSize, endpointValueCount0, m)
              | none =>
                if endpointFormatsMatched == 0 then
                  let ef := (List.range partitionCount).map (fun _ => endpointFormat)
                  let efm := 1
                  let ehs := 0
                  let evc := partitionCount * epvp endpointFormat
                  let cba := 99 - ci.weightBits
                  let m := match astcLutColorQuant evc cba with
                    | some m => some m
                    | none => astcChooseColorQuant evc cba
                  match m with
                  | some m => (ef, efm, ehs, evc, m)
                  | none => (ef, efm, ehs, evc, 0)
                else
                  (endpointFormats, endpointFormatsMatched, endpointHighpartSize, endpointValueCount0, 0)
            if colorQuantMethod == 0 && !colorQuantSupported colorQuantMethod then none
            else
              -- per-partition LSQ refinement
              let decim := astcDecimEntry ci.wx ci.wy ci.wx ci.wy
              let weightCount := ci.wx * ci.wy
              let (weights, bestWt) := astcWeightsFromIdeal ci.wx ci.wy ci.wx ci.wy
                ci.quant fitIdeal (if fitAllActive then none else some fitActive) count
              let wt := bestWt
              let err := astcEvalPartitionSse block count piMap partitionCount endpointFormats
                partLo partHi colorQuantMethod wt
              let (partLo, partHi, err) := (partLo, partHi, err.getD bestErr)
              if err == 0xFFFFFFFFFFFFFFFF then none
              else
                let colorValues := astcEmitPartitionEndpointValues colorQuantMethod partitionCount endpointFormats partLo partHi
                let weightsScrambled := astcScrambleWeights weights weightCount ci.quant
                let weightbuf := List.replicate 16 0
                let (weightbuf, _) := astcIseEncodeBits ci.quant weightCount weightsScrambled weightbuf 0 16
                -- Use the gated pack tail
                let out := astcPackPartitionRgb ci.blockMode partitionCount piSeed
                  endpointFormatsMatched endpointFormats endpointHighpartSize
                  colorValues weightbuf colorQuantMethod endpointValueCount ci.weightBits
                some (out, err)

end Texcomp
