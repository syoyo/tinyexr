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
import Texcomp.AstcScore
import Texcomp.AstcPack
import Texcomp.AstcBlockMode
import Texcomp.AstcCandidates
import Texcomp.AstcEndpoints
import Texcomp.AstcColorQuant
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch

namespace Texcomp

set_option linter.unusedVariables false

/-- Partition candidate budget check: the C skips candidates whose weight
  bits leave no room (`weight_bits >= 99`) or whose colour-quant LUT lookup
  fails. -/
def astcPartBudget (m : AstcEncMode) (evc : Nat) : Option Nat :=
  if m.weightBits ≥ 99 then none
  else astcLutColorQuant evc (99 - m.weightBits)

/-- Colour-quant level recorded on a positional best update: the C computes
  `99u - weight_bits` (which underflows to a huge budget for weight_bits >
  99, clamped to 111) and falls back to the identity quantizer when the LUT
  lookup fails. -/
def astcPartCqAt (cands : List AstcEncMode) (j evc : Nat) : Nat :=
  let m := cands.getD j (AstcEncMode.mk 0 0 0 0 0 0)
  let cba := if m.weightBits > 99 then 111 else 99 - m.weightBits
  (astcLutColorQuant evc cba).getD 20

/-- `tc_astc_get_decim_cache` returns non-NULL only for weight grids inside
  [2,12]; candidates outside would be skipped. -/
def astcPartDecimOk (wx wy : Nat) : Bool :=
  2 ≤ wx && wx ≤ 12 && 2 ≤ wy && wy ≤ 12

/-- Batch collection for the partition scan (`quality <= 1`, all-texel
  ideals): consecutive candidates sharing decimation entry and weight
  quantizer, while the scan budget has room. -/
def astcPartCollectLoop (cands : List AstcEncMode) (evc scanned scanCap : Nat)
    (group : Option (((Nat × Nat) × Nat))) (ci : Nat) (acc : List Nat) :
    List Nat × Nat :=
  if h1 : ci < cands.length then
    if scanned + acc.length < scanCap then
      let cand := cands.getD ci (AstcEncMode.mk 0 0 0 0 0 0)
      if (astcPartBudget cand evc).isNone ||
          !(astcPartDecimOk cand.wx cand.wy) then
        astcPartCollectLoop cands evc scanned scanCap group (ci + 1) acc
      else
        let key := ((cand.wx, cand.wy), cand.quant)
        match group with
        | none =>
          astcPartCollectLoop cands evc scanned scanCap (some key) (ci + 1) (acc ++ [ci])
        | some g =>
          if key == g then
            astcPartCollectLoop cands evc scanned scanCap group (ci + 1) (acc ++ [ci])
          else (acc, ci)
    else (acc, ci)
  else (acc, ci)
  termination_by cands.length - ci
  decreasing_by all_goals omega

/-- The partition candidate scan (`tc_encode_astc_partition_rgb_block`'s
  scoring loop, all three C branches). Returns the best candidate index
  (the C's possibly misattributed positional index) and its error. -/
def astcPartScanLoop
    (block : List (List Nat)) (count bx by_ evc quality scanCap : Nat)
    (cands : List AstcEncMode)
    (fitIdeal fitActive : List Nat) (fitAllActive : Bool)
    (fitE0t fitE1t : List (List Nat)) :
    Nat → Nat → Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0, _, _, best => best
  | f + 1, ci, scanned, best =>
    if ci < cands.length && scanned < scanCap then
      if quality > 1 then
        let m := cands.getD ci (AstcEncMode.mk 0 0 0 0 0 0)
        match astcPartBudget m evc with
        | none => astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f (ci + 1) scanned best
        | some _ =>
          let err := astcFitFromIdealPt bx by_ m.wx m.wy m.quant count
            block fitIdeal (if fitAllActive then List.replicate count 1 else fitActive)
            fitE0t fitE1t
          let best2 :=
            match best with
            | none => some (ci, err)
            | some (_, e) => if err < e then some (ci, err) else best
          astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f (ci + 1) (scanned + 1) best2
      else if fitAllActive then
        let batchStart := ci
        let (members, nextCi) :=
          astcPartCollectLoop cands evc scanned scanCap none ci []
        if members.isEmpty then
          astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f nextCi scanned best
        else
          let best2 := members.zipIdx.foldl
            (fun (b : Option (Nat × Nat)) p =>
              let (mc, bj) := p
              let cj := batchStart + bj
              let m := cands.getD mc (AstcEncMode.mk 0 0 0 0 0 0)
              let err := astcScoreFromIdeal bx by_ m.wx m.wy m.quant
                fitIdeal none count
              match b with
              | none => some (cj, err)
              | some (_, e) => if err < e then some (cj, err) else b)
            best
          astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f nextCi (scanned + members.length) best2
      else
        let m := cands.getD ci (AstcEncMode.mk 0 0 0 0 0 0)
        match astcPartBudget m evc with
        | none => astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f (ci + 1) scanned best
        | some _ =>
          let err := astcScoreFromIdeal bx by_ m.wx m.wy m.quant
            fitIdeal (some fitActive) count
          let best2 :=
            match best with
            | none => some (ci, err)
            | some (_, e) => if err < e then some (ci, err) else best
          astcPartScanLoop block count bx by_ evc quality scanCap
            cands fitIdeal fitActive fitAllActive fitE0t fitE1t
            f (ci + 1) (scanned + 1) best2
    else best

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
  -- the C builds the 3/4-partition caches only when ctx->quality > 1;
  -- with an empty cache `find_best_partition` always fails
  else if partitionCount != 2 && quality ≤ 1 then none
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
          -- scoring: quality > 1 scores candidates exactly with
          -- fit_from_ideal_pt; the reduced tiers use score_from_ideal,
          -- batched (all-texel ideals only) with the C's positional
          -- `batch_start + bj` indexing, or per-candidate with the active
          -- mask otherwise.
          let evcScan := partitionCount * (if endpointFormat0 == 6 then 4 else 6)
          let scanCap := if quality > 1 then candidates.length else 16
          let best := astcPartScanLoop block count bx by_ evcScan quality scanCap
            candidates fitIdeal fitActive fitAllActive fitE0t fitE1t
            (candidates.length + 1) 0 0 none
          match best with
          | none => none
          | some (bestIdx, bestErr) =>
            let ci := candidates.getD bestIdx (AstcEncMode.mk 0 0 0 0 0 0)
            -- format selection
            let endpointFormat :=
              if isOpaque then endpointFormat0
              else (if astcBlockIsRgbScale block count then 10 else 12)
            let scaleCount := if isOpaque && (partitionCount == 2 || partitionCount == 3) then
              (List.range partitionCount).foldl (fun acc p =>
                acc + (if astcPartitionRgbScaleOk (partLo.getD p [0,0,0,0]) (partHi.getD p [0,0,0,0]) then 1 else 0)) 0
              else 0
            let endpointFormatsMatched :=
              if isOpaque && (partitionCount == 2 || partitionCount == 3) then
                if scaleCount != 0 && scaleCount != partitionCount then 0 else 1
              else 1
            let endpointFormats := if endpointFormatsMatched == 0 then
              (List.range partitionCount).map (fun p =>
                if astcPartitionRgbScaleOk (partLo.getD p [0,0,0,0]) (partHi.getD p [0,0,0,0])
                then 6 else 8)
              else (List.range partitionCount).map (fun _ => endpointFormat)
            let endpointHighpartSize := if endpointFormatsMatched == 0 then 3 * partitionCount - 4 else 0
            let epvp := fun (f : Nat) =>
              if f == 6 then 4 else if f == 10 then 6 else if f == 12 then 8 else 6
            let endpointValueCount0 := (List.range partitionCount).foldl (fun acc p =>
              acc + epvp (endpointFormats.getD p endpointFormat)) 0
            -- C: with a positional best the weight bits can crowd out the
            -- endpoint highpart; unmatched formats are dropped then.
            let (endpointFormats, endpointFormatsMatched, endpointHighpartSize, endpointValueCount0) :=
              if ci.weightBits + endpointHighpartSize ≥ 99 then
                ((List.range partitionCount).map (fun _ => endpointFormat), 1, 0,
                  partitionCount * epvp endpointFormat)
              else (endpointFormats, endpointFormatsMatched, endpointHighpartSize,
                endpointValueCount0)
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
              let (weights, bestWt) := astcWeightsFromIdeal bx by_ ci.wx ci.wy
                ci.quant fitIdeal (if fitAllActive then none else some fitActive) count
              let wt := bestWt
              let initErr := (astcEvalPartitionSse block count piMap partitionCount endpointFormats
                partLo partHi colorQuantMethod wt).getD bestErr
              let (partLo, partHi, err) := (List.range partitionCount).foldl
                (fun (st : List (List Nat) × List (List Nat) × Nat) p =>
                  let (curLo, curHi, curErr) := st
                  let lsq := astcLsqEndpointsPartition block count piMap p wt
                  match lsq with
                  | none => st
                  | some (lsqLo, lsqHi) =>
                    let newLo := curLo.set p lsqLo
                    let newHi := curHi.set p lsqHi
                    let errLsq := astcEvalPartitionSse block count piMap partitionCount endpointFormats
                      newLo newHi colorQuantMethod wt
                    if errLsq.isSome && errLsq.getD 0 < curErr then
                      (newLo, newHi, errLsq.getD curErr)
                    else st) (partLo, partHi, initErr)
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
