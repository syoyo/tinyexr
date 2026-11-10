/-
  TinyEXR - Lean 4 formalization of the ASTC dual RGBA block encoder.

  Ports `tc_encode_astc_dual_rgba_block` from
  `tools/texcomp/src/texcomp_astc.c`.

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
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_encode_astc_dual_rgba_block`. -/
def astcEncodeDualRgbaBlock (block : List (List Nat)) (count : Nat)
    (quality : Nat) (bx by_ : Nat) : Option (List Nat × Nat) :=
  let isOpaque := astcBlockIsOpaque block count
  let isLuminance := astcBlockIsLuminance block count
  let isRgbScale := astcBlockIsRgbScale block count
  -- Early outs
  if quality < 1 then none
  else if isOpaque then none
  else if isLuminance then none
  else if quality < 2 && isRgbScale then none
  else
    let endpointFormat := if isRgbScale then 10 else 12
    let endpointValueCount := if isRgbScale then 6 else 8
    -- alpha range check
    let alphaMin := (List.range count).foldl (fun acc i => min acc ((block.getD i [0,0,0,0]).getD 3 0)) 255
    let alphaMax := (List.range count).foldl (fun acc i => max acc ((block.getD i [0,0,0,0]).getD 3 0)) 0
    if alphaMax - alphaMin < 48 then none
    else
      -- axis extremes
      let (lumaLoI, lumaHiI) := astcAxisExtremes block count 4
      let (alphaLoI, alphaHiI) := astcAxisExtremes block count 3
      -- axis line
      let (lineColorLo, lineColorHi, colorRecip, colorOk) := astcAxisLine block lumaLoI lumaHiI
      let (lineAlphaLo, lineAlphaHi, alphaRecip, alphaOk) := astcAxisLine block alphaLoI alphaHiI
      if !colorOk || !alphaOk then none
      else
        -- project ideal
        let colorIdeal := astcProjectIdeal block count lineColorLo lineColorHi colorRecip
        let alphaIdeal := astcProjectIdeal block count lineAlphaLo lineAlphaHi alphaRecip
        -- candidates
        let candidates := astcBuildDualBlockModeCandidates bx by_ 17 quality
        if candidates.isEmpty then none
        else
          -- candidate search
          let best := candidates.foldl (fun (st : Option (Nat × Nat × List Nat × List Nat)) (ci : AstcEncMode) =>
            let (bestIdx, bestErr, bestColorW, bestAlphaW) := match st with
              | none => (0, 0xFFFFFFFFFFFFFFFF, [], [])
              | some (bi, be, bcw, baw) => (bi, be, bcw, baw)
            let colorBitsAvailable := 109 - ci.weightBits
            if ci.weightBits >= 109 then st
            else
              match astcLutColorQuant endpointValueCount colorBitsAvailable with
              | none => st
              | some candColorQuant =>
                let decim := astcDecimEntry bx by_ ci.wx ci.wy
                let weightCount := ci.wx * ci.wy
                let colorErr := astcFitFromIdeal bx by_ ci.wx ci.wy ci.quant count block colorIdeal lineColorLo lineColorHi
                let alphaErr := astcFitFromIdeal bx by_ ci.wx ci.wy ci.quant count block alphaIdeal lineAlphaLo lineAlphaHi
                let err := colorErr + alphaErr
                if err < bestErr then
                  let (candColorWeights, _) := astcWeightsFromIdeal bx by_ ci.wx ci.wy ci.quant colorIdeal none count
                  let (candAlphaWeights, _) := astcWeightsFromIdeal bx by_ ci.wx ci.wy ci.quant alphaIdeal none count
                  some (ci.blockMode, err, candColorWeights.take weightCount, candAlphaWeights.take weightCount)
                else st) (none : Option (Nat × Nat × List Nat × List Nat))
          match best with
          | none => none
          | some (bestBlockMode, bestErr, bestColorW, bestAlphaW) =>
            let ci := candidates.find? (fun c => AstcEncMode.blockMode c == bestBlockMode) |>.getD (candidates.getD 0 (AstcEncMode.mk 0 0 0 0 0 0))
            -- color quant method
            let colorBitsAvailable := 109 - ci.weightBits
            match astcLutColorQuant endpointValueCount colorBitsAvailable with
            | none => none
            | some colorQuantMethod =>
              -- copy endpoints
              let colorLo := lineColorLo
              let colorHi := lineColorHi
              let alphaLo := lineAlphaLo
              let alphaHi := lineAlphaHi
              -- infill weights
              let bd := astcDecimEntry bx by_ ci.wx ci.wy
              let wtc := astcInfillWeights bestColorW bx by_ ci.wx ci.wy ci.quant
              let wta := astcInfillWeights bestAlphaW bx by_ ci.wx ci.wy ci.quant
              -- cur endpoints
              let cur0 := (List.range 4).map (fun c => if c == 3 then alphaLo.getD 3 0 else colorLo.getD c 0)
              let cur1 := (List.range 4).map (fun c => if c == 3 then alphaHi.getD 3 0 else colorHi.getD c 0)
              -- eval dual sse
              let err := astcEvalDualSse block count wtc wta endpointFormat colorQuantMethod cur0 cur1
              -- LSQ refinement: color plane
              let (colorLo, colorHi, cur0, cur1, err) :=
                match astcLsqEndpoints block count wtc with
                | none => (colorLo, colorHi, cur0, cur1, err)
                | some (lsqLo, lsqHi) =>
                  let tryLo := (List.range 3).map (fun c => lsqLo.getD c 0) ++ [cur0.getD 3 0]
                  let tryHi := (List.range 3).map (fun c => lsqHi.getD c 0) ++ [cur1.getD 3 0]
                  let lsqErr := astcEvalDualSse block count wtc wta endpointFormat colorQuantMethod tryLo tryHi
                  if lsqErr < err then
                    let newColorLo := (List.range 3).map (fun c => tryLo.getD c 0)
                    let newColorHi := (List.range 3).map (fun c => tryHi.getD c 0)
                    (newColorLo, newColorHi, tryLo, tryHi, lsqErr)
                  else (colorLo, colorHi, cur0, cur1, err)
              -- LSQ refinement: alpha plane
              let (alphaLo, alphaHi, err) :=
                match astcLsqEndpoints block count wta with
                | none => (alphaLo, alphaHi, err)
                | some (lsqLo, lsqHi) =>
                  let tryLo := cur0.set 3 (lsqLo.getD 3 0)
                  let tryHi := cur1.set 3 (lsqHi.getD 3 0)
                  let lsqErr := astcEvalDualSse block count wtc wta endpointFormat colorQuantMethod tryLo tryHi
                  if lsqErr < err then
                    (alphaLo.set 3 (tryLo.getD 3 0), alphaHi.set 3 (tryHi.getD 3 0), lsqErr)
                  else (alphaLo, alphaHi, err)
              -- emit values
              let values :=
                if endpointFormat == 10 then
                  let sumLo := colorLo.getD 0 0 + colorLo.getD 1 0 + colorLo.getD 2 0
                  let sumHi := colorHi.getD 0 0 + colorHi.getD 1 0 + colorHi.getD 2 0
                  let scale := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
                  let scale := if scale > 255 then 255 else scale
                  [colorHi.getD 0 0, colorHi.getD 1 0, colorHi.getD 2 0, scale,
                   alphaLo.getD 3 0, alphaHi.getD 3 0]
                else
                  [colorLo.getD 0 0, colorHi.getD 0 0, colorLo.getD 1 0, colorHi.getD 1 0,
                   colorLo.getD 2 0, colorHi.getD 2 0, alphaLo.getD 3 0, alphaHi.getD 3 0]
              -- CEM 12 ordering check
              let (values, colorWeights, alphaWeights) :=
                if endpointFormat == 12 then
                  let sLo := (List.range 3).foldl (fun acc c => acc + colorRoundtrip colorQuantMethod (values.getD (c * 2) 0)) 0
                  let sHi := (List.range 3).foldl (fun acc c => acc + colorRoundtrip colorQuantMethod (values.getD (c * 2 + 1) 0)) 0
                  if sLo > sHi then
                    let vals := (List.range 4).foldl (fun (acc : List Nat) c =>
                      acc ++ [values.getD (c * 2 + 1) 0, values.getD (c * 2) 0]) []
                    let cw := astcInvertWeights bestColorW (ci.wx * ci.wy) ci.quant
                    let aw := astcInvertWeights bestAlphaW (ci.wx * ci.wy) ci.quant
                    (vals, cw, aw)
                  else (values, bestColorW, bestAlphaW)
                else (values, bestColorW, bestAlphaW)
              -- scramble
              let cw := astcScrambleWeights colorWeights (ci.wx * ci.wy) ci.quant
              let aw := astcScrambleWeights alphaWeights (ci.wx * ci.wy) ci.quant
              -- interleave
              let weightCount := ci.wx * ci.wy
              let weights := (List.range weightCount).foldl (fun (acc : List Nat) i =>
                acc ++ [cw.getD i 0, aw.getD i 0]) []
              -- pack
              let weightbuf := List.replicate 16 0
              let (weightbuf, _) := astcIseEncodeBits ci.quant (weightCount * 2) weights weightbuf 0 16
              let out := (List.range 16).map (fun i => bitrev8 (weightbuf.getD (15 - i) 0))
              let bitpos0 := 0
              let (out, bitpos) := astcSetBits out bitpos0 11 ci.blockMode
              let (out, bitpos) := astcSetBits out bitpos 2 0
              let (out, bitpos) := astcSetBits out bitpos 4 endpointFormat
              let bitpos := 128 - ci.weightBits - 2
              let (out, bitpos) := astcSetBits out bitpos 2 3
              let packedValues := astcQuantizeColorValues colorQuantMethod endpointValueCount values
              let (out, _) := astcIseEncodeBits colorQuantMethod endpointValueCount packedValues out 17 16
              some (out, err)

end Texcomp