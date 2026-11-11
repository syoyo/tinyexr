/-
  TinyEXR - Lean 4 formalization of the ASTC LDR block encoder.

  Ports `tc_encode_astc_ldr_block` from
  `tools/texcomp/src/texcomp_astc.c`: the quality-tiered arbitration over
  the luma-axis single-partition fit, the partition-RGB (2/3/4 subsets) and
  dual-RGBA alternative paths, and the const-colour fallback, together with
  the final CEM endpoint assembly / swap / ISE bit-packing.

  The C's `scanned` scan accounting, the bounded error-sorted shortlist,
  the least-squares endpoint upgrades and the iterative reproject/refit
  refinement are reproduced exactly. The C builds the RGB axes lazily
  inside the sweep; this model computes them up front (identical values,
  they depend only on the block).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEval
import Texcomp.AstcFits
import Texcomp.AstcScore
import Texcomp.AstcEncode
import Texcomp.AstcBlockMode
import Texcomp.AstcCandidates
import Texcomp.AstcEndpoints
import Texcomp.AstcColorQuant
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch
import Texcomp.AstcPartitionRgb
import Texcomp.AstcDualRgba
import Texcomp.AstcConstBlock

namespace Texcomp

set_option linter.unusedVariables false

/-- `UINT64_MAX` = "no single-partition fit yet". -/
def astcLdrInf : Nat := 0xFFFFFFFFFFFFFFFF

/-- Medium-tier knobs (the C's tunable defaults in `texcomp_astc.c`). -/
def astcLdrMediumScanCap : Nat := 20
def astcLdrMediumOpaqueScanCap : Nat := 10
def astcLdrMediumSelectedLimit : Nat := 6
def astcLdrMediumOpaqueSelectedLimit : Nat := 4
def astcLdrMediumFullAxisLimit : Nat := 3
def astcLdrMediumOpaqueFullAxisLimit : Nat := 2
def astcLdrMediumRefineRounds : Nat := 2
def astcLdrMediumPartitionErrScale : Nat := 512
def astcLdrMediumOpaquePartitionErrScale : Nat := 3072

/-- `tc_astc_get_decim_cache` returns non-NULL only for weight grids inside
  [2,12]; candidates outside would be skipped. -/
def astcLdrDecimOk (wx wy : Nat) : Bool :=
  2 ≤ wx && wx ≤ 12 && 2 ≤ wy && wy ≤ 12

/-- The per-candidate colour-quant budget check: `quality > 0` consults the
  LUT, the fast tier keeps the identity (256-level) quantizer. -/
def astcLdrColorQuant (quality evc weightBits : Nat) : Option Nat :=
  if quality > 0 then
    if weightBits ≥ 111 then none
    else astcLutColorQuant evc (111 - weightBits)
  else some 20

/-- Batch collection: the C medium/fast scan groups consecutive candidates
  that share the decimation entry and weight quantizer while the scan
  budget has room, skipping over budget-invalid candidates. Returns the
  collected candidate indices and the index the outer loop resumes at. -/
def ldrCollectLoop (cands : List AstcEncMode) (evc quality scanned scanCap : Nat)
    (group : Option (((Nat × Nat) × Nat))) (ci : Nat) (acc : List Nat) :
    List Nat × Nat :=
  if h1 : ci < cands.length then
    if scanned + acc.length < scanCap then
      let cand := cands.getD ci (AstcEncMode.mk 0 0 0 0 0 0)
      if quality > 0 &&
        (cand.weightBits ≥ 111 ||
          (astcLutColorQuant evc (111 - cand.weightBits)).isNone ||
          !(astcLdrDecimOk cand.wx cand.wy)) then
        ldrCollectLoop cands evc quality scanned scanCap group (ci + 1) acc
      else
        let key := ((cand.wx, cand.wy), cand.quant)
        match group with
        | none =>
          ldrCollectLoop cands evc quality scanned scanCap (some key) (ci + 1) (acc ++ [ci])
        | some g =>
          if key == g then
            ldrCollectLoop cands evc quality scanned scanCap group (ci + 1) (acc ++ [ci])
          else (acc, ci)
    else (acc, ci)
  else (acc, ci)
  termination_by cands.length - ci
  decreasing_by all_goals omega

/-- The luma-axis candidate scan. `quality > 1` scores candidates exactly
  with `tc_astc_fit_from_ideal`; the reduced tiers batch-score consecutive
  same-decim/quant candidates with `tc_astc_score_batch` and keep the top
  `selLimit` by insertion into the error-sorted shortlist, mirroring the
  C's `scanned` accounting. `fuel` bounds the loop (one unit per candidate
  position consumed). -/
def ldrScanLoop (block : List (List Nat)) (count bx by_ quality evc : Nat)
    (candLo candHi candIdeal : List Nat)
    (cands : List AstcEncMode) (scanCap selLimit : Nat) :
    Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, sel => sel
  | f + 1, ci, scanned, sel =>
    if ci < cands.length && scanned < scanCap then
      if quality > 1 then
        let cand := cands.getD ci (AstcEncMode.mk 0 0 0 0 0 0)
        if cand.weightBits ≥ 111 ||
          (astcLutColorQuant evc (111 - cand.weightBits)).isNone ||
          !(astcLdrDecimOk cand.wx cand.wy) then
          ldrScanLoop block count bx by_ quality evc candLo candHi candIdeal
            cands scanCap selLimit f (ci + 1) scanned sel
        else
          -- exact per-candidate fit against the luma axis line
          let err := astcFitFromIdeal bx by_ cand.wx cand.wy cand.quant count
            block candIdeal candLo candHi
          ldrScanLoop block count bx by_ quality evc candLo candHi candIdeal
            cands scanCap selLimit f (ci + 1) (scanned + 1)
            (astcShortlistInsert sel selLimit err ci)
      else
        let batchStart := ci
        let (members, nextCi) :=
          ldrCollectLoop cands evc quality scanned scanCap none ci []
        if members.isEmpty then
          ldrScanLoop block count bx by_ quality evc candLo candHi candIdeal
            cands scanCap selLimit f nextCi scanned sel
        else
          -- batch-score the group in one shot (shared decim + quant).
          -- The C inserts `batch_start + bj`, the member's positional
          -- index: budget-skipped candidates shift it off the true index
          -- and that misattribution is part of the reference behaviour.
          let scored : List (Nat × Nat) :=
            (List.zipIdx members 0).map (fun p =>
              let (mc, bj) := p
              let m := cands.getD mc (AstcEncMode.mk 0 0 0 0 0 0)
              (astcScoreFromIdeal bx by_ m.wx m.wy m.quant candIdeal none count,
                batchStart + bj))
          let (sel2, scanned2) := scored.foldl
            (fun (s : List (Nat × Nat) × Nat) e =>
              (astcShortlistInsert s.1 selLimit e.1 e.2, s.2 + 1)) (sel, scanned)
          ldrScanLoop block count bx by_ quality evc candLo candHi candIdeal
            cands scanCap selLimit f nextCi scanned2 sel2
    else sel

/-- Best-fit state after the per-candidate axis sweep:
  `(err, lo, hi, gridWeights, colorQuant, blockMode, weightQm,
    weightX, weightY, fromLsq)`. -/
def LdrBest :=
  Nat × List Nat × List Nat × List Nat × Nat × Nat × Nat × Nat × Nat × Bool

/-- One axis of the shortlist sweep: fit the candidate's weights to the
  axis' ideal projection, score with the decoded (quantized) endpoints,
  then try replacing the axis-extreme endpoints with the least-squares
  solution. Updates the best state when the error improves. -/
def ldrFitAxis (block : List (List Nat)) (count bx by_ : Nat)
    (cand : AstcEncMode) (cquant fmt axis : Nat)
    (axisLoI axisHiI : List Nat) (axisLo axisHi axisIdeal : List (List Nat))
    (axisValid : List Bool) (lumaLoI lumaHiI : Nat)
    (st : LdrBest) : LdrBest :=
  if !axisValid.getD axis false then st
  else if axis != 4 && axisLoI.getD axis 0 == lumaLoI &&
    axisHiI.getD axis 0 == lumaHiI then st -- same pair as the luma axis
  else
    let (bestErr, bestLo, bestHi, bestW, bestCq, bestBm, bestQm, bestWx,
      bestWy, bestFl) := st
    let candLo := axisLo.getD axis []
    let candHi := axisHi.getD axis []
    let (candWeights, wt) :=
      astcWeightsFromIdeal bx by_ cand.wx cand.wy cand.quant
        (axisIdeal.getD axis []) none count
    -- With an identity color quantizer and a direct endpoint format the
    -- fit error already is the decoded error; otherwise eval with the
    -- quantized endpoints.
    let (err, candLo, candHi, fl) :=
      if cquant != 20 || (fmt != 8 && fmt != 12) then
        (astcEvalSingleSse block count wt fmt cquant candLo candHi,
          candLo, candHi, false)
      else
        (astcReconSse block count candLo candHi wt, candLo, candHi, false)
    let (err, candLo, candHi, fl) :=
      match astcLsqEndpoints block count wt with
      | none => (err, candLo, candHi, fl)
      | some (lsqLo, lsqHi) =>
        let e := astcEvalSingleSse block count wt fmt cquant lsqLo lsqHi
        if e < err then (e, lsqLo, lsqHi, true) else (err, candLo, candHi, fl)
    if err < bestErr then
      (err, candLo, candHi, candWeights, cquant, cand.blockMode, cand.quant,
        cand.wx, cand.wy, fl)
    else st

/-- The shortlist sweep: one entry after another; `fullAxes` (astcenc's
  channel-axis endpoint seeding) only for the leading shortlist entries at
  medium quality, everything at high quality, luma-only otherwise. -/
def ldrSweep (block : List (List Nat)) (count bx by_ evc fmt quality : Nat)
    (cands : List AstcEncMode)
    (axisLoI axisHiI : List Nat) (axisLo axisHi axisIdeal : List (List Nat))
    (axisValid : List Bool) (lumaLoI lumaHiI fullAxisLimit : Nat)
    (sel : List (Nat × Nat)) : LdrBest :=
  let init : LdrBest :=
    (astcLdrInf, [0, 0, 0, 0], [0, 0, 0, 0], [], 20, 0, 0, 0, 0, false)
  let step := fun (st : LdrBest) (pkc : (Nat × Nat) × Nat) =>
    let (entry, k) := pkc
    let candIdx := entry.2
    let cand := cands.getD candIdx (AstcEncMode.mk 0 0 0 0 0 0)
    match astcLdrColorQuant quality evc cand.weightBits with
    | none => st
    | some cq =>
      let fullAxes := quality > 1 || (quality == 1 && k < fullAxisLimit)
      let axes := if fullAxes then [0, 1, 2, 3, 4] else [4]
      axes.foldl (fun (s : LdrBest) axis =>
        ldrFitAxis block count bx by_ cand cq fmt axis
          axisLoI axisHiI axisLo axisHi axisIdeal axisValid
          lumaLoI lumaHiI s) st
  sel.zipIdx.foldl step init

/-- Iterative refinement on the winner only: re-project the texels onto
  the refined endpoint line, refit the weights, re-solve the endpoints;
  accept while the decoded error improves. -/
def ldrRefine (block : List (List Nat)) (count bx by_ : Nat)
    (wx wy qm cq fmt : Nat) :
    Nat → (Nat × List Nat × List Nat × List Nat) →
    Nat × List Nat × List Nat × List Nat
  | 0, st => st
  | r + 1, st =>
    let (err, lo, hi, weights) := st
    let denom := (List.range 4).foldl (fun acc c =>
      let dd := if hi.getD c 0 > lo.getD c 0 then hi.getD c 0 - lo.getD c 0
                else lo.getD c 0 - hi.getD c 0
      acc + dd * dd) 0
    if denom == 0 then st
    else
      let recip := astcProjectRecip denom
      let ideal := astcProjectIdeal block count lo hi recip
      let (itWeights, wt) := astcWeightsFromIdeal bx by_ wx wy qm ideal none count
      let itErr := astcEvalSingleSse block count wt fmt cq lo hi
      let (err2, w2, improved) :=
        if itErr < err then (itErr, itWeights, true) else (err, weights, false)
      let (err3, lo3, hi3, w3, improved2) :=
        match astcLsqEndpoints block count wt with
        | none => (err2, lo, hi, w2, improved)
        | some (lsqLo, lsqHi) =>
          let e := astcEvalSingleSse block count wt fmt cq lsqLo lsqHi
          if e < err2 then (e, lsqLo, lsqHi, itWeights, true)
          else (err2, lo, hi, w2, improved)
      if !improved2 then (err3, lo3, hi3, w3)
      else ldrRefine block count bx by_ wx wy qm cq fmt r (err3, lo3, hi3, w3)

/-- Alternative paths: partition-RGB (2/3/4 subsets) and dual-RGBA; each
  replaces the running path only when strictly better (`cand_err <
  path_err`). -/
def ldrAltPaths (block : List (List Nat)) (count quality bx by_ : Nat) :
    Option (List Nat × Nat) :=
  let tryPath (st : Option (List Nat × Nat))
      (mk : Option (List Nat × Nat)) : Option (List Nat × Nat) :=
    match st, mk with
    | none, mk2 => mk2
    | some oe, none => st
    | some (o, e), some (o2, e2) => if e2 < e then some (o2, e2) else some (o, e)
  let p0 := if quality > 0 then
    astcEncodePartitionRgbBlock block count 2 quality bx by_ else none
  let p1 := if quality > 1 then
    astcEncodePartitionRgbBlock block count 3 quality bx by_ else none
  let p2 := if quality > 1 then
    astcEncodePartitionRgbBlock block count 4 quality bx by_ else none
  let p3 := astcEncodeDualRgbaBlock block count quality bx by_
  tryPath (tryPath (tryPath (tryPath none p0) p1) p2) p3

/-- Final single-path pack: CEM value assembly, CEM 8/12 ascending-sum
  endpoint swap with mirrored weights, scramble, ISE weight pack and the
  bit layout. -/
def ldrPackFinal (block : List (List Nat)) (count : Nat)
    (lo hi weights : List Nat) (cquant blockMode weightQm wx wy : Nat)
    (fmt evc : Nat) : List Nat :=
  let wc := wx * wy
  -- endpoint value assembly per CEM
  let values0 : List Nat :=
    if fmt == 0 then [lo.getD 0 0, hi.getD 0 0]
    else if fmt == 4 then [lo.getD 0 0, hi.getD 0 0, lo.getD 3 0, hi.getD 3 0]
    else if fmt == 6 || fmt == 10 then
      let sumLo := lo.getD 0 0 + lo.getD 1 0 + lo.getD 2 0
      let sumHi := hi.getD 0 0 + hi.getD 1 0 + hi.getD 2 0
      let scale0 := if sumHi != 0 then (sumLo * 256 + sumHi / 2) / sumHi else 0
      let scale := min scale0 255
      ([hi.getD 0 0, hi.getD 1 0, hi.getD 2 0, scale] ++
        (if fmt == 10 then [lo.getD 3 0, hi.getD 3 0] else []))
    else
      let base := [lo.getD 0 0, hi.getD 0 0, lo.getD 1 0, hi.getD 1 0,
                   lo.getD 2 0, hi.getD 2 0]
      if fmt == 12 then base ++ [lo.getD 3 0, hi.getD 3 0] else base
  -- CEM 8/12: a decoder swaps the endpoints and applies blue-contract when
  -- the first endpoint's quantized RGB sum is larger, so emit the pair in
  -- ascending-sum order and mirror the weights to compensate.
  let (values, weights) :=
    if fmt == 8 || fmt == 12 then
      let sLo := (List.range 3).foldl (fun acc c =>
        acc + colorRoundtrip cquant (values0.getD (c * 2) 0)) 0
      let sHi := (List.range 3).foldl (fun acc c =>
        acc + colorRoundtrip cquant (values0.getD (c * 2 + 1) 0)) 0
      if sLo > sHi then
        let pairs := if fmt == 12 then 4 else 3
        let vals := (List.range pairs).foldl (fun (acc : List Nat) p =>
          acc ++ [values0.getD (p * 2 + 1) 0, values0.getD (p * 2) 0]) []
        (vals, astcInvertWeights weights wc weightQm)
      else (values0, weights)
    else (values0, weights)
  let weightsScrambled := astcScrambleWeights weights wc weightQm
  let weightbuf0 := List.replicate 16 0
  let (weightbuf, _) :=
    astcIseEncodeBits weightQm wc weightsScrambled weightbuf0 0 16
  let out := (List.range 16).map (fun i => bitrev8 (weightbuf.getD (15 - i) 0))
  let (out, _) := astcSetBits out 0 11 blockMode
  let (out, _) := astcSetBits out 11 2 0 -- one partition
  let (out, _) := astcSetBits out 13 4 fmt
  let packedValues := astcQuantizeColorValues cquant evc values
  let (out, _) := astcIseEncodeBits cquant evc packedValues out 17 16
  out

/-- `tc_encode_astc_ldr_block`. -/
def astcEncodeLdrBlock (block : List (List Nat)) (count quality bx by_ : Nat) :
    List Nat :=
  let isOpaque := astcBlockIsOpaque block count
  let isLuminance := astcBlockIsLuminance block count
  let isRgbScale := !isLuminance && astcBlockIsRgbScale block count
  let endpointFormat :=
    if isLuminance && isOpaque then 0
    else if isLuminance then 4
    else if isRgbScale then (if isOpaque then 6 else 10)
    else if isOpaque then 8 else 12
  let endpointValueCount :=
    if endpointFormat == 0 then 2
    else if endpointFormat == 4 || endpointFormat == 6 then 4
    else if endpointFormat == 8 || endpointFormat == 10 then 6 else 8
  let candidateEndpointEndBit :=
    if quality > 0 then 17 else 17 + endpointValueCount * 8
  -- Axis 4 (luma) drives pass 1.
  let (lumaLoI, lumaHiI) := astcAxisExtremes block count 4
  let axisExts := (List.range 4).map (fun a => astcAxisExtremes block count a)
  let axisLoI := ((List.range 4).map (fun a => (axisExts.getD a (0, 0)).1)) ++ [lumaLoI]
  let axisHiI := ((List.range 4).map (fun a => (axisExts.getD a (0, 0)).2)) ++ [lumaHiI]
  let lumaLine := astcAxisLine block lumaLoI lumaHiI
  let axisLines := ((List.range 4).map (fun a =>
    let (loI, hiI) := axisExts.getD a (0, 0)
    astcAxisLine block loI hiI)) ++ [lumaLine]
  let axisLo := axisLines.map (fun l => l.1)
  let axisHi := axisLines.map (fun l => l.2.1)
  let axisRecip := axisLines.map (fun l => l.2.2.1)
  let axisValid := axisLines.map (fun l => l.2.2.2)
  let axisIdeal := (List.range 5).map (fun a =>
    astcProjectIdeal block count (axisLo.getD a []) (axisHi.getD a [])
      (axisRecip.getD a 0))
  let cands := astcBuildBlockModeCandidates bx by_ candidateEndpointEndBit quality
  -- scan caps and shortlist limits per tier
  let isOpaque36 := isOpaque && count == 36
  let scanCap :=
    if quality > 1 then cands.length
    else if quality > 0 then (if isOpaque36 then astcLdrMediumOpaqueScanCap
                              else astcLdrMediumScanCap)
    else 3
  let selLimit0 :=
    if quality > 1 then 48
    else if quality > 0 then (if isOpaque36 then astcLdrMediumOpaqueSelectedLimit
                              else astcLdrMediumSelectedLimit)
    else 2
  let selLimit := min selLimit0 cands.length
  let fullAxisLimit :=
    if isOpaque36 then astcLdrMediumOpaqueFullAxisLimit
    else astcLdrMediumFullAxisLimit
  -- pass 1: luma-axis scan into the bounded shortlist
  let lumaLo := axisLo.getD 4 []
  let lumaHi := axisHi.getD 4 []
  let lumaIdeal := axisIdeal.getD 4 []
  let sel :=
    ldrScanLoop block count bx by_ quality endpointValueCount
      lumaLo lumaHi lumaIdeal cands scanCap selLimit (cands.length + 1) 0 0 []
  -- pass 2: score the shortlist
  let best := ldrSweep block count bx by_ endpointValueCount endpointFormat
    quality cands axisLoI axisHiI axisLo axisHi axisIdeal axisValid
    lumaLoI lumaHiI fullAxisLimit sel
  let (bestErr, bestLo, bestHi, bestW, bestCq, bestBm, bestQm, bestWx,
    bestWy, bestFl) := best
  -- Iterative refinement happens before the partition/dual fallback
  -- decision (the refined error feeds the threshold check).
  let refineRounds :=
    if quality > 1 then 2
    else if quality > 0 then astcLdrMediumRefineRounds else 2
  let (refErr, refLo, refHi, refW) :=
    if bestErr != astcLdrInf && bestFl then
      ldrRefine block count bx by_ bestWx bestWy bestQm bestCq
        endpointFormat refineRounds (bestErr, bestLo, bestHi, bestW)
    else (bestErr, bestLo, bestHi, bestW)
  if refErr == astcLdrInf then
    -- nothing fit: the partition threshold is always exceeded, so try the
    -- partition/dual paths, then the const fallback
    match ldrAltPaths block count quality bx by_ with
    | some (bytes, _) => bytes
    | none => astcEncodeConstBlock block count
  else
    let pathErrScale :=
      if quality > 1 then 4
      else if quality > 0 then
        (if isOpaque36 then astcLdrMediumOpaquePartitionErrScale
         else astcLdrMediumPartitionErrScale)
      else 256
    let path :=
      if refErr > count * pathErrScale then
        ldrAltPaths block count quality bx by_
      else none
    match path with
    | some (bytes, perr) =>
      if perr < refErr then bytes else
        ldrPackFinal block count refLo refHi refW bestCq bestBm
          bestQm bestWx bestWy endpointFormat endpointValueCount
    | none =>
      ldrPackFinal block count refLo refHi refW bestCq bestBm
        bestQm bestWx bestWy endpointFormat endpointValueCount

end Texcomp
