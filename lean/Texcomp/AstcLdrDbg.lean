/-
  TinyEXR - ASTC LDR block encoder debug trace (Lean side).

  Mirrors the C-side `tc_ldr_dbg_block` trace for differential debugging.
  Not part of the verification gate.
-/
import Texcomp.AstcLdr

open Texcomp

set_option linter.unusedVariables false

deriving instance BEq for LdrBest

/-- Debug variant of `astcEncodeLdrBlock` that emits the same decision
  trace as the C `tc_ldr_dbg_block` harness. -/
def astcEncodeLdrBlockDbg (block : List (List Nat)) (count quality bx by_ : Nat) :
    List Nat × List String := Id.run do
  let mut log : List String := []
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
  log := log ++ [s!"DBG cls opaque={decide isOpaque} luma={decide isLuminance} rgb_scale={decide isRgbScale} fmt={endpointFormat} evc={endpointValueCount}"]
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
  log := log ++ [s!"DBG scan cand_count={cands.length} scan_cap={scanCap} sel_limit={selLimit}"]
  let lumaLo := axisLo.getD 4 []
  let lumaHi := axisHi.getD 4 []
  let lumaIdeal := axisIdeal.getD 4 []
  let sel :=
    ldrScanLoop block count bx by_ quality endpointValueCount
      lumaLo lumaHi lumaIdeal cands scanCap selLimit (cands.length + 1) 0 0 []
  log := log ++ sel.reverse.map (fun (e, i) =>
    s!"DBG sel err={e} idx={i}")
  -- sweep with tracing: replicate ldrSweep step by step
  let init : LdrBest :=
    (astcLdrInf, [0, 0, 0, 0], [0, 0, 0, 0], [], 20, 0, 0, 0, 0, false)
  let step := fun (st : LdrBest × List String) (pkc : (Nat × Nat) × Nat) =>
    let (best, lg) := st
    let (entry, k) := pkc
    let candIdx := entry.2
    let cand := cands.getD candIdx (AstcEncMode.mk 0 0 0 0 0 0)
    match astcLdrColorQuant quality endpointValueCount cand.weightBits with
    | none => (best, lg)
    | some cq =>
      let fullAxes := quality > 1 || (quality == 1 && k < fullAxisLimit)
      let axes := if fullAxes then [0, 1, 2, 3, 4] else [4]
      let st2 := axes.foldl (fun (s : LdrBest × List String) axis =>
        let (sb, slog) := s
        let st2 := ldrFitAxis block count bx by_ cand cq endpointFormat axis
          axisLoI axisHiI axisLo axisHi axisIdeal axisValid
          lumaLoI lumaHiI sb
        let slog :=
          if st2 != sb then
            let (e2, _, _, _, cq2, bm2, qm2, wx2, wy2, fl2) := st2
            slog ++ [s!"DBG best ci={k} cand={candIdx} axis={axis} err={e2} bm={bm2} qm={qm2} cq={cq2} fl={decide fl2} wx={wx2} wy={wy2}"]
          else slog
        (st2, slog)) (best, lg)
      st2
  let (best, log2) := sel.zipIdx.foldl step (init, log)
  let (bestErr, bestLo, bestHi, bestW, bestCq, bestBm, bestQm, bestWx,
    bestWy, bestFl) := best
  let l0 := String.intercalate "," (bestLo.map toString)
  let h0 := String.intercalate "," (bestHi.map toString)
  log := log2 ++ [s!"DBG sweepend err={bestErr} bm={bestBm} cq={bestCq} qm={bestQm} wx={bestWx} wy={bestWy} fl={decide bestFl} lo={l0} hi={h0}"]
  let refineRounds :=
    if quality > 1 then 2
    else if quality > 0 then astcLdrMediumRefineRounds else 2
  let (refErr, refLo, refHi, refW) :=
    if bestErr != astcLdrInf && bestFl then
      ldrRefine block count bx by_ bestWx bestWy bestQm bestCq
        endpointFormat refineRounds (bestErr, bestLo, bestHi, bestW)
    else (bestErr, bestLo, bestHi, bestW)
  let l1 := String.intercalate "," (refLo.map toString)
  let h1 := String.intercalate "," (refHi.map toString)
  log := log ++ [s!"DBG refout err={refErr} lo={l1} hi={h1}"]
  if refErr == astcLdrInf then
    log := log ++ ["DBG decide nofit"]
    match ldrAltPaths block count quality bx by_ with
    | some (bytes, _) => return (bytes, log)
    | none => return (astcEncodeConstBlock block count, log)
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
      log := log ++ [s!"DBG decide path err={perr}"]
      if perr < refErr then return (bytes, log) else
        return (ldrPackFinal block count refLo refHi refW bestCq bestBm
          bestQm bestWx bestWy endpointFormat endpointValueCount, log)
    | none =>
      log := log ++ ["DBG decide single"]
      return (ldrPackFinal block count refLo refHi refW bestCq bestBm
        bestQm bestWx bestWy endpointFormat endpointValueCount, log)
