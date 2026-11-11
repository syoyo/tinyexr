/-
  TinyEXR - Lean 4 formalization of the ASTC HDR block encoders.

  Ports `tc_encode_astc_hdr_cem11_block`, `tc_encode_astc_hdr_cem15_block`,
  `tc_encode_astc_hdr_cem7_block`, `tc_encode_astc_hdr_cem11_2subset_block`,
  `tc_astc_hdr_lsq{,4,_part}` and `tc_astc_float_to_lns16` /
  `tc_astc_lns16_to_sf16` / `tc_astc_hdr_write_void_extent` from
  `tools/texcomp/src/texcomp_astc.c` and `texcomp_astc_hdr.c`.

  The round loops are unrolled exactly like the reference: round 0 always
  stores, later rounds only on strict improvement, least-squares re-solve
  between rounds. Failures return `none` (the C's `UINT64_MAX` SSE).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEval
import Texcomp.AstcEncode
import Texcomp.AstcBlockMode
import Texcomp.AstcEndpoints
import Texcomp.AstcColorQuant
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch
import Texcomp.AstcWeightInfill
import Texcomp.AstcUastc
import Texcomp.AstcHdr
import Texcomp.AstcHdrPack

namespace Texcomp

set_option linter.unusedVariables false
set_option maxRecDepth 5000

/-- C truncating-toward-zero division with round-half-away adjustment
  (`tc_div_round_s64`, den > 0). -/
def hdrDivRound (num den : Int) : Int :=
  let half := den / 2
  if num ≥ 0 then (num + half) / den
  else -((-num + half) / den)

/-- Arithmetic right shift by 8 on a C `int` (floor division). -/
def hdrShift8 (x : Int) : Int :=
  if x ≥ 0 then x / 256 else -((-x + 255) / 256)

/-- `tc_astc_hdr_lsq`: least-squares endpoints per channel in the LNS
  domain. A degenerate channel keeps its incoming endpoints. -/
def hdrLsq (lns : List (List Int)) (wt : List Nat) (e0 e1 : List Int) :
    List Int × List Int :=
  (List.range 3).foldl (fun (acc : List Int × List Int) c =>
    let (e0, e1) := acc
    let sums := (List.range 16).foldl
      (fun (s : Int × Int × Int × Int × Int) i =>
        let a := 64 - (wt.getD i 0 : Int)
        let b := (wt.getD i 0 : Int)
        let p := (lns.getD i []).getD c 0
        (s.1 + a * a, s.2.1 + a * b, s.2.2.1 + b * b, s.2.2.2.1 + a * p,
          s.2.2.2.2 + b * p))
      (0, 0, 0, 0, 0)
    let (saa, sab, sbb, sap, sbp) := sums
    let det := saa * sbb - sab * sab
    if det ≤ 0 then (e0, e1)
    else
      let cl := fun (x : Int) => if x < 0 then 0 else if x > 65535 then 65535 else x
      let l := cl (hdrDivRound ((sap * sbb - sbp * sab) * 64) det)
      let h := cl (hdrDivRound ((sbp * saa - sap * sab) * 64) det)
      (e0.set c l, e1.set c h))
    (e0, e1)

/-- `tc_astc_hdr_lsq4`: the 4-channel (RGBA) variant. -/
def hdrLsq4 (lns : List (List Int)) (wt : List Nat) (e0 e1 : List Int) :
    List Int × List Int :=
  (List.range 4).foldl (fun (acc : List Int × List Int) c =>
    let (e0, e1) := acc
    let sums := (List.range 16).foldl
      (fun (s : Int × Int × Int × Int × Int) i =>
        let a := 64 - (wt.getD i 0 : Int)
        let b := (wt.getD i 0 : Int)
        let p := (lns.getD i []).getD c 0
        (s.1 + a * a, s.2.1 + a * b, s.2.2.1 + b * b, s.2.2.2.1 + a * p,
          s.2.2.2.2 + b * p))
      (0, 0, 0, 0, 0)
    let (saa, sab, sbb, sap, sbp) := sums
    let det := saa * sbb - sab * sab
    if det ≤ 0 then (e0, e1)
    else
      let cl := fun (x : Int) => if x < 0 then 0 else if x > 65535 then 65535 else x
      let l := cl (hdrDivRound ((sap * sbb - sbp * sab) * 64) det)
      let h := cl (hdrDivRound ((sbp * saa - sap * sab) * 64) det)
      (e0.set c l, e1.set c h))
    (e0, e1)

/-- `tc_astc_hdr_lsq_part`: per-subset sums only. -/
def hdrLsqPart (lns : List (List Int)) (wt : List Nat) (partOf : List Nat)
    (subset : Nat) (e0 e1 : List Int) : List Int × List Int :=
  (List.range 3).foldl (fun (acc : List Int × List Int) c =>
    let (e0, e1) := acc
    let sums := (List.range 16).foldl
      (fun (s : Int × Int × Int × Int × Int) i =>
        if partOf.getD i 0 != subset then s else
        let a := 64 - (wt.getD i 0 : Int)
        let b := (wt.getD i 0 : Int)
        let p := (lns.getD i []).getD c 0
        (s.1 + a * a, s.2.1 + a * b, s.2.2.1 + b * b, s.2.2.2.1 + a * p,
          s.2.2.2.2 + b * p))
      (0, 0, 0, 0, 0)
    let (saa, sab, sbb, sap, sbp) := sums
    let det := saa * sbb - sab * sab
    if det ≤ 0 then (e0, e1)
    else
      let cl := fun (x : Int) => if x < 0 then 0 else if x > 65535 then 65535 else x
      let l := cl (hdrDivRound ((sap * sbb - sbp * sab) * 64) det)
      let h := cl (hdrDivRound ((sbp * saa - sap * sab) * 64) det)
      (e0.set c l, e1.set c h))
    (e0, e1)

/-- Per-texel projection weight in the quantized-endpoint domain over
  channels `chs` (clamped dot / dl scaled to [0,64]). -/
def hdrProjW (px : List Int) (q0 : List Int) (d : List Int) (dl : Int)
    (chs : List Nat) : Int :=
  if dl ≤ 0 then 0
  else
    let dot := chs.foldl (fun acc c =>
      acc + ((px.getD c 0) - q0.getD c 0) * d.getD c 0) 0
    let dot := if dot < 0 then 0 else if dot > dl then dl else dot
    (dot * 64 + dl / 2) / dl

/-- C int64 division: truncation toward zero (Lean's `/` floors). `b > 0`. -/
def hdrTdiv (a b : Int) : Int :=
  if a ≥ 0 || a % b == 0 then a / b else a / b + 1

/-- Per-texel reconstruction error over `nch` channels with one weight:
  `rec = q0[c] + d[c] * uq / 64` (C truncating int64 division). -/
def hdrTexelErr (px : List Int) (q0 d : List Int) (nch : Nat) (uq : Int) : Int :=
  (List.range nch).foldl (fun acc c =>
    let rc := q0.getD c 0 + hdrTdiv (d.getD c 0 * uq) 64
    let e := rc - px.getD c 0
    acc + e * e) 0

/-- `tc_encode_astc_hdr_cem11_block`: HDR RGB direct (CEM 11), single-plane
  with LSQ refinement plus a dual-plane (CCS) alternative. Returns the
  packed block and the LNS-domain SSE. -/
def astcEncodeHdrCem11Block (lns : List (List Int)) : Option (List Nat × Nat) :=
  let bmSingle := (astcUastcGridMode 5 false).getD 0
  let bmDual := (astcUastcGridMode 1 true).getD 0
  -- per-channel LNS bounding box
  let (e0b, e1b) := (List.range 16).foldl
    (fun (a : List Int × List Int) i =>
      let px := lns.getD i []
      ((List.range 3).map (fun c => min (a.1.getD c 0) (px.getD c 0)),
       (List.range 3).map (fun c => max (a.2.getD c 0) (px.getD c 0))))
    (lns.getD 0 [], lns.getD 0 [])
  -- single-plane 3-round refine
  let round := fun (e0 e1 : List Int) =>
    let (b0, b1, b2, b3, b4, b5) :=
      cem11Pack (e0.map (fun x => x.toNat)) (e1.map (fun x => x.toNat)) 20
    let vv : List Nat := [b0, b1, b2, b3, b4, b5]
    let (q0l, q1l) := hdrEncCem11Unpack vv
    let d := (List.range 3).map (fun c => q1l.getD c 0 - q0l.getD c 0)
    let dl := (List.range 3).foldl (fun acc c =>
      acc + d.getD c 0 * d.getD c 0) 0
    let (sw, wt, sse) := (List.range 16).foldl
      (fun (st : List Nat × List Nat × Int) i =>
        let (swa, wta, ssea) := st
        let px := lns.getD i []
        let w64 := hdrProjW px q0l d dl (List.range 3)
        let w := astcUastcQuantWeight w64.toNat 5
        let uq := astcUastcUnquant w 5
        (swa ++ [w], wta ++ [uq],
          ssea + hdrTexelErr px q0l d 3 uq))
      ([], [], 0)
    (vv, sw, wt, sse)
  let (v0, sw0, wt0, sse0) := round e0b e1b
  let best0 := some (sse0, v0, sw0)
  let (e0a, e1a) := hdrLsq lns wt0 e0b e1b
  let (v1, sw1, wt1, sse1) := round e0a e1a
  let best12 :=
    if sse1 < sse0 then
      let best1 := some (sse1, v1, sw1)
      let (e0c, e1c) := hdrLsq lns wt1 e0a e1a
      let (v2, sw2, _, sse2) := round e0c e1c
      if sse2 < sse1 then some (sse2, v2, sw2) else best1
    else best0
  match best12 with
  | none => none
  | some (sseSingle, vBest, swBest) =>
    let (qe0, qe1) := hdrEncCem11Unpack vBest
    let dir := (List.range 3).map (fun c => qe1.getD c 0 - qe0.getD c 0)
    -- dual-plane alternatives (CCS 0..2)
    let (bestCcs, bestDualSse, dp1, dp2) := (List.range 3).foldl
      (fun (st : Int × Int × List Nat × List Nat) ccs =>
        let d1 := (List.range 3).foldl (fun acc c =>
          if c != ccs then acc + dir.getD c 0 * dir.getD c 0 else acc) 0
        let d2 := dir.getD ccs 0 * dir.getD ccs 0
        let (t1, t2, dsse) := (List.range 16).foldl
          (fun (st : List Nat × List Nat × Int) i =>
            let (s1, s2, s3) := st
            let px := lns.getD i []
            let w1 := hdrProjW px qe0 dir d1
              ((List.range 3).filter (fun c => c != ccs))
            let w2 := hdrProjW px qe0 dir d2 [ccs]
            let q1 := astcUastcQuantWeight w1.toNat 1
            let q2 := astcUastcQuantWeight w2.toNat 1
            let u1 := astcUastcUnquant q1 1
            let u2 := astcUastcUnquant q2 1
            let uqs := (List.range 3).map (fun c =>
              if c == ccs then u2 else u1)
            (s1 ++ [q1], s2 ++ [q2],
              s3 + (List.range 3).foldl (fun acc c =>
                let uq := uqs.getD c 0
                let rc := qe0.getD c 0 + hdrTdiv (dir.getD c 0 * uq) 64
                let e := rc - px.getD c 0
                acc + e * e) 0))
          ([], [], 0)
        if st.1 < 0 || dsse < st.2.1 then
          (ccs, dsse, t1, t2) else st)
      (-1, 0, [], [])
    if bestCcs ≥ 0 && bestDualSse < sseSingle then
      let wbits := iseBitcount 32 1
      let dualw := (List.range 16).foldl (fun (acc : List Nat) i =>
        acc ++ [dp1.getD i 0, dp2.getD i 0]) []
      let out := astcUastcWeightBytes 1 dualw true
      let (out, _) := astcSetBits out 0 11 bmDual
      let (out, _) := astcSetBits out 11 2 0
      let (out, _) := astcSetBits out 13 4 11
      let (out, _) := astcSetBits out (128 - wbits - 2) 2 bestCcs.toNat
      let packed := astcQuantizeColorValues 20 6 vBest
      let (out, _) := astcIseEncodeBits 20 6 packed out 17 16
      some (out, bestDualSse.toNat)
    else
      let out := astcUastcWeightBytes 5 swBest false
      let (out, _) := astcSetBits out 0 11 bmSingle
      let (out, _) := astcSetBits out 11 2 0
      let (out, _) := astcSetBits out 13 4 11
      let packed := astcQuantizeColorValues 20 6 vBest
      let (out, _) := astcIseEncodeBits 20 6 packed out 17 16
      some (out, sseSingle.toNat)

/-- `tc_encode_astc_hdr_cem7_block`: HDR RGB base+scale (CEM 7), 4x4 range-16
  weights, 4 endpoint values at colour quant 256. -/
def astcEncodeHdrCem7Block (lns : List (List Int)) : Option (List Nat × Nat) :=
  let bmSingle := (astcUastcGridMode 8 false).getD 0
  let (e0b, e1b) := (List.range 16).foldl
    (fun (a : List Int × List Int) i =>
      let px := lns.getD i []
      ((List.range 3).map (fun c => min (a.1.getD c 0) (px.getD c 0)),
       (List.range 3).map (fun c => max (a.2.getD c 0) (px.getD c 0))))
    (lns.getD 0 [], lns.getD 0 [])
  let round := fun (e0 e1 : List Int) =>
    let (v0, v1, v2, v3) := cem7Pack (e0.map (fun x => x.toNat)) (e1.map (fun x => x.toNat)) 20
    let vv : List Nat := [v0, v1, v2, v3]
    let (q0l, q1l) := hdrEncCem7Unpack vv
    let d := (List.range 3).map (fun c => q1l.getD c 0 - q0l.getD c 0)
    let dl := (List.range 3).foldl (fun acc c =>
      acc + d.getD c 0 * d.getD c 0) 0
    let (sw, wt, sse) := (List.range 16).foldl
      (fun (st : List Nat × List Nat × Int) i =>
        let (swa, wta, ssea) := st
        let px := lns.getD i []
        let w64 := hdrProjW px q0l d dl (List.range 3)
        let w := astcUastcQuantWeight w64.toNat 8
        let uq := astcUastcUnquant w 8
        (swa ++ [w], wta ++ [uq],
          ssea + hdrTexelErr px q0l d 3 uq))
      ([], [], 0)
    (vv, sw, wt, sse)
  let (v0, sw0, wt0, sse0) := round e0b e1b
  let best0 := some (sse0, v0, sw0)
  let (e0a, e1a) := hdrLsq lns wt0 e0b e1b
  let (v1, sw1, wt1, sse1) := round e0a e1a
  let best12 :=
    if sse1 < sse0 then
      let best1 := some (sse1, v1, sw1)
      let (e0c, e1c) := hdrLsq lns wt1 e0a e1a
      let (v2, sw2, _, sse2) := round e0c e1c
      if sse2 < sse1 then some (sse2, v2, sw2) else best1
    else best0
  match best12 with
  | none => none
  | some (best, vBest, swBest) =>
    let out := astcUastcWeightBytes 8 swBest false
    let (out, _) := astcSetBits out 0 11 bmSingle
    let (out, _) := astcSetBits out 11 2 0
    let (out, _) := astcSetBits out 13 4 7
    let packed := astcQuantizeColorValues 20 4 vBest
    let (out, _) := astcIseEncodeBits 20 4 packed out 17 16
    some (out, best.toNat)

/-- Largest colour-quant level in [20..4] whose 8-value ISE fits `avail`
  (the C's descending scan). -/
def hdrFitColorQuant (avail : Nat) : Option Nat :=
  ((List.range 17).map (fun k => 20 - k)).find? (fun cq =>
    iseBitcount 8 cq ≤ avail)

/-- `tc_encode_astc_hdr_cem15_block`: HDR RGB + HDR alpha (CEM 15),
  single-plane at weight range 6 with a dual-plane alpha alternative whose
  colour quant is derived from the leftover space. -/
def astcEncodeHdrCem15Block (lns : List (List Int)) : Option (List Nat × Nat) :=
  let bm := (astcUastcGridMode 4 false).getD 0
  let dbm := (astcUastcGridMode 1 true).getD 0
  let (e0b, e1b) := (List.range 16).foldl
    (fun (a : List Int × List Int) i =>
      let px := lns.getD i []
      ((List.range 4).map (fun c => min (a.1.getD c 0) (px.getD c 0)),
       (List.range 4).map (fun c => max (a.2.getD c 0) (px.getD c 0))))
    (lns.getD 0 [], lns.getD 0 [])
  let round := fun (e0 e1 : List Int) =>
    let v := hdrEncCem15Pack (e0.map (fun x => x.toNat)) (e1.map (fun x => x.toNat)) (e0.getD 3 0) (e1.getD 3 0) 20
    let (q0l, q1l) := hdrEncCem15Unpack v
    let d := (List.range 4).map (fun c => q1l.getD c 0 - q0l.getD c 0)
    let dl := (List.range 4).foldl (fun acc c =>
      acc + d.getD c 0 * d.getD c 0) 0
    let (sw, wt, sse) := (List.range 16).foldl
      (fun (st : List Nat × List Nat × Int) i =>
        let (swa, wta, ssea) := st
        let px := lns.getD i []
        let w64 := hdrProjW px q0l d dl (List.range 4)
        let w := astcUastcQuantWeight w64.toNat 4
        let uq := astcUastcUnquant w 4
        (swa ++ [w], wta ++ [uq],
          ssea + hdrTexelErr px q0l d 4 uq))
      ([], [], 0)
    (v, sw, wt, sse)
  let (v0, sw0, wt0, sse0) := round e0b e1b
  let best0 := some (sse0, v0, sw0)
  let (e0a, e1a) := hdrLsq4 lns wt0 e0b e1b
  let (v1, sw1, wt1, sse1) := round e0a e1a
  let best12 :=
    if sse1 < sse0 then
      let best1 := some (sse1, v1, sw1)
      let (e0c, e1c) := hdrLsq4 lns wt1 e0a e1a
      let (v2, sw2, _, sse2) := round e0c e1c
      if sse2 < sse1 then some (sse2, v2, sw2) else best1
    else best0
  -- the C's dual path packs the endpoints as left by the last executed
  -- least-squares re-solve (after round 1 if it improved, else round 0's)
  let (e0Fin, e1Fin) :=
    if sse1 < sse0 then hdrLsq4 lns wt1 e0a e1a else (e0a, e1a)
  match best12 with
  | none => none
  | some (bestSse, vBest, swBest) =>
    -- dual-plane alpha alternative: RGB on plane 0, alpha on plane 1
    let dualTry : Option (List Nat × Nat) :=
      let dwbits := iseBitcount 32 1
      if dwbits + 2 + 17 ≥ 128 then none
      else
        let davail := 128 - dwbits - 2 - 17
        match hdrFitColorQuant davail with
        | none => none
        | some dcq =>
          let v := hdrEncCem15Pack (e0Fin.map (fun x => x.toNat))
            (e1Fin.map (fun x => x.toNat)) (e0Fin.getD 3 0) (e1Fin.getD 3 0) dcq
          let (dq0, dq1) := hdrEncCem15Unpack v
          let dd := (List.range 4).map (fun c => dq1.getD c 0 - dq0.getD c 0)
          let ddl := (List.range 4).foldl (fun acc c =>
            acc + dd.getD c 0 * dd.getD c 0) 0
          if ddl ≤ 0 then none
          else
            let dualw := (List.range 16).foldl (fun (acc : List Nat) i =>
              let px := lns.getD i []
              let dotRgb := (List.range 3).foldl (fun acc c =>
                acc + ((px.getD c 0) - dq0.getD c 0) * dd.getD c 0) 0
              let dotA := (px.getD 3 0) - dq0.getD 3 0
              let cl := fun (x : Int) =>
                if x < 0 then 0 else if x > ddl then ddl else x
              let w0 := (cl dotRgb * 64 + ddl / 2) / ddl
              let w1 := (cl dotA * 64 + ddl / 2) / ddl
              acc ++ [astcUastcQuantWeight w0.toNat 1,
                      astcUastcQuantWeight w1.toNat 1]) []
            let dualSse := (List.range 16).foldl (fun acc i =>
              let px := lns.getD i []
              let uq0 := astcUastcUnquant (dualw.getD (i * 2) 0) 1
              let uq1 := astcUastcUnquant (dualw.getD (i * 2 + 1) 0) 1
              acc + (List.range 3).foldl (fun a2 c =>
                let rc := dq0.getD c 0 + hdrTdiv (dd.getD c 0 * uq0) 64
                let e := rc - px.getD c 0
                a2 + e * e) 0 +
                (let rc := dq0.getD 3 0 + hdrTdiv (dd.getD 3 0 * uq1) 64
                 let e := rc - px.getD 3 0
                 e * e)) 0
            if dualSse < bestSse then
              let out := astcUastcWeightBytes 1 dualw true
              let (out, _) := astcSetBits out 0 11 dbm
              let (out, _) := astcSetBits out 11 2 0
              let (out, _) := astcSetBits out 13 4 15
              let packed := astcQuantizeColorValues dcq 8 v
              let (out, _) := astcIseEncodeBits dcq 8 packed out 17 16
              let (out, _) := astcSetBits out (128 - dwbits - 2) 2 3
              some (out, dualSse.toNat)
            else none
    match dualTry with
    | some r => some r
    | none =>
      -- single-plane pack; derive the colour quant the decoder will see
      let wbits := iseBitcount 16 4
      let avail := if wbits + 17 < 128 then 128 - wbits - 17 else 0
      match hdrFitColorQuant avail with
      | none => none -- cannot encode this block as CEM 15
      | some cq =>
        let out := astcUastcWeightBytes 4 swBest false
        let (out, _) := astcSetBits out 0 11 bm
        let (out, _) := astcSetBits out 11 2 0
        let (out, _) := astcSetBits out 13 4 15
        let packed := astcQuantizeColorValues cq 8 vBest
        let (out, _) := astcIseEncodeBits cq 8 packed out 17 16
        some (out, bestSse.toNat)

/-- `tc_encode_astc_hdr_cem11_2subset_block`: two-subset CEM 11 with a
  10-bit partition index and per-subset endpoint pairs at a derived colour
  quant. -/
def astcEncodeHdrCem11TwoSubsetBlock (lns : List (List Int)) :
    Option (List Nat × Nat) :=
  let bm := (astcUastcGridMode 2 false).getD 0
  -- proxy block: 8-bit proxy of the LNS values (opaque alpha)
  let proxy : List (List Nat) := (List.range 16).map (fun i =>
    let px := lns.getD i []
    ((List.range 3).map (fun c =>
      let p := hdrShift8 (px.getD c 0)
      if p < 0 then (0 : Nat) else if p > 255 then (255 : Nat) else p.toNat
     ) ++ [255]))
  match astcFindBestPartition proxy 4 4 2 with
  | some (piIdx, true) =>
    let cache := astcBuildPartitionCache 4 4 2
    let piEntry := cache.getD piIdx (0, [], [], [])
    let partOf := piEntry.2.1
    let piSeed := piEntry.1
    match astcLutColorQuant 12 67 with
    | none => none
    | some clevel =>
      -- per-subset LNS bbox
      let bbox := (List.range 2).map (fun s =>
        (List.range 16).foldl
          (fun (a : Option (List Int × List Int × Bool)) i =>
            if partOf.getD i 0 != s then a else
            let px := lns.getD i []
            match a with
            | none => some (px.take 3, px.take 3, true)
            | some (lo3, hi3, _) =>
              some ((List.range 3).map (fun c =>
                      min (lo3.getD c 0) (px.getD c 0)),
                    (List.range 3).map (fun c =>
                      max (hi3.getD c 0) (px.getD c 0)),
                    true))
          none)
      if bbox.any (fun b => b.isNone) then none
      else
        let rlo0 := bbox.map (fun b =>
          match b with
          | some (lo3, _, _) => lo3 | none => [])
        let rhi0 := bbox.map (fun b =>
          match b with
          | some (_, hi3, _) => hi3 | none => [])
        let cnt := (List.range 2).map (fun s =>
          (List.range 16).foldl (fun acc i =>
            if partOf.getD i 0 == s then acc + 1 else acc) 0)
        if cnt.getD 0 0 == 0 || cnt.getD 1 0 == 0 then none
        else
          let rnd := fun (rlo rhi : List (List Int)) =>
            let perSub := (List.range 2).map (fun s =>
              let (b0, b1, b2, b3, b4, b5) :=
                cem11Pack ((rlo.getD s []).map (fun x => x.toNat))
                  ((rhi.getD s []).map (fun x => x.toNat)) clevel
              let vv : List Nat := [b0, b1, b2, b3, b4, b5]
              let (q0l, q1l) := hdrEncCem11Unpack vv
              (vv, q0l, q1l))
            let ev := (perSub.foldl (fun acc p => acc ++ p.1) [])
            let (weights, wt, rsse) := (List.range 16).foldl
              (fun (st : List Nat × List Nat × Int) i =>
                let (swa, wta, ssea) := st
                let s2 := partOf.getD i 0
                let px := lns.getD i []
                let q0l := (perSub.getD s2 ([], [], [])).2.1
                let q1l := (perSub.getD s2 ([], [], [])).2.2
                let d := (List.range 3).map (fun c =>
                  q1l.getD c 0 - q0l.getD c 0)
                let dl := (List.range 3).foldl (fun acc c =>
                  acc + d.getD c 0 * d.getD c 0) 0
                let w64 := hdrProjW px q0l d dl (List.range 3)
                let w := astcUastcQuantWeight w64.toNat 2
                let uq := astcUastcUnquant w 2
                (swa ++ [w], wta ++ [uq],
                  ssea + hdrTexelErr px q0l d 3 uq))
              ([], [], 0)
            (ev, weights, wt, rsse)
          let lsqAll := fun (rlo rhi : List (List Int)) (wt : List Nat) =>
            (List.range 2).foldl
              (fun (acc : List (List Int) × List (List Int)) s =>
                let (l, h) := hdrLsqPart lns wt partOf s (rlo.getD s [])
                  (rhi.getD s [])
                (acc.1.set s l, acc.2.set s h))
              (rlo, rhi)
          let (ev0, w0, wt0, sse0) := rnd rlo0 rhi0
          let best0 := some (sse0, ev0, w0)
          let (rlo1, rhi1) := lsqAll rlo0 rhi0 wt0
          let (ev1, w1, wt1, sse1) := rnd rlo1 rhi1
          let best12 :=
            if sse1 < sse0 then
              let best1 := some (sse1, ev1, w1)
              let (rlo2, rhi2) := lsqAll rlo1 rhi1 wt1
              let (ev2, w2, _, sse2) := rnd rlo2 rhi2
              if sse2 < sse1 then some (sse2, ev2, w2) else best1
            else best0
          match best12 with
          | none => none
          | some (best, ev, weights) =>
            let out := astcUastcWeightBytes 2 weights false
            let (out, _) := astcSetBits out 0 11 bm
            let (out, _) := astcSetBits out 11 2 1
            let (out, _) := astcSetBits out 13 6 (piSeed &&& 63)
            let (out, _) := astcSetBits out 19 4 (piSeed >>> 6)
            let (out, _) := astcSetBits out 23 6 (11 <<< 2)
            let packed := astcQuantizeColorValues clevel 12 ev
            let (out, _) := astcIseEncodeBits clevel 12 packed out 29 16
            some (out, best.toNat)
  | _ => none

/-- `tc_float_to_half_bits` (from `texcomp_bc6h.c`). -/
def floatToHalfBits (fv : Float32) : Nat :=
  let u := fv.toBits.toNat
  let sign := (u >>> 16) &&& 0x8000
  let exp := (u >>> 23) &&& 0xFF
  let mant := u &&& 0x7FFFFF
  if exp == 255 then sign ||| 0x7C00 ||| (if mant != 0 then 0x0200 else 0)
  else if exp > 142 then sign ||| 0x7C00
  else if exp < 113 then
    if exp < 103 then sign
    else
      let m1 := (mant ||| 0x800000) >>> (125 - exp)
      sign ||| ((m1 + 0x1000) >>> 13)
  else
    let exp2 := exp - 112
    let mant2 := (mant + 0x1000) >>> 13
    let (mant3, exp3) :=
      if (mant2 &&& 0x400) != 0 then (0, exp2 + 1) else (mant2, exp2)
    if exp3 ≥ 31 then sign ||| 0x7C00
    else sign ||| (exp3 <<< 10) ||| (mant3 &&& 0x3FF)

/-- `tc_astc_frexp`: astcenc-compatible frexp via the raw bits. -/
def hdrFrexpF (a : Float32) : Float32 × Int :=
  let ai := a.toBits
  (Float32.ofBits ((ai &&& 0x807FFFFF) ||| 0x3F000000),
    Int.ofNat (((ai >>> 23) &&& 0xFF).toNat) - 126)

/-- `tc_astc_float_to_lns16`: float → 16-bit LNS (rounded, clamped). -/
def floatToLns16 (a : Float32) : Int :=
  let underflow := !(a > (1.0 : Float32) / 67108864.0)
  let infinity := a >= 65536.0
  let (mant, expo) := hdrFrexpF a
  let (av, expv) : Float32 × Int :=
    if expo < -13 then (a * 33554432.0, 0)
    else ((mant - 0.5) * 4096.0, expo + 14)
  let a2 : Float32 :=
    if av < 384.0 then av * (4.0 / 3.0)
    else if av ≤ 1408.0 then av + 128.0
    else (av + 512.0) * (4.0 / 5.0)
  let r := a2 + Float32.ofInt expv * 2048.0 + 1.0
  let r : Float32 := if infinity then 65535.0 else r
  let r : Float32 := if underflow then 0.0 else r
  let ri := Tocio.truncToIntF (r + 0.5)
  let ri := if ri < 0 then 0 else ri
  if ri > 65535 then 65535 else ri

/-- One 4x4 block gather with edge clamping, as in
  `tc_astc_hdr_compress_rgbf` / `_rgbaf`. Returns the per-texel LNS rows
  and the raw float bits of texel 0. -/
def hdrGatherBlock (pix : List (List Nat)) (width height bx by0 nch : Nat) :
    List (List Int) × List Nat :=
  let cells := (List.range 16).map (fun idx =>
    let yy := idx / 4
    let xx := idx % 4
    let y := min (by0 + yy) (height - 1)
    let x := min (bx + xx) (width - 1)
    pix.getD (y * width + x) [])
  let lns := cells.map (fun p =>
    (List.range nch).map (fun c =>
      floatToLns16 (Float32.ofBits (UInt32.ofNat (p.getD c 0)))))
  (lns, cells.getD 0 [])

/-- `tc_astc_hdr_compress_rgbf`: RGB HDR image → ASTC HDR blocks. The
  per-texel input is a list of RGB float bit patterns in row-major order. -/
def astcEncodeHdrRgbF (pix : List (List Nat)) (width height : Nat) :
    List Nat :=
  -- iterate over 4x4 blocks, best-of {cem11, 2-subset, cem7, mean void}
  let nBlocksY := (height + 3) / 4
  let nBlocksX := (width + 3) / 4
  (List.range (nBlocksY * nBlocksX)).foldl (fun (acc : List Nat) bi =>
    let byB := (bi / nBlocksX) * 4
    let bx := (bi % nBlocksX) * 4
    let (lns, src0) := hdrGatherBlock pix width height bx byB 3
    let allSame := (List.range 16).all (fun i =>
      lns.getD i [] == lns.getD 0 [])
    let block : List Nat :=
      if allSame then
        hdrWriteVoidExtent (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 0 0))))
          (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 1 0))))
          (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 2 0)))) 0x3C00
      else
        let (cemSse, cemBuf) : Nat × List Nat :=
          match astcEncodeHdrCem11Block lns with
          | some (b, s) => (s, b)
          | none => (astcUastcInf, List.replicate 16 0)
        let (subSse, subBuf) : Nat × List Nat :=
          match astcEncodeHdrCem11TwoSubsetBlock lns with
          | some (b, s) => (s, b)
          | none => (astcUastcInf, List.replicate 16 0)
        let (c7Sse, c7Buf) : Nat × List Nat :=
          match astcEncodeHdrCem7Block lns with
          | some (b, s) => (s, b)
          | none => (astcUastcInf, List.replicate 16 0)
        let bestSse0 := cemSse
        let bestBuf0 := cemBuf
        let (bestSse1, bestBuf1) :=
          if subSse < bestSse0 then (subSse, subBuf) else (bestSse0, bestBuf0)
        let (bestSse2, bestBuf2) :=
          if c7Sse < bestSse1 then (c7Sse, c7Buf) else (bestSse1, bestBuf1)
        -- block-mean void extent comparison (`ve_sse <= best_sse`)
        let sums := (List.range 3).map (fun c =>
          (List.range 16).foldl (fun acc i =>
            acc + (lns.getD i []).getD c 0) 0)
        let mean := sums.map (fun s => s / 16)
        let veSse := (List.range 16).foldl (fun acc i =>
          (List.range 3).foldl (fun a2 c =>
            let e := (lns.getD i []).getD c 0 - mean.getD c 0
            a2 + e * e) acc) 0
        if veSse ≤ bestSse2 then
          hdrWriteVoidExtent (lns16ToSf16 (mean.getD 0 0).toNat)
            (lns16ToSf16 (mean.getD 1 0).toNat)
            (lns16ToSf16 (mean.getD 2 0).toNat) 0x3C00
        else bestBuf2
    acc ++ block) []

/-- `tc_astc_hdr_compress_rgbaf`: RGBA HDR image → ASTC HDR blocks. -/def astcEncodeHdrRgbaF (pix : List (List Nat)) (width height : Nat) :
    List Nat :=
  let nBlocksY := (height + 3) / 4
  let nBlocksX := (width + 3) / 4
  (List.range (nBlocksY * nBlocksX)).foldl (fun (acc : List Nat) bi =>
    let byB := (bi / nBlocksX) * 4
    let bx := (bi % nBlocksX) * 4
    let (lns, src0) := hdrGatherBlock pix width height bx byB 4
    let allSame := (List.range 16).all (fun i =>
      lns.getD i [] == lns.getD 0 [])
    let block : List Nat :=
      if allSame then
        hdrWriteVoidExtent (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 0 0))))
          (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 1 0))))
          (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 2 0))))
          (floatToHalfBits (Float32.ofBits (UInt32.ofNat (src0.getD 3 0))))
      else
        let (cemSse, cemBuf) : Nat × List Nat :=
          match astcEncodeHdrCem15Block lns with
          | some (b, s) => (s, b)
          | none => (astcUastcInf, List.replicate 16 0)
        let sums := (List.range 4).map (fun c =>
          (List.range 16).foldl (fun acc i =>
            acc + (lns.getD i []).getD c 0) 0)
        let mean := sums.map (fun s => s / 16)
        let veSse := (List.range 16).foldl (fun acc i =>
          (List.range 4).foldl (fun a2 c =>
            let e := (lns.getD i []).getD c 0 - mean.getD c 0
            a2 + e * e) acc) 0
        if veSse ≤ cemSse then
          hdrWriteVoidExtent (lns16ToSf16 (mean.getD 0 0).toNat)
            (lns16ToSf16 (mean.getD 1 0).toNat)
            (lns16ToSf16 (mean.getD 2 0).toNat)
            (lns16ToSf16 (mean.getD 3 0).toNat)
        else cemBuf
    acc ++ block) []

end Texcomp
