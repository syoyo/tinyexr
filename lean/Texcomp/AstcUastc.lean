/-
  TinyEXR - Lean 4 formalization of the ASTC UASTC LDR 4x4 block encoder.

  Ports `tc_encode_uastc_ldr_block` and its sub-encoders
  (`tc_uastc_encode_mode`, `tc_uastc_encode_cem4`, `tc_uastc_encode_msubset`,
  `tc_uastc_encode_dual`) plus the small helpers `tc_astc_block_is_solid`,
  `tc_astc_hdr_quant_weight`, `tc_astc_hdr_find_grid_mode` /
  `tc_astc_find_dual_grid_mode` and `tc_uastc_lum` from
  `tools/texcomp/src/texcomp_astc.c`.

  The C's three-round refine loops are unrolled (round 0 always stores its
  result, later rounds only on strict improvement, LSQ re-solve between
  rounds with break-on-failure), matching the reference exactly.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEval
import Texcomp.AstcFits
import Texcomp.AstcEncode
import Texcomp.AstcBlockMode
import Texcomp.AstcCandidates
import Texcomp.AstcEndpoints
import Texcomp.AstcColorQuant
import Texcomp.AstcPartition
import Texcomp.AstcPartitionSearch
import Texcomp.AstcWeightInfill
import Texcomp.AstcConstBlock

namespace Texcomp

set_option linter.unusedVariables false
set_option maxRecDepth 5000

/-- `UINT64_MAX` sentinel. -/
def astcUastcInf : Nat := 0xFFFFFFFFFFFFFFFF

/-- `tc_astc_block_is_solid`: every texel identical to the first. -/
def astcBlockIsSolid (block : List (List Nat)) (count : Nat) : Bool :=
  let p0 := block.getD 0 [0, 0, 0, 0]
  (List.range count).all (fun i =>
    let p := block.getD i [0, 0, 0, 0]
    (List.range 4).all (fun c => p.getD c 0 == p0.getD c 0))

/-- `tc_uastc_lum`. -/
def astcUastcLum (px : List Nat) : Nat :=
  (px.getD 0 0 + px.getD 1 0 + px.getD 2 0) / 3

/-- The encoder's unquantized weight value for a symbol. -/
def astcUastcUnquant (q qm : Nat) : Nat :=
  (astcWeightUnquantEnc.getD qm []).getD q 0

/-- `tc_astc_hdr_quant_weight`: nearest weight symbol by absolute distance
  (first minimum wins, `bestd` starts at `1 << 30`). -/
def astcUastcQuantWeight (w64 qm : Nat) : Nat :=
  let levels := astcQuantLevels.getD qm 2
  ((List.range levels).foldl (fun (st : Nat × Nat) q =>
    let uq := astcUastcUnquant q qm
    let ad := if uq ≥ w64 then uq - w64 else w64 - uq
    if ad < st.2 then (q, ad) else st) (0, 0x40000000)).1

/-- `tc_astc_hdr_find_grid_mode` / `tc_astc_find_dual_grid_mode`: the first
  4x4 single/dual-plane block mode at a weight quantizer. -/
def astcUastcGridMode (qm : Nat) (dual : Bool) : Option Nat :=
  (List.range 2048).find? (fun bm =>
    match astcEncBlockMode bm with
    | some m => m.wx == 4 && m.wy == 4 && (m.dual != 0) == dual && m.quant == qm
    | none => false)

/-- `tc_astc_color_symbol_uquant`. -/
def astcUastcSymUquant (er sym : Nat) : Nat :=
  colorSymbolUquant er sym

/-- Clamped projection of one texel onto the quantized endpoint direction
  over `chs`, scaled to [0,64] (the C's `w64`). -/
def astcUastcProjW (px qe0 : List Nat) (dir : List Int) (dl : Nat)
    (chs : List Nat) : Int :=
  if dl == 0 then 0
  else
    let dot := chs.foldl (fun acc c =>
      acc + (Int.ofNat (px.getD c 0) - Int.ofNat (qe0.getD c 0)) *
        dir.getD c 0) 0
    let dot := if dot < 0 then 0 else if dot > Int.ofNat dl then Int.ofNat dl
               else dot
    (dot * 64 + Int.ofNat (dl / 2)) / Int.ofNat dl

/-- One texel's squared reconstruction error over `chs` with per-channel
  weights `uqs` (the C's inline `(e0*(64-uq) + e1*uq + 32) >> 6`). -/
def astcUastcTexelErr (px qe0 qe1 : List Nat) (chs uqs : List Nat) : Nat :=
  (List.range chs.length).foldl (fun acc k =>
    let c := chs.getD k 0
    let uq := uqs.getD k 0
    let rc := (qe0.getD c 0 * (64 - uq) + qe1.getD c 0 * uq + 32) >>> 6
    let e : Int := Int.ofNat (px.getD c 0) - Int.ofNat rc
    acc + (e * e).toNat) 0

/-- Scramble + ISE the weights, bit-reverse into the 16 block bytes. -/
def astcUastcWeightBytes (qm : Nat) (wsym : List Nat) (dualWeights : Bool) :
    List Nat :=
  let nW := if dualWeights then 32 else 16
  let wsymS := astcScrambleWeights wsym nW qm
  let (weightbuf, _) := astcIseEncodeBits qm nW wsymS (List.replicate 16 0) 0 16
  (List.range 16).map (fun i => bitrev8 (weightbuf.getD (15 - i) 0))

/-- Per-texel endpoint lists induced by a subset map. -/
def astcUastcPerTexel (count : Nat) (partOf : List Nat)
    (qe0 qe1 : List (List Nat)) : List (List Nat) × List (List Nat) :=
  ((List.range count).map (fun i => qe0.getD (partOf.getD i 0) []),
   (List.range count).map (fun i => qe1.getD (partOf.getD i 0) []))

/-- One `tc_uastc_encode_mode` refinement round: quantize the endpoints,
  project the texels, quantize the weights, score the reconstruction.
  Returns `(sse, sym, wsym, wt)`. -/
def astcUastcModeRound (block : List (List Nat)) (count cem nv er qm nch : Nat)
    (chs : List Nat) (rlo rhi : List Nat) :
    Nat × List Nat × List Nat × List Nat :=
  let values := [rlo.getD 0 0, rhi.getD 0 0, rlo.getD 1 0, rhi.getD 1 0,
                 rlo.getD 2 0, rhi.getD 2 0] ++
    (if cem == 12 then [rlo.getD 3 0, rhi.getD 3 0] else [])
  let sym := astcQuantizeColorValues er nv values
  let qe0 := chs.map (fun c => astcUastcSymUquant er (sym.getD (c * 2) 0))
  let qe1 := chs.map (fun c => astcUastcSymUquant er (sym.getD (c * 2 + 1) 0))
  let qe0f := if cem == 12 then qe0 else qe0 ++ [255]
  let qe1f := if cem == 12 then qe1 else qe1 ++ [255]
  let dir := chs.map (fun c =>
    Int.ofNat (qe1.getD c 0) - Int.ofNat (qe0.getD c 0))
  let dl := chs.foldl (fun acc c => acc + (dir.getD c 0 * dir.getD c 0).toNat) 0
  let (wsym, wt) := (List.range count).foldl
    (fun (s : List Nat × List Nat) i =>
      let px := block.getD i [0, 0, 0, 0]
      let w64 := astcUastcProjW px qe0 dir dl chs |>.toNat
      let w := astcUastcQuantWeight w64 qm
      (s.1 ++ [w], s.2 ++ [astcUastcUnquant w qm]))
    ([], [])
  let sse := astcReconSse block count qe0f qe1f wt
  (sse, sym, wsym, wt)

/-- `tc_uastc_encode_mode`: single-subset CEM 8/12 with a fixed 4x4 grid at
  weight range `qm`. Returns the packed block and its SSE. -/
def astcUastcEncodeMode (block : List (List Nat)) (count cem nv qm : Nat)
    (lo hi : List Nat) : Option (List Nat × Nat) :=
  match astcUastcGridMode qm false with
  | none => none
  | some bm =>
    let weightBits := iseBitcount 16 qm
    if weightBits ≥ 111 then none
    else
      let colorBits := 111 - weightBits
      match astcLutColorQuant nv colorBits with
      | none => none
      | some er =>
        let nch := if cem == 12 then 4 else 3
        let chs := List.range nch
        let round := astcUastcModeRound block count cem nv er qm nch chs
        -- round 0: bounding-box endpoints; always stores
        let (sse0, sym0, wsym0, wt0) := round lo hi
        let best0 := some (sse0, sym0, wsym0)
        let best :=
          match astcLsqEndpoints block count wt0 with
          | none => best0
          | some (lo1, hi1) =>
            let (sse1, sym1, wsym1, wt1) := round lo1 hi1
            if sse1 < sse0 then
              let best1 := some (sse1, sym1, wsym1)
              match astcLsqEndpoints block count wt1 with
              | none => best1
              | some (lo2, hi2) =>
                let (sse2, sym2, wsym2, _) := round lo2 hi2
                if sse2 < sse1 then some (sse2, sym2, wsym2) else best1
            else best0
        match best with
        | none => none
        | some (best, sym0, wsym0) =>
          -- ascending-sum ordering to avoid the decoder's blue-contract path
          let sLo := astcUastcSymUquant er (sym0.getD 0 0) +
            astcUastcSymUquant er (sym0.getD 2 0) +
            astcUastcSymUquant er (sym0.getD 4 0)
          let sHi := astcUastcSymUquant er (sym0.getD 1 0) +
            astcUastcSymUquant er (sym0.getD 3 0) +
            astcUastcSymUquant er (sym0.getD 5 0)
          let pc := if cem == 12 then 4 else 3
          let (sym, wsym) :=
            if sLo > sHi then
              let vals := (List.range pc).foldl (fun (acc : List Nat) k =>
                acc ++ [sym0.getD (k * 2 + 1) 0, sym0.getD (k * 2) 0]) []
              (vals, astcInvertWeights wsym0 16 qm)
            else (sym0, wsym0)
          let out := astcUastcWeightBytes qm wsym false
          let (out, _) := astcSetBits out 0 11 bm
          let (out, _) := astcSetBits out 11 2 0
          let (out, _) := astcSetBits out 13 4 cem
          let (out, _) := astcIseEncodeBits er nv sym out 17 16
          some (out, best)

/-- Per-subset `(L0,L1,A0,A1)` quantization for `tc_uastc_encode_cem4`:
  symbols, reconstructed endpoints, direction and `dl` per subset. -/
def astcUastcCem4Quant (nsub er : Nat) (rlo rhi : List (List Nat)) :
    List (List Nat) × List (List Nat) × List (List Nat) × List (List Int) ×
    List Nat :=
  let seg := (List.range nsub).map (fun s =>
    let rl := rlo.getD s [0, 0, 0, 0]
    let rh := rhi.getD s [0, 0, 0, 0]
    let vals := [rl.getD 0 0, rh.getD 0 0, rl.getD 3 0, rh.getD 3 0]
    let sym := astcQuantizeColorValues er 4 vals
    let l0 := astcUastcSymUquant er (sym.getD 0 0)
    let l1 := astcUastcSymUquant er (sym.getD 1 0)
    let a0 := astcUastcSymUquant er (sym.getD 2 0)
    let a1 := astcUastcSymUquant er (sym.getD 3 0)
    let qe0 := [l0, l0, l0, a0]
    let qe1 := [l1, l1, l1, a1]
    let dir := (List.range 4).map (fun c =>
      Int.ofNat (qe1.getD c 0) - Int.ofNat (qe0.getD c 0))
    let dl := (List.range 4).foldl (fun acc c =>
      acc + (dir.getD c 0 * dir.getD c 0).toNat) 0
    (sym, qe0, qe1, dir, dl))
  (seg.map (fun x => x.1), seg.map (fun x => x.2.1), seg.map (fun x => x.2.2.1),
   seg.map (fun x => x.2.2.2.1), seg.map (fun x => x.2.2.2.2))

/-- `tc_uastc_encode_cem4`: luminance+alpha modes — 15 (nsub 1), 16
  (nsub 2, partitioned) and 17 (single subset, dual-plane). Returns the
  packed block and its SSE. -/
def astcUastcEncodeCem4 (block : List (List Nat)) (count nsub dual qm : Nat)
    (bx by_ : Nat) : Option (List Nat × Nat) :=
  match astcUastcGridMode qm (dual != 0) with
  | none => none
  | some bm =>
    let dualB := dual != 0
    let nvw := if dualB then 32 else 16
    let weightBits := iseBitcount nvw qm
    let budgetOk :=
      if dualB then weightBits + 2 < 109
      else if nsub > 1 then weightBits < 99
      else weightBits < 111
    if !budgetOk then none
    else
      let colorBits :=
        if dualB then 109 - weightBits
        else if nsub > 1 then 99 - weightBits
        else 111 - weightBits
      match astcLutColorQuant (nsub * 4) colorBits with
      | none => none
      | some er =>
        -- partition (the C passes ctx->part2_cache; 2 subsets only)
        let partOf : List Nat :=
          if nsub > 1 then
            match astcFindBestPartition block bx by_ 2 with
            | some (piIdx, true) =>
              (astcBuildPartitionCache bx by_ 2).getD piIdx
                (0, [], [], []) |>.2.1
            | _ => []
          else List.range count
        if nsub > 1 && partOf.length != count then none
        else
          let blkLum := (List.range count).map (fun i =>
            let L := astcUastcLum (block.getD i [0, 0, 0, 0])
            [L, L, L, (block.getD i [0, 0, 0, 0]).getD 3 0])
          -- per-subset (Llo, Lhi, Alo, Ahi); an empty subset fails
          let bbox := (List.range nsub).map (fun s =>
            (List.range count).foldl
              (fun (a : Option (Nat × Nat × Nat × Nat)) i =>
                if partOf.getD i 0 != s then a else
                let px := block.getD i [0, 0, 0, 0]
                let L := astcUastcLum px
                match a with
                | none => some (L, L, px.getD 3 0, px.getD 3 0)
                | some (llo, lhi, alo, ahi) =>
                  some (min llo L, max lhi L, min alo (px.getD 3 0),
                        max ahi (px.getD 3 0)))
              none)
          if bbox.any (fun b => b.isNone) then none
          else
            let rlo := bbox.map (fun b =>
              let (llo, _, _, alo) := (b.getD (0, 0, 0, 0))
              [llo, llo, llo, alo])
            let rhi := bbox.map (fun b =>
              let (_, lhi, _, ahi) := (b.getD (0, 0, 0, 0))
              [lhi, lhi, lhi, ahi])
            if dualB then
              -- mode 17: bbox endpoints kept, best CCS by SSE
              let (syms, qe0s, qe1s, dirs, _) := astcUastcCem4Quant nsub er rlo rhi
              let qe0 := qe0s.getD 0 []
              let qe1 := qe1s.getD 0 []
              let dir := dirs.getD 0 []
              let (bestCcs, bestSse, bestP1, bestP2) :=
                (List.range 4).foldl
                  (fun (st : Nat × Nat × List Nat × List Nat) ccs =>
                    let d1 := (List.range 4).foldl (fun acc c =>
                      if c != ccs then
                        acc + (dir.getD c 0 * dir.getD c 0).toNat
                      else acc) 0
                    let d2 := (dir.getD ccs 0 * dir.getD ccs 0).toNat
                    let (t1, t2, dsse) := (List.range count).foldl
                      (fun (st3 : List Nat × List Nat × Nat) i =>
                        let (s1, s2, s3) := st3
                        let px := block.getD i [0, 0, 0, 0]
                        let w1 := (astcUastcProjW px qe0 dir d1
                          ((List.range 4).filter (fun c => c != ccs))).toNat
                        let w2 := (astcUastcProjW px qe0 dir d2 [ccs]).toNat
                        let q1 := astcUastcQuantWeight w1 qm
                        let q2 := astcUastcQuantWeight w2 qm
                        let u1 := astcUastcUnquant q1 qm
                        let u2 := astcUastcUnquant q2 qm
                        let uqs := (List.range 4).map (fun c =>
                          if c == ccs then u2 else u1)
                        (s1 ++ [q1], s2 ++ [q2],
                          s3 + astcUastcTexelErr px qe0 qe1
                            (List.range 4) uqs))
                      ([], [], 0)
                    if st.1 == 99 || dsse < st.2.1 then
                      (ccs, dsse, t1, t2) else st)
                  (99, 0, [], [])
              let dualw := (List.range 16).foldl (fun (acc : List Nat) i =>
                acc ++ [bestP1.getD i 0, bestP2.getD i 0]) []
              let out := astcUastcWeightBytes qm dualw true
              let (out, _) := astcSetBits out 0 11 bm
              let (out, _) := astcSetBits out 11 2 0
              let (out, _) := astcSetBits out 13 4 4 -- CEM 4
              let (out, _) := astcSetBits out (128 - weightBits - 2) 2 bestCcs
              let (out, _) := astcIseEncodeBits er 4 (syms.getD 0 []) out 17 16
              some (out, bestSse)
            else
              -- modes 15/16: 3 refine rounds on the luminance block
              let rnd := fun (rlo rhi : List (List Nat)) =>
                let (syms, qe0s, qe1s, dirs, dls) :=
                  astcUastcCem4Quant nsub er rlo rhi
                let (wsym, wt) := (List.range count).foldl
                  (fun (s : List Nat × List Nat) i =>
                    let s2 := partOf.getD i 0
                    let px := block.getD i [0, 0, 0, 0]
                    let w64 := (astcUastcProjW px (qe0s.getD s2 [])
                      (dirs.getD s2 []) (dls.getD s2 0) (List.range 4)).toNat
                    let w := astcUastcQuantWeight w64 qm
                    (s.1 ++ [w], s.2 ++ [astcUastcUnquant w qm]))
                  ([], [])
                let (e0t, e1t) := astcUastcPerTexel count partOf qe0s qe1s
                let sse := astcReconSsePt block count e0t e1t wt
                (syms, wsym, wt, sse)
              let lsqAll := fun (rlo rhi : List (List Nat)) (wt : List Nat) =>
                (List.range nsub).foldl
                  (fun (acc : List (List Nat) × List (List Nat)) s =>
                    let lsq :=
                      if nsub > 1 then
                        astcLsqEndpointsPartition blkLum count partOf s wt
                      else astcLsqEndpoints blkLum count wt
                    match lsq with
                    | none => acc
                    | some (l, h) => (acc.1.set s l, acc.2.set s h))
                  (rlo, rhi)
              let (syms0, wsym0, wt0, sse0) := rnd rlo rhi
              let best0 := some (sse0, syms0, wsym0)
              let (rlo1, rhi1) := lsqAll rlo rhi wt0
              let (syms1, wsym1, wt1, sse1) := rnd rlo1 rhi1
              let best12 :=
                if sse1 < sse0 then
                  let best1 := some (sse1, syms1, wsym1)
                  let (rlo2, rhi2) := lsqAll rlo1 rhi1 wt1
                  let (syms2, wsym2, _, sse2) := rnd rlo2 rhi2
                  if sse2 < sse1 then some (sse2, syms2, wsym2) else best1
                else best0
              match best12 with
              | none => none
              | some (best, syms, wsym) =>
                let sym := syms.foldl (fun acc s => acc ++ s) []
                let out := astcUastcWeightBytes qm wsym false
                let (out, _) := astcSetBits out 0 11 bm
                if nsub > 1 then
                  let piIdx := match astcFindBestPartition block bx by_ 2 with
                    | some (piIdx, _) => piIdx | none => 0
                  let piSeed := (astcBuildPartitionCache bx by_ 2).getD piIdx
                    (0, [], [], []) |>.1
                  let (out, _) := astcSetBits out 11 2 (nsub - 1)
                  let (out, _) := astcSetBits out 13 6 (piSeed &&& 63)
                  let (out, _) := astcSetBits out 19 4 (piSeed >>> 6)
                  let (out, _) := astcSetBits out 23 6 (4 <<< 2)
                  let (out, _) := astcIseEncodeBits er (nsub * 4) sym out 29 16
                  some (out, best)
                else
                  let (out, _) := astcSetBits out 11 2 0
                  let (out, _) := astcSetBits out 13 4 4 -- CEM 4
                  let (out, _) := astcIseEncodeBits er 4 sym out 17 16
                  some (out, best)

/-- `tc_uastc_encode_msubset`: multi-subset CEM 8 (2/3 subsets) / CEM 12
  (2 subsets). Per-subset bounding boxes, shared weights, blue-contract
  ordering check, 3 refine rounds. -/
def astcUastcEncodeMsubset (block : List (List Nat))
    (count cem nsub qm quality : Nat) (bx by_ : Nat) :
    Option (List Nat × Nat) :=
  -- the C builds the 3-partition cache only when ctx->quality > 1
  if nsub == 3 && quality ≤ 1 then none
  else
    match astcUastcGridMode qm false with
    | none => none
    | some bm =>
      let nvs := if cem == 12 then 8 else 6
      let nch := if cem == 12 then 4 else 3
      let chs := List.range nch
      let weightBits := iseBitcount 16 qm
      if weightBits ≥ 99 then none
      else
        let colorBits := 99 - weightBits
        match astcLutColorQuant (nsub * nvs) colorBits with
        | none => none
        | some er =>
          match astcFindBestPartition block bx by_ nsub with
          | some (piIdx, true) =>
            let cache := astcBuildPartitionCache bx by_ nsub
            let piEntry := cache.getD piIdx (0, [], [], [])
            let partOf := piEntry.2.1
            let piSeed := piEntry.1
            -- per-subset 4-channel bbox; an empty subset fails
            let bbox := (List.range nsub).map (fun s =>
              (List.range count).foldl
                (fun (a : Option (List Nat × List Nat)) i =>
                  if partOf.getD i 0 != s then a else
                  let px := block.getD i [0, 0, 0, 0]
                  match a with
                  | none => some (px, px)
                  | some (lo4, hi4) =>
                    some ((List.range 4).map (fun c =>
                            min (lo4.getD c 0) (px.getD c 0)),
                          (List.range 4).map (fun c =>
                            max (hi4.getD c 0) (px.getD c 0))))
                none)
            if bbox.any (fun b => b.isNone) then none
            else
              let rlo := bbox.map (fun b => (b.getD ([], [])).1)
              let rhi := bbox.map (fun b => (b.getD ([], [])).2)
              -- one round: quantize per subset (ordering check), project,
              -- quantize weights, score through per-subset endpoints
              let rnd := fun (rlo rhi : List (List Nat)) =>
                let seg := (List.range nsub).foldl
                  (fun (st : Option (List Nat × List (List Nat) ×
                          List (List Nat) × List (List Int) × List Nat)) s =>
                    match st with
                    | none => none
                    | some (syms, qe0s, qe1s, dirs, dls) =>
                      let rl := rlo.getD s []
                      let rh := rhi.getD s []
                      let vals := [rl.getD 0 0, rh.getD 0 0, rl.getD 1 0,
                                   rh.getD 1 0, rl.getD 2 0, rh.getD 2 0] ++
                        (if cem == 12 then [rl.getD 3 0, rh.getD 3 0] else [])
                      let sym := astcQuantizeColorValues er nvs vals
                      let qe0 := chs.map (fun c =>
                        astcUastcSymUquant er (sym.getD (c * 2) 0))
                      let qe1 := chs.map (fun c =>
                        astcUastcSymUquant er (sym.getD (c * 2 + 1) 0))
                      let qe0f := if cem == 12 then qe0 else qe0 ++ [255]
                      let qe1f := if cem == 12 then qe1 else qe1 ++ [255]
                      if qe0.getD 0 0 + qe0.getD 1 0 + qe0.getD 2 0 >
                         qe1.getD 0 0 + qe1.getD 1 0 + qe1.getD 2 0 then none
                      else
                        let dir := chs.map (fun c =>
                          Int.ofNat (qe1.getD c 0) - Int.ofNat (qe0.getD c 0))
                        let dl := chs.foldl (fun acc c =>
                          acc + (dir.getD c 0 * dir.getD c 0).toNat) 0
                        some (syms ++ sym, qe0s ++ [qe0f], qe1s ++ [qe1f],
                              dirs ++ [dir], dls ++ [dl]))
                  (some ([], [], [], [], []))
                match seg with
                | none => none
                | some (syms, qe0s, qe1s, dirs, dls) =>
                  let (wsym, wt) := (List.range count).foldl
                    (fun (s : List Nat × List Nat) i =>
                      let s2 := partOf.getD i 0
                      let px := block.getD i [0, 0, 0, 0]
                      let w64 := (astcUastcProjW px (qe0s.getD s2 [])
                        (dirs.getD s2 []) (dls.getD s2 0) chs).toNat
                      let w := astcUastcQuantWeight w64 qm
                      (s.1 ++ [w], s.2 ++ [astcUastcUnquant w qm]))
                    ([], [])
                  let (e0t, e1t) := astcUastcPerTexel count partOf qe0s qe1s
                  let sse := astcReconSsePt block count e0t e1t wt
                  some (syms, wsym, wt, sse)
              let lsqAll := fun (rlo rhi : List (List Nat)) (wt : List Nat) =>
                (List.range nsub).foldl
                  (fun (acc : List (List Nat) × List (List Nat)) s =>
                    match astcLsqEndpointsPartition block count partOf s wt with
                    | none => acc
                    | some (l, h) => (acc.1.set s l, acc.2.set s h))
                  (rlo, rhi)
              match rnd rlo rhi with
              | none => none
              | some (syms0, wsym0, wt0, sse0) =>
                let best0 := some (sse0, syms0, wsym0)
                let (rlo1, rhi1) := lsqAll rlo rhi wt0
                let best12 :=
                  match rnd rlo1 rhi1 with
                  | none => best0
                  | some (syms1, wsym1, wt1, sse1) =>
                    if sse1 < sse0 then
                      let best1 := some (sse1, syms1, wsym1)
                      let (rlo2, rhi2) := lsqAll rlo1 rhi1 wt1
                      match rnd rlo2 rhi2 with
                      | none => best1
                      | some (syms2, wsym2, _, sse2) =>
                        if sse2 < sse1 then some (sse2, syms2, wsym2) else best1
                    else best0
                match best12 with
                | none => none
                | some (best, syms, wsym) =>
                  let sym := syms
                  let out := astcUastcWeightBytes qm wsym false
                  let (out, _) := astcSetBits out 0 11 bm
                  let (out, _) := astcSetBits out 11 2 (nsub - 1)
                  let (out, _) := astcSetBits out 13 6 (piSeed &&& 63)
                  let (out, _) := astcSetBits out 19 4 (piSeed >>> 6)
                  let (out, _) := astcSetBits out 23 6 (cem <<< 2)
                  let (out, _) := astcIseEncodeBits er (nsub * nvs) sym out 29 16
                  some (out, best)
          | _ => none

/-- `tc_uastc_encode_dual`: dual-plane CEM 8 (mode 6) / CEM 12 (modes
  11/13). Single subset, one channel (the CCS) on a second weight plane;
  best CCS by SSE, 3 refine rounds re-solving both planes. -/
def astcUastcEncodeDual (block : List (List Nat)) (count cem qm : Nat) :
    Option (List Nat × Nat) :=
  match astcUastcGridMode qm true with
  | none => none
  | some bm =>
    let nv := if cem == 12 then 8 else 6
    let nch := if cem == 12 then 4 else 3
    let chs := List.range nch
    let weightBits := iseBitcount 32 qm
    if weightBits + 2 ≥ 109 then none
    else
      let colorBits := 109 - weightBits
      match astcLutColorQuant nv colorBits with
      | none => none
      | some er =>
        -- 4-channel bounding box
        let (rlo0, rhi0) := (List.range count).foldl
          (fun (a : List Nat × List Nat) i =>
            let px := block.getD i [0, 0, 0, 0]
            ((List.range 4).map (fun c => min (a.1.getD c 255) (px.getD c 0)),
             (List.range 4).map (fun c => max (a.2.getD c 0) (px.getD c 0))))
          ([255, 255, 255, 255], [0, 0, 0, 0])
        let roundSeg := fun (rlo rhi : List Nat) =>
          let vals := [rlo.getD 0 0, rhi.getD 0 0, rlo.getD 1 0, rhi.getD 1 0,
                       rlo.getD 2 0, rhi.getD 2 0] ++
            (if cem == 12 then [rlo.getD 3 0, rhi.getD 3 0] else [])
          let sym := astcQuantizeColorValues er nv vals
          let qe0 := chs.map (fun c => astcUastcSymUquant er (sym.getD (c * 2) 0))
          let qe1 := chs.map (fun c =>
            astcUastcSymUquant er (sym.getD (c * 2 + 1) 0))
          if qe0.getD 0 0 + qe0.getD 1 0 + qe0.getD 2 0 >
             qe1.getD 0 0 + qe1.getD 1 0 + qe1.getD 2 0 then none
          else some (sym, qe0, qe1)
        let ccsPass := fun (qe0 qe1 : List Nat) =>
          let dir := chs.map (fun c =>
            Int.ofNat (qe1.getD c 0) - Int.ofNat (qe0.getD c 0))
          (List.range nch).foldl
            (fun (st : Nat × Nat × List Nat × List Nat × List Nat ×
                  List Nat) ccs =>
              let d1 := chs.foldl (fun acc c =>
                if c != ccs then acc + (dir.getD c 0 * dir.getD c 0).toNat
                else acc) 0
              let d2 := (dir.getD ccs 0 * dir.getD ccs 0).toNat
              let (t1, t2, dsse, u1s, u2s) := (List.range count).foldl
                (fun (st5 : List Nat × List Nat × Nat × List Nat × List Nat) i =>
                  let (s1, s2, s3, s4, s5) := st5
                  let px := block.getD i [0, 0, 0, 0]
                  let w1 := (astcUastcProjW px qe0 dir d1
                    (chs.filter (fun c => c != ccs))).toNat
                  let w2 := (astcUastcProjW px qe0 dir d2 [ccs]).toNat
                  let q1 := astcUastcQuantWeight w1 qm
                  let q2 := astcUastcQuantWeight w2 qm
                  let u1 := astcUastcUnquant q1 qm
                  let u2 := astcUastcUnquant q2 qm
                  let uqs := chs.map (fun c => if c == ccs then u2 else u1)
                  (s1 ++ [q1], s2 ++ [q2],
                    s3 + astcUastcTexelErr px qe0 qe1 chs uqs,
                    s4 ++ [u1], s5 ++ [u2]))
                ([], [], 0, [], [])
              if st.1 == 99 || dsse < st.2.1 then
                (ccs, dsse, t1, t2, u1s, u2s) else st)
            (99, 0, [], [], [], [])
        -- round 0 (bbox endpoints; always stores)
        match roundSeg rlo0 rhi0 with
        | none => none
        | some (sym0, qe0, qe1) =>
          let (ccs0, sse0, p1_0, p2_0, wt1_0, wt2_0) := ccsPass qe0 qe1
          let best0 := some (sse0, sym0, ccs0, p1_0, p2_0, wt1_0, wt2_0)
          let best12 :=
            match astcLsqEndpoints block count wt1_0 with
            | none => best0
            | some (lo1, hi1) =>
              match astcLsqEndpoints block count wt2_0 with
              | none => best0
              | some (lo2, hi2) =>
                let rlo1 := (List.range 4).map (fun c =>
                  if c == ccs0 then lo2.getD c 0 else lo1.getD c 0)
                let rhi1 := (List.range 4).map (fun c =>
                  if c == ccs0 then hi2.getD c 0 else hi1.getD c 0)
                match roundSeg rlo1 rhi1 with
                | none => best0
                | some (sym1, qe0, qe1) =>
                  let (ccs1, sse1, p1_1, p2_1, wt1_1, wt2_1) := ccsPass qe0 qe1
                  if sse1 < sse0 then
                    let best1 := some (sse1, sym1, ccs1, p1_1, p2_1, wt1_1,
                      wt2_1)
                    match astcLsqEndpoints block count wt1_1 with
                    | none => best1
                    | some (lo1, hi1) =>
                      match astcLsqEndpoints block count wt2_1 with
                      | none => best1
                      | some (lo2, hi2) =>
                        let rlo2 := (List.range 4).map (fun c =>
                          if c == ccs1 then lo2.getD c 0 else lo1.getD c 0)
                        let rhi2 := (List.range 4).map (fun c =>
                          if c == ccs1 then hi2.getD c 0 else hi1.getD c 0)
                        match roundSeg rlo2 rhi2 with
                        | none => best1
                        | some (sym2, qe0, qe1) =>
                          let (ccs2, sse2, p1_2, p2_2, _, _) :=
                            ccsPass qe0 qe1
                          if sse2 < sse1 then
                            some (sse2, sym2, ccs2, p1_2, p2_2, [], [])
                          else best1
                  else best0
          match best12 with
          | none => none
          | some (best, sym, bestCcs, p1, p2, _, _) =>
            let dualw := (List.range 16).foldl (fun (acc : List Nat) i =>
              acc ++ [p1.getD i 0, p2.getD i 0]) []
            let out := astcUastcWeightBytes qm dualw true
            let (out, _) := astcSetBits out 0 11 bm
            let (out, _) := astcSetBits out 11 2 0
            let (out, _) := astcSetBits out 13 4 cem
            let (out, _) := astcSetBits out (128 - weightBits - 2) 2 bestCcs
            let (out, _) := astcIseEncodeBits er nv sym out 17 16
            some (out, best)

/-- `tc_encode_uastc_ldr_block`: the UASTC LDR 4x4 mode ladder. `quality`
  is the compress-time context quality (it decides whether the
  3-partition cache exists). -/
def astcEncodeUastcLdrBlock (block : List (List Nat)) (count quality bx by_ : Nat) :
    List Nat :=
  if astcBlockIsSolid block count then astcEncodeConstBlock block count
  else
    let opq := astcBlockIsOpaque block count
    let cem := if opq then 8 else 12
    let nv := if opq then 6 else 8
    let (lo, hi) := (List.range count).foldl
      (fun (a : List Nat × List Nat) i =>
        let px := block.getD i [0, 0, 0, 0]
        ((List.range 4).map (fun c => min (a.1.getD c 255) (px.getD c 0)),
         (List.range 4).map (fun c => max (a.2.getD c 0) (px.getD c 0))))
      ([255, 255, 255, 255], [0, 0, 0, 0])
    let tryAdd := fun (st : Option (List Nat × Nat))
        (mk : Option (List Nat × Nat)) =>
      match st, mk with
      | none, mk2 => mk2
      | some oe, none => st
      | some (o, e), some (o2, e2) =>
        if e2 < e then some (o2, e2) else some (o, e)
    -- single-subset modes
    let wr := if opq then [8, 5, 2, 11] else [8, 5, 2]
    let st0 := wr.foldl (fun st q =>
      tryAdd st (astcUastcEncodeMode block count cem nv q lo hi)) none
    -- 2-subset modes
    let sw := if opq then [5, 2] else [2]
    let st1 := sw.foldl (fun st q =>
      tryAdd st (astcUastcEncodeMsubset block count cem 2 q quality bx by_)) st0
    -- 3-subset mode (opaque only)
    let st2 := if opq then
      tryAdd st1 (astcUastcEncodeMsubset block count cem 3 2 quality bx by_)
      else st1
    -- dual-plane modes
    let dw := if opq then [2] else [2, 0]
    let st3 := dw.foldl (fun st q =>
      tryAdd st (astcUastcEncodeDual block count cem q)) st2
    -- CEM 4 modes (non-opaque only)
    let st4 :=
      if !opq then
        tryAdd (tryAdd (tryAdd st3
          (astcUastcEncodeCem4 block count 1 0 8 bx by_))
          (astcUastcEncodeCem4 block count 2 0 2 bx by_))
          (astcUastcEncodeCem4 block count 1 1 2 bx by_)
      else st3
    match st4 with
    | some (bytes, _) => bytes
    | none => astcEncodeConstBlock block count

end Texcomp
