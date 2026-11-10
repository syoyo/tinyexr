/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's block-mode candidates.

  Ports `tc_astc_footprint_index`, `tc_astc_candidate_rank`,
  `tc_astc_rank_block_mode_candidates`, `tc_astc_build_block_mode_candidates`
  and `tc_astc_build_dual_block_mode_candidates` from
  `tools/texcomp/src/texcomp_astc.c`: the valid block modes are filtered
  by plane count, weight-grid fit, quantisation budget and endpoint bit
  budget, deduplicated by `(weight_y, weight_x, quant)`, then stably
  insertion-sorted by the astcenc usage percentile (ties broken by a
  larger `weight_bits + weight_x*weight_y` merit).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcPartition
import Texcomp.AstcPercentiles

namespace Texcomp

set_option linter.unusedVariables false

/-- ASTC footprint table order (index 0..13), as in `tc_astc_footprint_index`. -/
def astcFootprints : List (Nat × Nat) :=
  [(4, 4), (5, 4), (5, 5), (6, 5), (6, 6), (8, 5), (8, 6),
   (8, 8), (10, 5), (10, 6), (10, 8), (10, 10), (12, 10), (12, 12)]

/-- `tc_astc_footprint_index`: `-1` for an unknown footprint. -/
def astcFootprintIndex (bx by_ : Nat) : Int :=
  match astcFootprints.findIdx? (fun p => p.1 == bx && p.2 == by_) with
  | some i => Int.ofNat i
  | none => -1

/-- `tc_astc_mode_percentile[fp][dual][wy-2][wx-2][quant]`, 65535 when
  unknown (`fp < 0`) or out of range. -/
def astcModePercentileAt (fp : Int) (dual wy wx quant : Nat) : Nat :=
  if fp < 0 then 65535
  else
    astcModePercentile.getD
      ((((fp.toNat * 2 + dual) * 11 + (wy - 2)) * 11 + (wx - 2)) * 12 + quant) 65535

/-- `tc_astc_candidate_rank`: percentile first, then higher merit first. -/
def astcCandidateRank (m : AstcEncMode) (fp : Int) (dual : Nat) : Nat :=
  let perc := astcModePercentileAt fp dual m.wy m.wx m.quant
  let merit := m.weightBits + m.wx * m.wy
  (perc <<< 16) ||| (0xFFFF - merit)

/-- `tc_astc_rank_block_mode_candidates`: stable insertion sort by rank. -/
def astcRankCandidates (cands : List AstcEncMode) (fp : Int) (dual : Nat) :
    List AstcEncMode :=
  cands.foldl (fun acc x =>
    let r := astcCandidateRank x fp dual
    let (before, after) := List.span (fun y => astcCandidateRank y fp dual ≤ r) acc
    before ++ [x] ++ after) []

/-- Shared filter/dedup pass; `dualPlane` selects single- or dual-plane modes
  and `extraBits` is the dual-plane endpoint overhead (2, else 0). -/
def astcBuildModeCandidates (bx by_ endpointEndBit : Nat) (quality : Nat)
    (dualPlane : Bool) : List AstcEncMode :=
  let maxQuant :=
    if dualPlane then (if quality > 1 then 11 else 5)
    else (if quality > 1 then 11 else if quality > 0 then 5 else 2)
  let extra := if dualPlane then 2 else 0
  let step (st : List AstcEncMode × List (Nat × Nat × Nat)) (mode : Nat) :=
    let (acc, seen) := st
    match astcEncBlockMode mode with
    | none => st
    | some m =>
      if (m.dual != 0) != dualPlane then st
      else if m.wx > bx || m.wy > by_ then st
      else if m.quant > maxQuant then st
      else if endpointEndBit + extra > 128 - m.weightBits then st
      else
        let key := (m.wy, m.wx, m.quant)
        if seen.contains key then st else (acc ++ [m], key :: seen)
  let (cands, _) := (List.range 2048).foldl step ([], [])
  astcRankCandidates cands (astcFootprintIndex bx by_) (if dualPlane then 1 else 0)

/-- `tc_astc_build_block_mode_candidates` (single plane). -/
def astcBuildBlockModeCandidates (bx by_ endpointEndBit : Nat) (quality : Nat) :
    List AstcEncMode :=
  astcBuildModeCandidates bx by_ endpointEndBit quality false

/-- `tc_astc_build_dual_block_mode_candidates` (dual plane). -/
def astcBuildDualBlockModeCandidates (bx by_ endpointEndBit : Nat) (quality : Nat) :
    List AstcEncMode :=
  astcBuildModeCandidates bx by_ endpointEndBit quality true

end Texcomp
