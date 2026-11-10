/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's score-from-ideal and
  score-batch kernels.

  Ports `tc_astc_score_from_ideal` (direct and non-direct, with and
  without an active mask) and `tc_astc_score_batch` (1..4 candidates) from
  `tools/texcomp/src/texcomp_astc.c`. The non-direct path reuses the
  `weights_from_ideal` accumulation and the fixed-point infill; the direct
  path is the `wq_err` table lookup. The batch returns the same per-candidate
  projection error as the scalar path (the AVX2/SSE2 batch variants are
  integer-exact by construction).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcFits

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_score_from_ideal`: projection error, scaled by 16 (returned
  as `err << 4`). `active = none` uses the all-texel path. -/
def astcScoreFromIdeal (blockX blockY weightX weightY qm : Nat)
    (ideal : List Nat) (active : Option (List Nat)) (count : Nat) : Nat :=
  let (taps, contribsEntry, direct) := astcDecimEntry blockX blockY weightX weightY
  let weightCount := weightX * weightY
  if direct then
    let err := (List.range count).foldl (fun acc i =>
      let use := match active with | none => true | some a => a.getD i 0 != 0
      if !use then acc
      else acc + astcWqErr qm (ideal.getD i 0)) 0
    err <<< 4
  else
    let (accum, contrib) := (List.range count).foldl
      (fun (st : List Nat × List Nat) i =>
        let use := match active with | none => true | some a => a.getD i 0 != 0
        if !use then st
        else
          (taps.getD i []).foldl (fun (s : List Nat × List Nat) (q, w) =>
            (s.1.set q (s.1.getD q 0 + ideal.getD i 0 * w),
             s.2.set q (s.2.getD q 0 + w))) st)
      ((List.range weightCount).map (fun _ => 0), (List.range weightCount).map (fun _ => 0))
    let contribs := match active with
      | none => contribsEntry
      | some _ => contrib
    let v := (List.range weightCount).map (fun k =>
      let c := contribs.getD k 0
      if c == 0 then 0 else (accum.getD k 0 + c / 2) / c)
    let grid := v.map (astcWqWt qm)
    let wt := astcInfillWeightsGrid grid blockX blockY weightX weightY
    let err := (List.range count).foldl (fun acc i =>
      let use := match active with | none => true | some a => a.getD i 0 != 0
      if !use then acc
      else
        let w := wt.getD i 0
        let d : Int := Int.ofNat w - Int.ofNat (ideal.getD i 0)
        acc + (d * d).toNat) 0
    err <<< 4

/-- `tc_astc_score_batch`: one projection error per candidate ideal. -/
def astcScoreBatch (blockX blockY weightX weightY qm : Nat)
    (ideals : List (List Nat)) (count : Nat) : List Nat :=
  ideals.map (fun ideal => astcScoreFromIdeal blockX blockY weightX weightY qm ideal none count)

end Texcomp
