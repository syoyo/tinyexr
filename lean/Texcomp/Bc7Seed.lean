/-
  TinyEXR - Lean 4 formalization of the BC7 luma endpoint seed.

  Ports the non-`fast_select` path of `tc_build_candidate_seed` in
  `tools/texcomp/src/texcomp_bc7.c` for an explicit `(mode, partition)`:
  luma-extreme endpoint texels per subset, per-channel endpoint
  quantisation (p-bits and shared p-bits), palette reconstruction and
  nearest-index selection under `tc_err3` / `tc_err4` / `tc_err1`, plus
  the separate-alpha index plane. `tc_build_candidate` with
  `pca_endpoints = 0` is exactly this seed, so combined with
  `bc7PackCandidate` it reproduces the encoder's per-mode candidate for
  modes other than 6 (which additionally refines; see `Bc7Mode6`).

  The remaining boundary is the partition *choice* for modes 1 and 7
  (`tc_select_partition2`), the PCA seed variant, and the multi-mode
  winner selection.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Encode

namespace Texcomp

set_option linter.unusedVariables false

/-- Luma extremes among the texels of one subset. -/
def bc7SubsetExtremes (pix : List (List Nat)) (part : List Nat) (subset : Nat) :
    Nat × Nat :=
  let acc := (List.range 16).foldl (fun (acc : Nat × Nat × Nat × Nat) i =>
    if part.getD i 0 != subset then acc
    else
      let p := pix.getD i [0, 0, 0, 0]
      let y := bc7LumaU8 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0)
      let (minL, maxL, minI, maxI) := acc
      let minI' := if y < minL then i else minI
      let minL' := if y < minL then y else minL
      let maxI' := if y ≥ maxL then i else maxI
      let maxL' := if y ≥ maxL then y else maxL
      (minL', maxL', minI', maxI'))
    (0xFFFFFFFF, 0, 0, 0)
  (acc.2.2.1, acc.2.2.2)

/-- Endpoint data accumulated for one subset. -/
structure Bc7SubEndpoints where
  (lo hi pb : List Nat)
  deriving Repr

/-- `tc_build_candidate_seed` for an explicit mode/partition
  (`fast_select = 0`), parameterised by the endpoint-texel chooser so the
  luma and PCA seeds share the quantisation/index code. Returns
  `(candidate, totalErr)`. -/
def bc7SeedWith (extremes : List Nat → Nat → Nat × Nat)
    (mode partition : Nat) (pix : List (List Nat)) : Bc7Candidate × Nat :=
  let part := bc7PartitionFor mode partition
  let subsets := bc7NumSubsets.getD mode 1
  let colPrec := bc7ColorPrecision.getD mode 0
  let aPrec := bc7AlphaPrecision.getD mode 0
  let hasP := bc7HasPbits.getD mode 0
  let sharedP := bc7SharedPbits.getD mode 0
  let sepA := bc7SepAlpha.getD mode 0
  let quantSubset (subset : Nat) : Bc7SubEndpoints :=
    let (minI, maxI) := extremes part subset
    let pmin := pix.getD minI [0, 0, 0, 0]
    let pmax := pix.getD maxI [0, 0, 0, 0]
    (List.range 4).foldl (fun (acc : Bc7SubEndpoints) c =>
      if mode < 4 && c == 3 then
        { acc with lo := acc.lo ++ [0], hi := acc.hi ++ [0], pb := acc.pb ++ [0, 1] }
      else
        let prec := if c == 3 && mode ≥ 4 then aPrec else colPrec
        let hp := if hasP != 0 && (c < 3 || sepA == 0) then 1 else 0
        let shared := ((pmin.getD c 0 + pmax.getD c 0) >>> 1) &&& 1
        let (q0, p0) := bc7QuantEndpoint (pmin.getD c 0) prec hp sharedP shared
        let (q1, p1) := bc7QuantEndpoint (pmax.getD c 0) prec hp sharedP shared
        let pb := if sharedP != 0 then [shared, shared]
                  else if hp != 0 then [p0, p1]
                  else [0, 1]
        { acc with lo := acc.lo ++ [q0], hi := acc.hi ++ [q1], pb := pb })
      ⟨[], [], [0, 1]⟩
  let perSubset := (List.range subsets).map quantSubset
  let cand0 : Bc7Candidate :=
    { mode := mode, partition := partition, indexSelector := 0, rotation := 0,
      lo := perSubset.map (fun s => s.lo),
      hi := perSubset.map (fun s => s.hi),
      pbits := perSubset.map (fun s => s.pb),
      selectors := (List.range 16).map (fun _ => 0),
      alphaSelectors := (List.range 16).map (fun _ => 0) }
  let pal := bc7FillPalette cand0
  let cbits := bc7ColorIndexBits.getD mode 0 + cand0.indexSelector
  let abits := bc7AlphaIndexBits.getD mode 0 - cand0.indexSelector
  let nc := 1 <<< cbits
  let na := if abits != 0 then 1 <<< abits else nc
  let pick (i : Nat) : (Nat × Nat) × (Nat × Nat) :=
    let subset := part.getD i 0
    let palS := pal.getD subset []
    let p := pix.getD i [0, 0, 0, 0]
    let bestS := (List.range nc).foldl (fun (acc : Nat × Nat) s =>
      let r := palS.getD s [0, 0, 0, 0]
      let e := if sepA != 0 || mode < 4 then
          bc7Err4 p (r.getD 0 0) (r.getD 1 0) (r.getD 2 0) 0 false
        else bc7Err4 p (r.getD 0 0) (r.getD 1 0) (r.getD 2 0) (r.getD 3 0) true
      if e < acc.2 then (s, e) else acc) (0, 0xFFFFFFFF)
    let bestA := if sepA != 0 then
        (List.range na).foldl (fun (acc : Nat × Nat) s =>
          let r := palS.getD s [0, 0, 0, 0]
          let e := bc7Err4 [0, 0, 0, p.getD 3 0] 0 0 0 (r.getD 3 0) true
          if e < acc.2 then (s, e) else acc) (0, 0xFFFFFFFF)
      else (bestS.1, 0)
    (bestS, bestA)
  let picks := (List.range 16).map pick
  let err := picks.foldl (fun acc pr => acc + pr.1.2 + pr.2.2) 0
  let sels := picks.map (fun pr => pr.1.1)
  let asels := picks.map (fun pr => pr.2.1)
  let cand : Bc7Candidate := { cand0 with selectors := sels, alphaSelectors := asels }
  (cand, err)

/-- The luma-extreme seed (`tc_build_candidate_seed` with `use_pca = 0`). -/
def bc7SeedLuma (mode partition : Nat) (pix : List (List Nat)) :
    Bc7Candidate × Nat :=
  bc7SeedWith (fun part subset => bc7SubsetExtremes pix part subset) mode partition pix

/-- Encode one 4x4 block with a single explicit mode's luma-seeded
  candidate and pack it (no refinement; mode 6 uses `bc7EncodeBlockMode6`). -/
def bc7EncodeBlockSeed (mode : Nat) (pix : List (List Nat)) : List Nat :=
  let (cand, _) := bc7SeedLuma mode 0 pix
  bc7PackCandidate cand

end Texcomp
