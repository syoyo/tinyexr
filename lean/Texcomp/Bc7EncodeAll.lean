/-
  TinyEXR - Lean 4 formalization of the BC7 block encoder driver.

  Ports the partition choice and the mode loop of
  `tc_encode_bc7_all_modes_block` in `tools/texcomp/src/texcomp_bc7.c` for
  the default options (`quality = MEDIUM`, `quick = 2`,
  `pca_endpoints = 0`, `mode_mask = 0xFF`):

  * the alpha gate that drops modes 0–3 for translucent blocks,
  * `tc_select_partition2` in its quick form (the RGB/alpha partition LUT
    selected from the dominant-channel mask),
  * `tc_build_candidate` = luma seed (see `Texcomp.Bc7Seed`), plus
    `tc_bc7_refine_mode6` for mode 6 (see `Texcomp.Bc7Mode6`), and
  * the strict `err < best_err` winner selection.

  The PCA endpoint seed (`pca_endpoints = 1`) and the non-quick
  exhaustive partition search are the remaining boundary.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Pca
import Texcomp.Bc7Mode6

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_lookup_index_from_mask`. -/
def bc7LookupIndexFromMask (mask : Nat) : Nat :=
  match mask with
  | 11 => 0 | 12 => 1 | 18 => 2 | 21 => 3 | 33 => 4 | 38 => 5 | 56 => 6 | 63 => 7
  | _ => 0

/-- `tc_dominant_rgb_channel`. -/
def bc7DominantRgbChannel (p : List Nat) : Nat :=
  let r := p.getD 0 0
  let g := p.getD 1 0
  let b := p.getD 2 0
  if r > g then (if r > b then 0 else 2) else (if g > b then 1 else 2)

/-- Pairwise-equality bitmask over four class ids (the inner loop of
  `tc_rgb_partition_lut_index` / `tc_alpha_partition_lut_index`). -/
def bc7ClassMask (ch : List Nat) : Nat :=
  ((List.range 4).foldl (fun (acc : Nat × Nat) i =>
    (List.range 4).foldl (fun (acc2 : Nat × Nat) j =>
      if j ≤ i then acc2
      else
        let m := if ch.getD i 0 == ch.getD j 0 then acc2.1 ||| (1 <<< acc2.2) else acc2.1
        (m, acc2.2 + 1)) acc) (0, 0)).1

/-- `tc_rgb_partition_lut_index`. -/
def bc7RgbPartitionLutIndex (pix : List (List Nat)) : Nat :=
  let ids := [0, 1, 4, 5]
  let ch := ids.map (fun i => bc7DominantRgbChannel (pix.getD i [0, 0, 0, 0]))
  bc7LookupIndexFromMask (bc7ClassMask ch)

/-- `tc_alpha_partition_lut_index`. -/
def bc7AlphaPartitionLutIndex (pix : List (List Nat)) : Nat :=
  let ids := [0, 3, 12, 15]
  let acc := (List.range 16).foldl (fun (acc : Nat × Nat) i =>
    let a := (pix.getD i [0, 0, 0, 0]).getD 3 0
    (min acc.1 a, max acc.2 a)) (255, 0)
  let median := (acc.1 + acc.2) >>> 1
  let cls := ids.map (fun i =>
    if ((pix.getD i [0, 0, 0, 0]).getD 3 0) > median then 1 else 0)
  bc7LookupIndexFromMask (bc7ClassMask cls)

/-- First column of `tc_bc7_part_lut` (only `[.][0]` is used by the quick
  partition choice). -/
def bc7PartLutFirst : List Nat := [5, 34, 2, 16, 14, 17, 48, 0]

/-- First column of `tc_bc7_alpha_part_lut`. -/
def bc7AlphaPartLutFirst : List Nat := [4, 27, 0, 18, 10, 17, 5, 26]

/-- `tc_select_partition2` in its quick form (`opt->quick != 0`). -/
def bc7SelectPartition2Quick (mode : Nat) (pix : List (List Nat)) : Nat :=
  if mode == 7 then
    bc7AlphaPartLutFirst.getD (bc7AlphaPartitionLutIndex pix) 0
  else
    bc7PartLutFirst.getD (bc7RgbPartitionLutIndex pix) 0

/-- `tc_partition_cluster_score`: how well this 2-subset partition separates
  the block (larger is better). -/
def bc7PartitionClusterScore (pix : List (List Nat)) (partition : Nat)
    (includeAlpha : Bool) : Nat :=
  let part := (List.range 16).map (fun i =>
    bc7Partition2.getD ((partition &&& 63) * 16 + i) 0)
  let comps := if includeAlpha then 4 else 3
  let (sums, total, counts) :=
    (List.range 16).foldl (fun (acc : List (List Nat) × List Nat × List Nat) i =>
      let s := part.getD i 0
      let (sums, total, counts) := acc
      let px := pix.getD i [0, 0, 0, 0]
      let sums := (List.range 2).map (fun r =>
        if r != s then sums.getD r [0, 0, 0, 0]
        else (List.range 4).map (fun c =>
          (sums.getD r [0, 0, 0, 0]).getD c 0 +
            (if c < comps then px.getD c 0 else 0)))
      let total := (List.range 4).map (fun c =>
        total.getD c 0 + (if c < comps then px.getD c 0 else 0))
      let counts := (List.range 2).map (fun r =>
        counts.getD r 0 + (if r == s then 1 else 0))
      (sums, total, counts))
      ([[0, 0, 0, 0], [0, 0, 0, 0]], [0, 0, 0, 0], [0, 0])
  (List.range 2).foldl (fun (score : Nat) r =>
    if counts.getD r 0 == 0 then score
    else
      (List.range comps).foldl (fun (sc : Nat) c =>
        let d : Int := (Int.ofNat (16 * (sums.getD r [0, 0, 0, 0]).getD c 0)) -
          (Int.ofNat ((counts.getD r 0) * (total.getD c 0)))
        let ad := if d < 0 then -d else d
        sc + (ad * ad).toNat / (counts.getD r 0)) score) 0

/-- `tc_select_partition2` with the exhaustive (non-quick) search. -/
def bc7SelectPartition2Full (mode : Nat) (pix : List (List Nat)) : Nat :=
  ((List.range 64).foldl (fun (acc : Nat × Nat) i =>
    let score := bc7PartitionClusterScore pix i (mode == 7)
    if i == 0 || score > acc.2 then (i, score) else acc) (0, 0)).1

/-- `tc_select_partition2` with an explicit `quick` flag. -/
def bc7SelectPartition2 (quick : Bool) (mode : Nat) (pix : List (List Nat)) : Nat :=
  if quick then bc7SelectPartition2Quick mode pix else bc7SelectPartition2Full mode pix

/-- One mode's candidate: luma seed for the selected partition, plus the
  mode-6 refinement. -/
def bc7ModeCandidate (quick pca : Bool) (mode : Nat) (pix : List (List Nat)) :
    Bc7Candidate × Nat :=
  let partition := if mode == 1 || mode == 7 then bc7SelectPartition2 quick mode pix else 0
  let (cand, err) := bc7BuildCandidate mode partition pix pca
  if mode == 6 then bc7RefineMode6 pix cand err else (cand, err)

/-- `tc_encode_bc7_all_modes_block` at the default options: drop the
  opaque-only modes for translucent blocks, score each remaining mode, and
  keep the first strict winner. -/
def bc7EncodeBlockQuickPca (quick pca : Bool) (pix : List (List Nat)) : List Nat :=
  let hasAlpha := (List.range 16).any (fun i => ((pix.getD i [0, 0, 0, 0]).getD 3 0) < 255)
  let mask := if hasAlpha then 0xF0 else 0xFF
  let best := (List.range 8).foldl (fun (acc : List Nat × Nat) mode =>
    if (mask >>> mode) &&& 1 == 0 then acc
    else
      let (cand, err) := bc7ModeCandidate quick pca mode pix
      if err < acc.2 then (bc7PackCandidate cand, err) else acc)
    ((List.range 16).map (fun _ => 0), 0xFFFFFFFFFFFFFFFF)
  best.1

/-- `tc_encode_bc7_all_modes_block` with an explicit `quick` flag and PCA
  seeding choice. -/
def bc7EncodeBlockQuick (quick : Bool) (pix : List (List Nat)) : List Nat :=
  bc7EncodeBlockQuickPca quick false pix

/-- `tc_encode_bc7_all_modes_block` with the default options
  (`quick = 2`, `pca_endpoints = 0`). -/
def bc7EncodeBlockDefault (pix : List (List Nat)) : List Nat :=
  bc7EncodeBlockQuickPca true false pix

/-- The same driver with `pca_endpoints = 1`. -/
def bc7EncodeBlockPca (pix : List (List Nat)) : List Nat :=
  bc7EncodeBlockQuickPca true true pix

/-- The same driver with `opt->quick = 0`, i.e. the exhaustive partition
  search for modes 1 and 7. -/
def bc7EncodeBlockNonQuick (pix : List (List Nat)) : List Nat :=
  bc7EncodeBlockQuick false pix

end Texcomp
