/-
  TinyEXR - Lean 4 formalization of the BC7 PCA endpoint seed.

  Ports `tc_bc7_pca_extremes` in `tools/texcomp/src/texcomp_bc7.c`: the
  weighted principal-axis (covariance power iteration, 8 rounds) used to
  pick the two endpoint texels of a subset, and `tc_build_candidate`'s
  "try both seeds, keep the lower error" rule.

  The power iteration needs `1/sqrt(len)`; that square root is the
  correctly-rounded `Tocio.sqrtfExact` (bit-identical to libm's `sqrtf`,
  see `make tocio-sqrt-diff`), which is what makes this model tractable
  at all — the fast polynomial `Tocio.sqrtf` is only ~1e-6 accurate.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Seed
import Tocio.Math

open Tocio

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc7_pca_extremes`: the two texels at the extremes of the weighted
  principal colour axis of one subset. Returns `(minTexel, maxTexel)`.
  Ties go to the later texel, as C's `<=` / `>=` comparisons do. -/
def bc7PcaExtremes (pix : List (List Nat)) (part : List Nat) (subset : Nat)
    (includeAlpha : Bool) : Nat × Nat :=
  let nch := if includeAlpha then 4 else 3
  -- Channel weights: sqrt of the (default 1,1,1,1) error weights.
  let w : List Float32 := (List.range 4).map (fun _ => sqrtfExact 1.0)
  let texels := (List.range 16).filter (fun i => part.getD i 0 == subset)
  let cnt := texels.length
  if cnt == 0 then (0, 0)
  else
    let mean := (List.range nch).map (fun c =>
      Float32.ofNat (texels.foldl (fun acc i =>
        acc + (pix.getD i [0, 0, 0, 0]).getD c 0) 0) / Float32.ofNat cnt)
    -- Covariance of the weighted, mean-centred channels.
    let dv := fun (i c : Nat) =>
      w.getD c 1.0 * ((Float32.ofNat ((pix.getD i [0, 0, 0, 0]).getD c 0)) - mean.getD c 0.0)
    let cov := (List.range nch).map (fun c =>
      (List.range nch).map (fun d =>
        texels.foldl (fun acc i => acc + dv i c * dv i d) 0.0))
    -- Power iteration for the principal axis.
    let axis0 : List Float32 := (List.range nch).map (fun _ => 1.0)
    let iter (axis : List Float32) (_ : Nat) : List Float32 :=
      let na := (List.range nch).map (fun c =>
        (List.range nch).foldl (fun acc d =>
          acc + (cov.getD c []).getD d 0.0 * axis.getD d 0.0) 0.0)
      let len := (List.range nch).foldl (fun acc c =>
        acc + na.getD c 0.0 * na.getD c 0.0) 0.0
      if len < 1e-12 then axis
      else
        let inv := 1.0 / sqrtfExact len
        (List.range nch).map (fun c => na.getD c 0.0 * inv)
    let axis := (List.range 8).foldl iter axis0
    let proj := (List.range 16).map (fun i =>
      (List.range nch).foldl (fun acc c =>
        acc + axis.getD c 0.0 * dv i c) 0.0)
    let minP := texels.foldl (fun (acc : Float32 × Nat) i =>
      let p := proj.getD i 0.0
      if p <= acc.1 then (p, i) else acc) (1e30, 0)
    let maxP := texels.foldl (fun (acc : Float32 × Nat) i =>
      let p := proj.getD i 0.0
      if p >= acc.1 then (p, i) else acc) (-1e30, 0)
    (minP.2, maxP.2)

/-- The PCA-extreme seed (`tc_build_candidate_seed` with `use_pca = 1`).
  Alpha joins the axis only for the modes whose alpha shares the colour
  index (`mode >= 4 && !sep_alpha`), as in C. -/
def bc7SeedPca (mode partition : Nat) (pix : List (List Nat)) :
    Bc7Candidate × Nat :=
  let incA := mode ≥ 4 && bc7SepAlpha.getD mode 0 == 0
  bc7SeedWith (fun part subset => bc7PcaExtremes pix part subset incA) mode partition pix

/-- `tc_build_candidate`: the luma seed always, plus the PCA seed when
  `try_pca` is set, keeping the lower-error candidate (strict `<`). -/
def bc7BuildCandidate (mode partition : Nat) (pix : List (List Nat))
    (tryPca : Bool) : Bc7Candidate × Nat :=
  let (c0, e0) := bc7SeedLuma mode partition pix
  if !tryPca then (c0, e0)
  else
    let (c1, e1) := bc7SeedPca mode partition pix
    if e1 < e0 then (c1, e1) else (c0, e0)

end Texcomp
