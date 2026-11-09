/-
  TinyEXR - Lean 4 formalization of the BC7 mode-6 block encoder.

  Ports the mode-6 path of `tools/texcomp/src/texcomp_bc7.c`, which is
  what the fastest profile and a `mode_mask = 1 << 6` request use:

  * `tc_bc7_luma_extremes` (the seed endpoint texels),
  * `tc_build_candidate_seed(6, 0, ...)` for a single subset with shared
    indices (per-channel endpoint quantisation with p-bits, palette
    nearest-index selection under `tc_err4`),
  * `tc_bc7_refine_mode6` (one least-squares re-fit over the chosen
    indices, then a 2x2 p-bit search), and
  * `bc7PackCandidate` from `Texcomp.Bc7Encode` for the block bytes.

  The remaining encoder surface (the multi-mode/partition search for modes
  0–5 and 7, and the PCA seed) is the documented boundary.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7Encode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_luma_u8`: fixed-point luma. -/
def bc7LumaU8 (r g b : Nat) : Nat := r * 38 + g * 76 + b * 14

/-- `tc_err4` with the default {1,1,1,1} channel weights. -/
def bc7Err4 (a : List Nat) (r g b al : Nat) (hasAlpha : Bool) : Nat :=
  let dr := (Int.ofNat (a.getD 0 0)) - (Int.ofNat r)
  let dg := (Int.ofNat (a.getD 1 0)) - (Int.ofNat g)
  let db := (Int.ofNat (a.getD 2 0)) - (Int.ofNat b)
  let da := if hasAlpha then (Int.ofNat (a.getD 3 0)) - (Int.ofNat al) else 0
  (dr * dr + dg * dg + db * db + da * da).toNat

/-- `tc_bc7_luma_extremes` over a single subset (all 16 texels). -/
def bc7LumaExtremes (pix : List (List Nat)) : Nat × Nat :=
  let acc := (List.range 16).foldl (fun (acc : Nat × Nat × Nat × Nat) i =>
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

/-- Mode-6 seed: luma extremes + per-channel endpoint quantisation with
  p-bits, then nearest-index selection over the 16-entry palette.
  Returns `(candidate, totalErr)`. -/
def bc7Mode6Seed (pix : List (List Nat)) : Bc7Candidate × Nat :=
  let (minI, maxI) := bc7LumaExtremes pix
  let pmin := pix.getD minI [0, 0, 0, 0]
  let pmax := pix.getD maxI [0, 0, 0, 0]
  let prec := 7    -- tc_bc7_color_precision[6] == tc_bc7_alpha_precision[6]
  let mk (c : Nat) : ((Nat × Nat) × (Nat × Nat)) :=
    let shared := ((pmin.getD c 0 + pmax.getD c 0) >>> 1) &&& 1
    (bc7QuantEndpoint (pmin.getD c 0) prec 1 0 shared,
     bc7QuantEndpoint (pmax.getD c 0) prec 1 0 shared)
  let steps := (List.range 4).map mk
  let los := steps.map (fun s => s.1.1)
  let his := steps.map (fun s => s.2.1)
  -- C writes `pbits[subset][k]` inside the per-channel loop, so the last
  -- channel (c = 3) wins; mode 6 has p-bits on every channel.
  let last := steps.getD 3 ((0, 0), (0, 0))
  let pbs := [last.1.2, last.2.2]
  let cand0 : Bc7Candidate :=
    { mode := 6, partition := 0, indexSelector := 0, rotation := 0,
      lo := [los], hi := [his], pbits := [pbs],
      selectors := (List.range 16).map (fun _ => 0),
      alphaSelectors := (List.range 16).map (fun _ => 0) }
  let pal0 := (bc7FillPalette cand0).getD 0 []
  let nc := 1 <<< (bc7ColorIndexBits.getD 6 0 + cand0.indexSelector)
  let pick (i : Nat) : Nat × Nat :=
    let p := pix.getD i [0, 0, 0, 0]
    (List.range nc).foldl (fun (acc : Nat × Nat) s =>
      let r := pal0.getD s [0, 0, 0, 0]
      let e := bc7Err4 p (r.getD 0 0) (r.getD 1 0) (r.getD 2 0) (r.getD 3 0) true
      if e < acc.2 then (s, e) else acc) (0, 0xFFFFFFFF)
  let picks := (List.range 16).map pick
  let err := picks.foldl (fun acc p => acc + p.2) 0
  let csel := picks.map (fun p => p.1)
  let cand : Bc7Candidate := { cand0 with selectors := csel, alphaSelectors := csel }
  (cand, err)

/-- `tc_bc7_refine_mode6`: least-squares endpoint re-fit for the chosen
  indices, then a 2x2 p-bit search keeping the lowest error. -/
def bc7RefineMode6 (pix : List (List Nat)) (c0 : Bc7Candidate) (bestErr0 : Nat) :
    Bc7Candidate × Nat :=
  -- Normal equations over the current 4-bit indices.
  let sums := (List.range 16).foldl (fun (acc : Nat × Nat × Nat × List Int × List Int) i =>
    let w := bc7Weights4.getD (c0.selectors.getD i 0) 0
    let u := 64 - w
    let p := pix.getD i [0, 0, 0, 0]
    let (aa, ab, bb, sx0, sx1) := acc
    (aa + u * u, ab + u * w, bb + w * w,
     (List.range 4).map (fun c => sx0.getD c 0 + (Int.ofNat (p.getD c 0)) * (Int.ofNat u)),
     (List.range 4).map (fun c => sx1.getD c 0 + (Int.ofNat (p.getD c 0)) * (Int.ofNat w))))
    (0, 0, 0, [0, 0, 0, 0], [0, 0, 0, 0])
  let (aa, ab, bb, sx0, sx1) := sums
  let det : Int := (Int.ofNat aa) * (Int.ofNat bb) - (Int.ofNat ab) * (Int.ofNat ab)
  if det ≤ 0 then (c0, bestErr0)
  else
    let ideal := (List.range 4).map (fun c =>
      let lo := (Int.ofNat bb) * (sx0.getD c 0) - (Int.ofNat ab) * (sx1.getD c 0)
      let hi := (Int.ofNat aa) * (sx1.getD c 0) - (Int.ofNat ab) * (sx0.getD c 0)
      let lo := (lo + det / 2) / det
      let hi := (hi + det / 2) / det
      let cl := fun (x : Int) => if x < 0 then 0 else if x > 255 then 255 else x.toNat
      (cl lo, cl hi))
    -- 2x2 p-bit search.
    let tryP (p0 p1 : Nat) : Bc7Candidate × Nat :=
      let lo := ideal.map (fun (l, _) => Nat.min 127 ((l + 1 - p0) >>> 1))
      let hi := ideal.map (fun (_, h) => Nat.min 127 ((h + 1 - p1) >>> 1))
      let trial := { c0 with lo := [lo], hi := [hi], pbits := [[p0, p1]] }
      let pal := (bc7FillPalette trial).getD 0 []
      let picks := (List.range 16).map (fun i =>
        let p := pix.getD i [0, 0, 0, 0]
        (List.range 16).foldl (fun (acc : Nat × Nat) s =>
          let r := pal.getD s [0, 0, 0, 0]
          let e := bc7Err4 p (r.getD 0 0) (r.getD 1 0) (r.getD 2 0) (r.getD 3 0) true
          if e < acc.2 then (s, e) else acc) (0, 0xFFFFFFFF))
      let err := picks.foldl (fun acc p => acc + p.2) 0
      let csel := picks.map (fun p => p.1)
      let res : Bc7Candidate := { trial with selectors := csel, alphaSelectors := csel }
      (res, err)
    let candidates := [tryP 0 0, tryP 0 1, tryP 1 0, tryP 1 1]
    candidates.foldl (fun (best : Bc7Candidate × Nat) (cur : Bc7Candidate × Nat) =>
      if cur.2 < best.2 then cur else best) (c0, bestErr0)

/-- Encode one 4x4 RGBA block with the BC7 mode-6 path (seed + refine +
  pack), mirroring `tc_encode_bc7_all_modes_block` under
  `mode_mask = 1 << 6` at the default quality. -/
def bc7EncodeBlockMode6 (pix : List (List Nat)) : List Nat :=
  let (cand0, err0) := bc7Mode6Seed pix
  let (cand, _) := bc7RefineMode6 pix cand0 err0
  bc7PackCandidate cand

end Texcomp
