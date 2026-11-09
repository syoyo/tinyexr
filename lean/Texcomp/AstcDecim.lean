/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's weight decimation.

  Ports `tc_astc_texel_weights_2d` and the per-entry aggregation in
  `tc_astc_get_decim_cache` from `tools/texcomp/src/texcomp_astc.c`: for
  each texel, the (up to four) weight-grid taps and their 1/16 fixed-point
  contributions, plus the per-tap contribution sums and the `direct` flag.
  The weighted infill (`tc_astc_infill_weights`) then uses these taps.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_texel_weights_2d`: the non-zero bilinear taps `(qweight, weight)`
  for one texel, in the C's tap order. -/
def astcTexelWeights2d (blockX blockY weightX weightY x y : Nat) :
    List (Nat × Nat) :=
  let xw := (((1024 + blockX / 2) / (blockX - 1)) * x * (weightX - 1) + 32) >>> 6
  let yw := (((1024 + blockY / 2) / (blockY - 1)) * y * (weightY - 1) + 32) >>> 6
  let xf := xw &&& 15
  let yf := yw &&& 15
  let xi := xw >>> 4
  let yi := yw >>> 4
  let q0 := xi + yi * weightX
  let prod := xf * yf
  let w3 := (prod + 8) >>> 4
  -- The first weight is `16 - x_frac - y_frac + w3` in C's uint32 arithmetic;
  -- it is always non-negative, but never truncate the intermediate `16 - xf -
  -- yf` with `Nat` subtraction.
  let ws : List Int :=
    [16 - Int.ofNat xf - Int.ofNat yf + Int.ofNat w3,
     Int.ofNat xf - Int.ofNat w3, Int.ofNat yf - Int.ofNat w3, Int.ofNat w3]
  let qs := [q0, q0 + 1, q0 + weightX, q0 + weightX + 1]
  (List.range 4).filterMap (fun k =>
    let w := ws.getD k 0
    if w != 0 then some (qs.getD k 0, w.toNat) else none)

/-- One decimation-cache entry: per-texel padded taps, per-weight-grid-tap
  contribution sums, and the `direct` flag. -/
def astcDecimEntry (blockX blockY weightX weightY : Nat) :
    List (List (Nat × Nat)) × List Nat × Bool :=
  let count := blockX * blockY
  let taps : List (List (Nat × Nat)) := (List.range count).map (fun i =>
    let t := astcTexelWeights2d blockX blockY weightX weightY (i % blockX) (i / blockX)
    let first := t.getD 0 (0, 0)
    t ++ List.replicate (4 - t.length) (first.1, 0))
  let contribs := (List.range count).foldl (fun (acc : List Nat) i =>
    (taps.getD i []).foldl (fun (a : List Nat) (q, w) =>
      a.set q (a.getD q 0 + w)) acc)
    (List.replicate 64 0)
  (taps, contribs, weightX == blockX && weightY == blockY)

end Texcomp
