/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's partition search and
  block classification.

  Ports `tc_astc_axis_extremes_rgba`, `tc_astc_bitmap_mismatch` (popcount
  form), `tc_astc_block_is_opaque`, `tc_astc_block_is_luminance`,
  `tc_astc_block_is_rgb_scale` and `tc_astc_find_best_partition` from
  `tools/texcomp/src/texcomp_astc.c`.

  The partition scan reproduces the two-partition estimation prefilter
  (RGBA 2-means, bitmap-mismatch shortlist) exactly, including the
  insertion order and the `worst_of_best` rejection test.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEval
import Texcomp.AstcPartition

namespace Texcomp

set_option linter.unusedVariables false

/-- Population count of a 64-bit word. -/
def astcPopcount64 (v : Nat) : Nat :=
  (List.range 64).foldl (fun acc i => acc + ((v >>> i) &&& 1)) 0

/-- `tc_astc_bitmap_mismatch`: the smaller of the direct and inverted
  popcount distances between the cluster bitmap and a seed's partition
  bitmap. -/
def astcBitmapMismatch (bbits seedBits mask : List Nat) (words : Nat) : Nat :=
  let allOnes := (1 <<< 64) - 1
  let direct := (List.range words).foldl (fun acc w =>
    acc + astcPopcount64 ((bbits.getD w 0 ^^^ seedBits.getD w 0) &&& mask.getD w 0)) 0
  let inverse := (List.range words).foldl (fun acc w =>
    acc + astcPopcount64
      ((bbits.getD w 0 ^^^ (allOnes - seedBits.getD w 0)) &&& mask.getD w 0)) 0
  if direct < inverse then direct else inverse

/-- `tc_astc_axis_extremes_rgba`: per-channel min/max texel indices. -/
def astcAxisExtremesRgba (block : List (List Nat)) (count : Nat) :
    List Nat × List Nat :=
  let step (st : List Nat × List Nat × List Nat × List Nat) (i : Nat) :=
    let (loKey, loI, hiKey, hiI) := st
    let row := block.getD i [0, 0, 0, 0]
    let f := fun (lk : List Nat) (li : List Nat) (hk : List Nat) (hi : List Nat) (c : Nat) =>
      let k := row.getD c 0
      let li := if k < lk.getD c 0xFFFFFFFF then li.set c i else li
      let lk := if k < lk.getD c 0xFFFFFFFF then lk.set c k else lk
      let hi := if k > hk.getD c 0 then hi.set c i else hi
      let hk := if k > hk.getD c 0 then hk.set c k else hk
      (lk, li, hk, hi)
    (List.range 4).foldl (fun (acc : List Nat × List Nat × List Nat × List Nat) c =>
      let (lk, li, hk, hi) := acc
      let (lk', li', hk', hi') := f lk li hk hi c
      (lk', li', hk', hi')) (loKey, loI, hiKey, hiI)
  let (_, loI, _, hiI) := (List.range count).foldl step
    ([0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], [0, 0, 0, 0],
     [0, 0, 0, 0], [0, 0, 0, 0])
  (loI, hiI)

/-- `tc_astc_block_is_opaque`. -/
def astcBlockIsOpaque (block : List (List Nat)) (count : Nat) : Bool :=
  (List.range count).all (fun i => (block.getD i [0, 0, 0, 0]).getD 3 0 == 255)

/-- `tc_astc_block_is_luminance`. -/
def astcBlockIsLuminance (block : List (List Nat)) (count : Nat) : Bool :=
  (List.range count).all (fun i =>
    let p := block.getD i [0, 0, 0, 0]
    p.getD 0 0 == p.getD 1 0 && p.getD 0 0 == p.getD 2 0)

/-- `tc_astc_block_is_rgb_scale`: whether every texel's non-major channels
  are proportional to the anchor texel's (within `6 * major`). -/
def astcBlockIsRgbScale (block : List (List Nat)) (count : Nat) : Bool :=
  let px := fun (i c : Nat) => (block.getD i [0, 0, 0, 0]).getD c 0
  let anchorPick := (List.range count).foldl (fun (acc : Nat × Nat) i =>
    let s := px i 0 + px i 1 + px i 2
    if s > acc.2 then (i, s) else acc) (0, 0)
  let bestSum := anchorPick.2
  let anchor := anchorPick.1
  if bestSum == 0 then false
  else
    let major := (List.range 3).foldl (fun (m : Nat) c =>
      if c == 0 then 0 else if px anchor c > px anchor m then c else m) 0
    let majorV := px anchor major
    if majorV == 0 then false
    else
      (List.range count).all (fun i =>
        (List.range 3).all (fun c =>
          if c == major then true
          else
            let a : Int := Int.ofNat (px i c) * Int.ofNat majorV
            let b : Int := Int.ofNat (px i major) * Int.ofNat (px anchor c)
            let d := if a > b then a - b else b - a
            d ≤ Int.ofNat (majorV * 6)))

/-- Insert one shortlist entry the way the C does: when full, the last slot
  is dropped and `mm >= worst` rejects the candidate outright. -/
def astcShortlistInsert (sl : List (Nat × Nat)) (limit mm idx : Nat) :
    List (Nat × Nat) :=
  let full := sl.length ≥ limit
  let worst := (sl.getD (sl.length - 1) (0, 0)).1
  if full && mm ≥ worst then sl
  else
    let base := if full then sl else sl ++ [(0, 0)]
    let pos := if full then sl.length - 1 else sl.length
    let (before, after) := List.span (fun e => e.1 ≤ mm) (base.take pos)
    before ++ [(mm, idx)] ++ after ++ base.drop (pos + 1)

/-- `tc_astc_find_best_partition`: returns the chosen cache index and the
  C's boolean (whether the best partition is worth using). `none` when C
  returns with `*out_pi == NULL`. -/
def astcFindBestPartition (block : List (List Nat)) (blockX blockY
    partitionCount : Nat) : Option (Nat × Bool) :=
  let texelCount := blockX * blockY
  let cache := astcBuildPartitionCache blockX blockY partitionCount
  let cacheCount := cache.length
  let px := fun (i c : Nat) => (block.getD i [0, 0, 0, 0]).getD c 0
  let sumAll := (List.range 3).map (fun c =>
    (List.range texelCount).foldl (fun acc i => acc + px i c) 0)
  let sumsqAll := (List.range 3).map (fun c =>
    (List.range texelCount).foldl (fun acc i => acc + px i c * px i c) 0)
  match astcRgbSseFromStats sumAll sumsqAll texelCount with
  | none => none
  | some baseErr =>
    if baseErr < 4096 then none
    else
      let limit := min 96 (32 + (texelCount >>> 1))
      let prefilter : List (Nat × Nat) :=
        if partitionCount != 2 || cacheCount ≤ limit then []
        else
          -- RGBA 2-means: farthest-point init, two Lloyd iterations.
          let farT := (List.range texelCount).foldl (fun (acc : Nat × Nat) t =>
            let d := (List.range 4).foldl (fun (a : Nat) c =>
              let v : Int := Int.ofNat (px t c) - Int.ofNat (px 0 c)
              a + (v * v).toNat) 0
            if d > acc.2 then (t, d) else acc) (0, 0)
          if farT.2 == 0 then []
          else
            let mean0 := (List.range 4).map (fun c => px 0 c)
            let mean1 := (List.range 4).map (fun c => px farT.1 c)
            let iterate (st : List Nat × List Nat × List Bool) (_ : Nat) :=
              let (m0, m1, _) := st
              let stepT (acc : List Nat × List Nat × Nat × Nat × List Bool) (t : Nat) :=
                let (s0, s1, c0, c1, assign) := acc
                let d0 := (List.range 4).foldl (fun (a : Nat) c =>
                  let v : Int := Int.ofNat (px t c) - Int.ofNat (m0.getD c 0)
                  a + (v * v).toNat) 0
                let d1 := (List.range 4).foldl (fun (a : Nat) c =>
                  let v : Int := Int.ofNat (px t c) - Int.ofNat (m1.getD c 0)
                  a + (v * v).toNat) 0
                let oneB : Bool := decide (d1 < d0)
                let s0 := if oneB then s0 else (List.range 4).map (fun c => s0.getD c 0 + px t c)
                let s1 := if oneB then (List.range 4).map (fun c => s1.getD c 0 + px t c) else s1
                (s0, s1, (if oneB then c0 else c0 + 1), (if oneB then c1 + 1 else c1),
                 assign ++ [oneB])
              let (s0, s1, c0, c1, assign) := (List.range texelCount).foldl stepT
                ((List.range 4).map (fun _ => 0), (List.range 4).map (fun _ => 0),
                 0, 0, ([] : List Bool))
              if c0 == 0 || c1 == 0 then (m0, m1, assign)
              else
                (((List.range 4).map (fun c => (s0.getD c 0 + c0 / 2) / c0)),
                 ((List.range 4).map (fun c => (s1.getD c 0 + c1 / 2) / c1)),
                 assign)
            let (_, _, assign) := (List.range 2).foldl iterate (mean0, mean1, [])
            let n1 := assign.foldl (fun acc b => if b then acc + 1 else acc) 0
            if n1 == 0 || n1 == texelCount then []
            else
              let words := (texelCount + 63) / 64
              let mkBits (use : Nat → Bool) : List Nat :=
                (List.range 3).map (fun w =>
                  (List.range 64).foldl (fun acc b =>
                    if w * 64 + b < texelCount && use (w * 64 + b) then acc + (1 <<< b)
                    else acc) 0)
              let bbits := mkBits (fun t => assign.getD t false)
              let mask := mkBits (fun _ => true)
              let ins := (List.range cacheCount).foldl (fun (sl : List (Nat × Nat)) i =>
                let part := (cache.getD i (0, [], [], [])).2.1
                let seedBits := ((List.range 3).map (fun w =>
                  (List.range 64).foldl (fun acc b =>
                    if w * 64 + b < texelCount && part.getD (w * 64 + b) 0 != 0
                    then acc + (1 <<< b) else acc) 0))
                astcShortlistInsert sl limit (astcBitmapMismatch bbits seedBits mask words) i) []
              ins
      let shortlist := prefilter
      let total := if shortlist.length > 0 then shortlist.length else cacheCount
      let best := (List.range ((total + 3) / 4)).foldl (fun (acc : Option (Nat × Nat)) bi =>
        let start := bi * 4
        let batchN := min 4 (total - start)
        let idxs := (List.range batchN).map (fun s =>
          if shortlist.length > 0 then (shortlist.getD (start + s) (0, 0)).2
          else start + s)
        let sums := (List.range batchN).map (fun s =>
          (List.range partitionCount).map (fun p =>
            (List.range 3).map (fun c =>
              (List.range texelCount).foldl (fun a t =>
                let part := ((cache.getD (idxs.getD s 0) (0, [], [], [])).2.1).getD t 0
                if part == p then a + px t c else a) 0)))
        let sumsqs := (List.range batchN).map (fun s =>
          (List.range partitionCount).map (fun p =>
            (List.range 3).map (fun c =>
              (List.range texelCount).foldl (fun a t =>
                let part := ((cache.getD (idxs.getD s 0) (0, [], [], [])).2.1).getD t 0
                if part == p then a + px t c * px t c else a) 0)))
        (List.range batchN).foldl (fun (acc2 : Option (Nat × Nat)) s =>
          let idx := idxs.getD s 0
          let counts := ((cache.getD idx (0, [], [], [])).2.2.1)
          -- The C accumulates in uint64: an empty partition contributes
          -- UINT64_MAX and the sum wraps modulo 2^64.
          let err := ((List.range partitionCount).foldl (fun a p =>
            a + (match astcRgbSseFromStats ((sums.getD s []).getD p [])
                    ((sumsqs.getD s []).getD p []) (counts.getD p 0) with
                  | some v => v
                  | none => 0xFFFFFFFFFFFFFFFF)) 0) % 0x10000000000000000
          match acc2 with
          | none => some (idx, err)
          | some (_, e) => if err < e then some (idx, err) else acc2) acc) none
      match best with
      | none => none
      | some (idx, err) => some (idx, err * 4 < baseErr * 3)

end Texcomp
