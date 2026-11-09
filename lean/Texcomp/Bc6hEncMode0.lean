/-
  TinyEXR - Lean 4 formalization of the BC6H mode-0 block encoder.

  Ports `tc_bc6h_mode0_uf16` in `tools/texcomp/src/texcomp_bc6h.c`: the
  32-entry two-region partition table, the TOPK-5 partition prefilter on
  the quantised endpoints, the 5-bit delta-fit check, palette selector
  choice, the two least-squares refinement rounds (with `rdiv`), the
  anchor fix-up, and the mode-0 bit layout. Built on the shared
  arithmetic core in `Texcomp.Bc6hKernels`.

  The other BC6H modes and the multi-mode winner selection are the
  remaining boundary.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hKernels

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc6h_part2`: the 32 two-region partitions (16 texels each). -/
def bc6hEncPart2 : List (List Nat) :=
  [[0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
   [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1],
   [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1],
   [0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1],
   [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
   [0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1],
   [0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1],
   [0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0],
   [0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
   [0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1],
   [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
   [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0],
   [0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0],
   [0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
   [0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0],
   [0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0]]

/-- `tc_bc6h_part2_anchor`: the region-1 anchor texel per partition. -/
def bc6hEncPart2Anchor : List Nat :=
  [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 2, 8, 2, 2, 8, 8, 15, 2, 8, 2, 2, 8, 8, 2, 2]

/-- Region bounds (min/max of the quantised endpoints) for a partition,
  with the maximum quantised value `maxv` as the "no texel yet" sentinel. -/
def bc6hEncRegionBoundsM (maxv : Nat) (q : List (List Nat)) (part : List Nat) :
    List (List Nat) × List (List Nat) × Bool × Bool :=
  let initLo : List (List Nat) := [[maxv, maxv, maxv], [maxv, maxv, maxv]]
  let initHi : List (List Nat) := [[0, 0, 0], [0, 0, 0]]
  (List.range 16).foldl (fun (acc : List (List Nat) × List (List Nat) × Bool × Bool) i =>
    let reg := part.getD i 0
    let (lo, hi, h0, h1) := acc
    let row := q.getD i [0, 0, 0]
    let lo := (List.range 2).map (fun r =>
      if r != reg then lo.getD r [maxv, maxv, maxv]
      else (List.range 3).map (fun c =>
        Nat.min ((lo.getD r [maxv, maxv, maxv]).getD c maxv) (row.getD c 0)))
    let hi := (List.range 2).map (fun r =>
      if r != reg then hi.getD r [0, 0, 0]
      else (List.range 3).map (fun c =>
        Nat.max ((hi.getD r [0, 0, 0]).getD c 0) (row.getD c 0)))
    (lo, hi, h0 || reg == 0, h1 || reg == 1)) (initLo, initHi, false, false)

/-- The 10-bit-sentinel specialisation used by modes 0 and 1. -/
def bc6hEncRegionBounds (q : List (List Nat)) (part : List Nat) :
    List (List Nat) × List (List Nat) × Bool × Bool :=
  bc6hEncRegionBoundsM 1023 q part

/-- The partition prefilter score: sum of squared endpoint ranges. -/
def bc6hEncPartScore (lo hi : List (List Nat)) : Nat :=
  (List.range 3).foldl (fun (acc : Nat) c =>
    let e0 := (hi.getD 0 [0, 0, 0]).getD c 0 - (lo.getD 0 [1023, 1023, 1023]).getD c 0
    let e1 := (hi.getD 1 [0, 0, 0]).getD c 0 - (lo.getD 1 [1023, 1023, 1023]).getD c 0
    acc + e0 * e0 + e1 * e1) 0

/-- `tc_bc6h_mode0_selectors`: nearest partition palette entry per texel. -/
def bc6hEncMode0Selectors (target : List (List Nat)) (part : List Nat)
    (ep : List (List Nat)) : List Nat × Nat :=
  let w3 := bc7Weights3
  let pal : List (List (List Nat)) := (List.range 2).map (fun r =>
    (List.range 8).map (fun s =>
      (List.range 3).map (fun c =>
        bc6hUnquantUf16ToMag
          ((((64 - w3.getD s 0) * (ep.getD (r * 2) [0, 0, 0]).getD c 0 +
             w3.getD s 0 * (ep.getD (r * 2 + 1) [0, 0, 0]).getD c 0 + 32) >>> 6)))))
  (List.range 16).foldl (fun (acc : List Nat × Nat) i =>
    let reg := part.getD i 0
    let t := target.getD i [0, 0, 0]
    let best := (List.range 8).foldl (fun (bacc : Nat × Nat) s =>
      let p := (pal.getD reg []).getD s [0, 0, 0]
      let e := bc6hErr3Mag t (p.getD 0 0) (p.getD 1 0) (p.getD 2 0)
      if e < bacc.2 then (s, e) else bacc) (0, 0xFFFFFFFF)
    (acc.1 ++ [best.1], acc.2 + best.2)) ([], 0)

/-- The 5-slot TOPK partition prefilter (`TOPK = 5`), slot order preserved
  (C replaces the leftmost worst slot in place). -/
def bc6hEncMode0Prefilter (q : List (List Nat)) : List (Nat × Nat) :=
  let slots := (List.range 32).foldl (fun (slots : List (Option (Nat × Nat))) p =>
    let part := bc6hEncPart2.getD p []
    let (lo, hi, h0, h1) := bc6hEncRegionBounds q part
    if !h0 || !h1 then slots
    else
      let score := bc6hEncPartScore lo hi
      if slots.any (fun s => s.isNone) then
        let idx := (slots.findIdx? (fun s => s.isNone)).getD 0
        slots.set idx (some (p, score))
      else
        let worst := (List.range 5).foldl (fun (w : Nat) k =>
          let cw := ((slots.getD w none).map (fun (x : Nat × Nat) => x.2)).getD 0
          let ck := ((slots.getD k none).map (fun (x : Nat × Nat) => x.2)).getD 0
          if ck > cw then k else w) 0
        let cworst := ((slots.getD worst none).map (fun (x : Nat × Nat) => x.2)).getD 0
        if score < cworst then slots.set worst (some (p, score)) else slots)
    ([none, none, none, none, none] : List (Option (Nat × Nat)))
  slots.filterMap id

/-- `tc_bc6h_pack_delta5`. -/
def bc6hEncPackDelta5 (d : Int) : Nat :=
  let d := if d < -16 then -16 else if d > 15 then 15 else d
  (Int32.ofInt d).toUInt32.toNat &&& 31

/-- `tc_bc6h_mode0_uf16`: encode one block as BC6H mode 0. Returns
  `(bytes, sse)` or `none` when no partition fits (C's `UINT64_MAX`). -/
def bc6hEncMode0Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantUf16 ((pix.getD i []).getD c 0)))
  let target := q.map (fun row => row.map bc6hUnquantUf16ToMag)
  let fits := fun (x : Int) => -16 ≤ x && x ≤ 15
  let evalCand (p : Nat) : Option (List (List Nat) × List Nat × Nat) :=
    let part := bc6hEncPart2.getD p []
    let (lo, hi, _, _) := bc6hEncRegionBounds q part
    let lo0 := lo.getD 0 [1023, 1023, 1023]
    let hi0 := hi.getD 0 [0, 0, 0]
    let lo1 := lo.getD 1 [1023, 1023, 1023]
    let hi1 := hi.getD 1 [0, 0, 0]
    let d1 := (List.range 3).map (fun c =>
      Int.ofNat (hi0.getD c 0) - Int.ofNat (lo0.getD c 0))
    let d2 := (List.range 3).map (fun c =>
      Int.ofNat (lo1.getD c 0) - Int.ofNat (lo0.getD c 0))
    let d3 := (List.range 3).map (fun c =>
      Int.ofNat (hi1.getD c 0) - Int.ofNat (lo0.getD c 0))
    if !((d1 ++ d2 ++ d3).all fits) then none
    else
      let ep : List (List Nat) := [lo0, hi0, lo1, hi1]
      let (sel, err) := bc6hEncMode0Selectors target part ep
      some (ep, sel, err)
  let bestInit : Option (Nat × List (List Nat) × List Nat × Nat) := none
  let best := (bc6hEncMode0Prefilter q).foldl
    (fun (acc : Option (Nat × List (List Nat) × List Nat × Nat)) (p, _) =>
      match evalCand p with
      | none => acc
      | some (ep, sel, err) =>
        match acc with
        | none => some (p, ep, sel, err)
        | some (_, _, _, e0) => if err < e0 then some (p, ep, sel, err) else acc)
    bestInit
  match best with
  | none => none
  | some (bestP, ep0, sel0, err0) =>
    let refineRound (st : List (List Nat) × List Nat × Nat) :
        Option (List (List Nat) × List Nat × Nat) :=
      let (bep, bsel, berr) := st
      let sumsFor (rr c : Nat) : Int × Int × Int × Int × Int :=
        (List.range 16).foldl (fun (acc : Int × Int × Int × Int × Int) i =>
          if (bc6hEncPart2.getD bestP []).getD i 0 != rr then acc
          else
            let bb : Int := Int.ofNat (bc7Weights3.getD (bsel.getD i 0) 0)
            let a : Int := 64 - bb
            let pp : Int := Int.ofNat ((q.getD i [0, 0, 0]).getD c 0)
            (acc.1 + a * a, acc.2.1 + a * bb, acc.2.2.1 + bb * bb,
             acc.2.2.2.1 + a * pp, acc.2.2.2.2 + bb * pp))
          (0, 0, 0, 0, 0)
      let cl := fun (x : Int) => if x < 0 then 0 else if x > 1023 then 1023 else x.toNat
      let nep : List (List Nat) := (List.range 4).map (fun row =>
        let rr := row / 2
        (List.range 3).map (fun c =>
          let (saa, sab, sbb, sap, sbp) := sumsFor rr c
          let det := saa * sbb - sab * sab
          if det ≤ 0 then (bep.getD row [0, 0, 0]).getD c 0
          else if row % 2 == 0 then cl (bc6hRdiv ((sap * sbb - sbp * sab) * 64) det)
          else cl (bc6hRdiv ((sbp * saa - sap * sab) * 64) det)))
      let d1 := (List.range 3).map (fun c =>
        Int.ofNat ((nep.getD 1 [0, 0, 0]).getD c 0) - Int.ofNat ((nep.getD 0 [0, 0, 0]).getD c 0))
      let d2 := (List.range 3).map (fun c =>
        Int.ofNat ((nep.getD 2 [0, 0, 0]).getD c 0) - Int.ofNat ((nep.getD 0 [0, 0, 0]).getD c 0))
      let d3 := (List.range 3).map (fun c =>
        Int.ofNat ((nep.getD 3 [0, 0, 0]).getD c 0) - Int.ofNat ((nep.getD 0 [0, 0, 0]).getD c 0))
      if !((d1 ++ d2 ++ d3).all fits) then none
      else
        let (nsel, ne) := bc6hEncMode0Selectors target (bc6hEncPart2.getD bestP []) nep
        if ne < berr then some (nep, nsel, ne) else none
    let refined := (List.range 2).foldl (fun (acc : List (List Nat) × List Nat × Nat) _ =>
      match refineRound acc with
      | some next => next
      | none => acc) (ep0, sel0, err0)
    let (bep0, bsel0, berr) := refined
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (bep, bsel) := (List.range 2).foldl (fun (st : List (List Nat) × List Nat) r =>
      let (ep, sel) := st
      let atIx := if r == 0 then 0 else anchor
      if (sel.getD atIx 0) &&& 4 != 0 then
        let ep := (List.range 4).map (fun k =>
          if k == r * 2 then ep.getD (r * 2 + 1) [0, 0, 0]
          else if k == r * 2 + 1 then ep.getD (r * 2) [0, 0, 0]
          else ep.getD k [0, 0, 0])
        let sel := (List.range 16).map (fun i =>
          if (bc6hEncPart2.getD bestP []).getD i 0 == r then 7 - (sel.getD i 0)
          else sel.getD i 0)
        (ep, sel)
      else (ep, sel)) (bep0, bsel0)
    let step := fun (acc : Nat × Nat) (v n : Nat) =>
      (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let (acc1, p1) := step (0, 2) ((epAt 2 1) >>> 4 &&& 1) 1
    let (acc2, p2) := step (acc1, p1) ((epAt 2 2) >>> 4 &&& 1) 1
    let (acc3, p3) := step (acc2, p2) ((epAt 3 2) >>> 4 &&& 1) 1
    let (acc4, p4) := step (acc3, p3) (epAt 0 0) 10
    let (acc5, p5) := step (acc4, p4) (epAt 0 1) 10
    let (acc6, p6) := step (acc5, p5) (epAt 0 2) 10
    let (acc7, p7) := step (acc6, p6)
      (bc6hEncPackDelta5 (Int.ofNat (epAt 1 0) - Int.ofNat (epAt 0 0))) 5
    let (acc8, p8) := step (acc7, p7) ((epAt 3 1) >>> 4 &&& 1) 1
    let (acc9, p9) := step (acc8, p8) ((epAt 2 1) &&& 0xF) 4
    let (acc10, p10) := step (acc9, p9)
      (bc6hEncPackDelta5 (Int.ofNat (epAt 1 1) - Int.ofNat (epAt 0 1))) 5
    let (acc11, p11) := step (acc10, p10) ((epAt 3 2) &&& 1) 1
    let (acc12, p12) := step (acc11, p11) ((epAt 3 1) &&& 0xF) 4
    let (acc13, p13) := step (acc12, p12)
      (bc6hEncPackDelta5 (Int.ofNat (epAt 1 2) - Int.ofNat (epAt 0 2))) 5
    let (acc14, p14) := step (acc13, p13) ((epAt 3 2) >>> 1 &&& 1) 1
    let (acc15, p15) := step (acc14, p14) ((epAt 2 2) &&& 0xF) 4
    let (acc16, p16) := step (acc15, p15)
      (bc6hEncPackDelta5 (Int.ofNat (epAt 2 0) - Int.ofNat (epAt 0 0))) 5
    let (acc17, p17) := step (acc16, p16) ((epAt 3 2) >>> 2 &&& 1) 1
    let (acc18, p18) := step (acc17, p17)
      (bc6hEncPackDelta5 (Int.ofNat (epAt 3 0) - Int.ofNat (epAt 0 0))) 5
    let (acc19, p19) := step (acc18, p18) ((epAt 3 2) >>> 3 &&& 1) 1
    let (acc20, p20) := step (acc19, p19) bestP 5
    let (accF, _) := (List.range 16).foldl (fun (st : Nat × Nat) i =>
      let nb := if i == 0 || i == anchor then 2 else 3
      step st (bsel.getD i 0) nb) (acc20, p20)
    some ((List.range 16).map (fun i => (accF >>> (8 * i)) &&& 0xFF), berr)

end Texcomp
