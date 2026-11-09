/-
  TinyEXR - Lean 4 formalization of the BC6H mode-9 encoder.

  Ports `tc_bc6h_mode9_uf16` in `tools/texcomp/src/texcomp_bc6h.c`: a
  two-region mode with all four endpoints stored explicitly at 6 bits,
  so no delta-fit test exists and the partition search always yields a
  candidate. Selectors use the 6-bit `unquant_n_to_mag` palette
  (`tc_bc6h_mode9_selectors`), not the 10-bit one modes 0/1 use.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode234

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc6h_mode9_selectors`: nearest of 8 palette entries per texel, with
  the 6-bit `unquant_n_to_mag` reconstruction. Returns `(selectors, err)`. -/
def bc6hEncMode9Selectors (target : List (List Nat)) (part : List Nat)
    (ep : List (List Nat)) : List Nat × Nat :=
  let w3 := bc7Weights3
  let pal : List (List (List Nat)) := (List.range 2).map (fun r =>
    (List.range 8).map (fun s =>
      (List.range 3).map (fun c =>
        bc6hUnquantNToMag
          ((((64 - w3.getD s 0) * (ep.getD (r * 2) [0, 0, 0]).getD c 0 +
             w3.getD s 0 * (ep.getD (r * 2 + 1) [0, 0, 0]).getD c 0 + 32) >>> 6)) 6)))
  (List.range 16).foldl (fun (acc : List Nat × Nat) i =>
    let reg := part.getD i 0
    let t := target.getD i [0, 0, 0]
    let best := (List.range 8).foldl (fun (bacc : Nat × Nat) s =>
      let p := (pal.getD reg []).getD s [0, 0, 0]
      let e := bc6hErr3Mag t (p.getD 0 0) (p.getD 1 0) (p.getD 2 0)
      if e < bacc.2 then (s, e) else bacc) (0, 0xFFFFFFFF)
    (acc.1 ++ [best.1], acc.2 + best.2)) ([], 0)

/-- TOPK-pre-filtered two-region search, refinement and anchor fix-up for
  mode 9. Returns `(partition, endpoints, selectors, err)`. -/
def bc6hEncMode9Search (pix : List (List UInt32)) :
    Option (Nat × List (List Nat) × List Nat × Nat) :=
  let maxv := 63
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantUf16N ((pix.getD i []).getD c 0) 6))
  let target := (List.range 16).map (fun i =>
    (List.range 3).map (fun c =>
      bc6hUnquantUf16ToMag (bc6hQuantUf16 ((pix.getD i []).getD c 0))))
  let bounds (p : Nat) := bc6hEncRegionBoundsM maxv q (bc6hEncPart2.getD p [])
  let slots := (List.range 32).foldl (fun (slots : List (Option (Nat × Nat))) p =>
    let (lo, hi, h0, h1) := bounds p
    if !h0 || !h1 then slots
    else
      let score := (List.range 3).foldl (fun (acc : Nat) c =>
        let e0 := (hi.getD 0 [0, 0, 0]).getD c 0 - (lo.getD 0 [maxv, maxv, maxv]).getD c 0
        let e1 := (hi.getD 1 [0, 0, 0]).getD c 0 - (lo.getD 1 [maxv, maxv, maxv]).getD c 0
        acc + e0 * e0 + e1 * e1) 0
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
  let cands : List (Nat × Nat) := slots.filterMap id
  let best := cands.foldl
    (fun (acc : Option (Nat × List (List Nat) × List Nat × Nat)) (p, _) =>
      let (lo, hi, _, _) := bounds p
      let ep : List (List Nat) := [lo.getD 0 [maxv, maxv, maxv], hi.getD 0 [0, 0, 0],
                                   lo.getD 1 [maxv, maxv, maxv], hi.getD 1 [0, 0, 0]]
      let (sel, err) := bc6hEncMode9Selectors target (bc6hEncPart2.getD p []) ep
      match acc with
      | none => some (p, ep, sel, err)
      | some (_, _, _, e0) => if err < e0 then some (p, ep, sel, err) else acc)
    none
  match best with
  | none => none
  | some (bestP, ep0, sel0, err0) =>
    let refineRound (st : List (List Nat) × List Nat × Nat) :
        Option (List (List Nat) × List Nat × Nat) :=
      let (bep, bsel, berr) := st
      let cl : Int → Nat := fun (x : Int) =>
        if x < 0 then 0 else if x > Int.ofNat maxv then maxv else x.toNat
      let nep : List (List Nat) := (List.range 4).map (fun row =>
        let rr := row / 2
        (List.range 3).map (fun c =>
          let (saa, sab, sbb, sap, sbp) :=
            (List.range 16).foldl (fun (acc : Int × Int × Int × Int × Int) i =>
              if (bc6hEncPart2.getD bestP []).getD i 0 != rr then acc
              else
                let bb : Int := Int.ofNat (bc7Weights3.getD (bsel.getD i 0) 0)
                let a : Int := 64 - bb
                let pp : Int := Int.ofNat ((q.getD i [0, 0, 0]).getD c 0)
                (acc.1 + a * a, acc.2.1 + a * bb, acc.2.2.1 + bb * bb,
                 acc.2.2.2.1 + a * pp, acc.2.2.2.2 + bb * pp)) (0, 0, 0, 0, 0)
          let det := saa * sbb - sab * sab
          if det ≤ 0 then (bep.getD row [0, 0, 0]).getD c 0
          else if row % 2 == 0 then cl (bc6hRdiv ((sap * sbb - sbp * sab) * 64) det)
          else cl (bc6hRdiv ((sbp * saa - sap * sab) * 64) det)))
      let (nsel, ne) := bc6hEncMode9Selectors target (bc6hEncPart2.getD bestP []) nep
      if ne < berr then some (nep, nsel, ne) else none
    let refined := (List.range 2).foldl (fun (acc : List (List Nat) × List Nat × Nat) _ =>
      match refineRound acc with
      | some next => next
      | none => acc) (ep0, sel0, err0)
    let (bep0, bsel0, berr) := refined
    let (bep, bsel) := bc6hEncAnchorFix bestP (bc6hEncPart2Anchor.getD bestP 15) bep0 bsel0
    some (bestP, bep, bsel, berr)

/-- `tc_bc6h_mode9_uf16`: two regions, four explicit 6-bit endpoints. -/
def bc6hEncMode9Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncMode9Search pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 30 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0) 6
    let (a3, p3) := bc6hEncPut (a2, p2) ((epAt 3 1) >>> 4 &&& 1) 1
    let (a4, p4) := bc6hEncPut (a3, p3) ((epAt 3 2) &&& 1) 1
    let (a5, p5) := bc6hEncPut (a4, p4) ((epAt 3 2) >>> 1 &&& 1) 1
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 2 2) >>> 4 &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (epAt 0 1) 6
    let (a8, p8) := bc6hEncPut (a7, p7) ((epAt 2 1) >>> 5 &&& 1) 1
    let (a9, p9) := bc6hEncPut (a8, p8) ((epAt 2 2) >>> 5 &&& 1) 1
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 3 2) >>> 2 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) ((epAt 2 1) >>> 4 &&& 1) 1
    let (a12, p12) := bc6hEncPut (a11, p11) (epAt 0 2) 6
    let (a13, p13) := bc6hEncPut (a12, p12) ((epAt 3 1) >>> 5 &&& 1) 1
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 3 2) >>> 3 &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) ((epAt 3 2) >>> 5 &&& 1) 1
    let (a16, p16) := bc6hEncPut (a15, p15) ((epAt 3 2) >>> 4 &&& 1) 1
    let (a17, p17) := bc6hEncPut (a16, p16) (epAt 1 0) 6
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 2 1) &&& 0xF) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (epAt 1 1) 6
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 3 1) &&& 0xF) 4
    let (a21, p21) := bc6hEncPut (a20, p20) (epAt 1 2) 6
    let (a22, p22) := bc6hEncPut (a21, p21) ((epAt 2 2) &&& 0xF) 4
    let (a23, p23) := bc6hEncPut (a22, p22) (epAt 2 0) 6
    let (a24, p24) := bc6hEncPut (a23, p23) (epAt 3 0) 6
    let bits := bc6hEncTail (a24, p24) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

end Texcomp
