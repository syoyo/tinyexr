/-
  TinyEXR - Lean 4 formalization of the BC6H two-region delta encoders
  (modes 2, 3, 4).

  Ports `tc_bc6h_mode234_uf16` in `tools/texcomp/src/texcomp_bc6h.c`: an
  11-bit primary endpoint per channel plus 4/5-bit signed deltas
  (mode 2 = R5G4B4, mode 3 = R4G5B4, mode 4 = R4G4B5), sharing the same
  TOPK-5 partition prefilter, delta-fit test, mode-0 selectors, two
  least-squares refinement rounds and anchor fix-up as mode 0.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode0

namespace Texcomp

set_option linter.unusedVariables false

/-- Anchor fix-up: if a region's anchor selector has its top bit set, swap
  that region's endpoints and invert its selectors (`7 - sel`). -/
def bc6hEncAnchorFix (part anchor : Nat) (bep0 : List (List Nat)) (bsel0 : List Nat) :
    List (List Nat) × List Nat :=
  let step (st : List (List Nat) × List Nat) (r : Nat) : List (List Nat) × List Nat :=
    let (ep, sel) := st
    let atIx := if r == 0 then 0 else anchor
    if (sel.getD atIx 0) &&& 4 != 0 then
      let ep' := (List.range 4).map (fun k =>
        if k == r * 2 then ep.getD (r * 2 + 1) [0, 0, 0]
        else if k == r * 2 + 1 then ep.getD (r * 2) [0, 0, 0]
        else ep.getD k [0, 0, 0])
      let sel' := (List.range 16).map (fun i =>
        if (bc6hEncPart2.getD part []).getD i 0 == r then 7 - (sel.getD i 0)
        else sel.getD i 0)
      (ep', sel')
    else (ep, sel)
  (List.range 2).foldl step (bep0, bsel0)

/-- Shared two-region search for the delta modes: 11-bit quantisation,
  per-channel delta limits from `dbits`, TOPK prefilter, refine, anchor
  fix-up. Returns `(partition, endpoints, selectors, error)`. -/
def bc6hEncDeltaSearch (maxv : Nat) (dbits : List Nat) (pix : List (List UInt32)) :
    Option (Nat × List (List Nat) × List Nat × Nat) :=
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantUf16N ((pix.getD i []).getD c 0) 11))
  -- The selector target is the *10-bit* reconstruction of the input (C uses
  -- `unquant_uf16_to_mag(quant_uf16(f))` here, not the 11-bit `q`).
  let target := (List.range 16).map (fun i =>
    (List.range 3).map (fun c =>
      bc6hUnquantUf16ToMag (bc6hQuantUf16 ((pix.getD i []).getD c 0))))
  let bounds (p : Nat) := bc6hEncRegionBoundsM maxv q (bc6hEncPart2.getD p [])
  let inRange (c : Nat) (d : Int) : Bool :=
    let lim : Int := Int.ofNat (1 <<< ((dbits.getD c 5) - 1))
    (-lim) ≤ d && d ≤ lim - 1
  let fitsAt (ep : List (List Nat)) : Bool :=
    (List.range 3).all (fun c =>
      let d1 := Int.ofNat ((ep.getD 1 [0, 0, 0]).getD c 0) - Int.ofNat ((ep.getD 0 [0, 0, 0]).getD c 0)
      let d2 := Int.ofNat ((ep.getD 2 [0, 0, 0]).getD c 0) - Int.ofNat ((ep.getD 0 [0, 0, 0]).getD c 0)
      let d3 := Int.ofNat ((ep.getD 3 [0, 0, 0]).getD c 0) - Int.ofNat ((ep.getD 0 [0, 0, 0]).getD c 0)
      inRange c d1 && inRange c d2 && inRange c d3)
  -- Prefilter: same TOPK-5 slot logic as mode 0.
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
  let evalCand (p : Nat) : Option (List (List Nat) × List Nat × Nat) :=
    let (lo, hi, _, _) := bounds p
    let ep : List (List Nat) := [lo.getD 0 [maxv, maxv, maxv], hi.getD 0 [0, 0, 0],
                                 lo.getD 1 [maxv, maxv, maxv], hi.getD 1 [0, 0, 0]]
    if !fitsAt ep then none
    else
      let (sel, err) := bc6hEncMode0Selectors target (bc6hEncPart2.getD p []) ep
      some (ep, sel, err)
  let bestInit : Option (Nat × List (List Nat) × List Nat × Nat) := none
  let cands : List (Nat × Nat) := slots.filterMap id
  let best := cands.foldl
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
      if !fitsAt nep then none
      else
        let (nsel, ne) := bc6hEncMode0Selectors target (bc6hEncPart2.getD bestP []) nep
        if ne < berr then some (nep, nsel, ne) else none
    let refined := (List.range 2).foldl (fun (acc : List (List Nat) × List Nat × Nat) _ =>
      match refineRound acc with
      | some next => next
      | none => acc) (ep0, sel0, err0)
    let (bep0, bsel0, berr) := refined
    let (bep, bsel) := bc6hEncAnchorFix bestP (bc6hEncPart2Anchor.getD bestP 15) bep0 bsel0
    some (bestP, bep, bsel, berr)

/-- Bit writer over a `Nat` accumulator (LSB-first, as `tc_bc6h_w`). -/
def bc6hEncPut (acc : Nat × Nat) (v n : Nat) : Nat × Nat :=
  (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)

/-- Emit the trailing partition + selector fields shared by all modes. -/
def bc6hEncTail (acc : Nat × Nat) (bestP anchor : Nat) (bsel : List Nat) : Nat :=
  let (a1, p1) := bc6hEncPut acc bestP 5
  (List.range 16).foldl (fun (st : Nat × Nat) i =>
    let nb := if i == 0 || i == anchor then 2 else 3
    bc6hEncPut st (bsel.getD i 0) nb) (a1, p1) |>.1

/-- `tc_bc6h_mode234_uf16` for mode 2 (R5G4B4 deltas). -/
def bc6hEncMode2Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 2047 [5, 4, 4] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x02 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0 &&& 1023) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (epAt 0 1 &&& 1023) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (epAt 0 2 &&& 1023) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 0 0 >>> 10) &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (epAt 2 1 &&& 0xF) 4
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hEncPackDelta5 (d 1 1)) 4
    let (a9, p9) := bc6hEncPut (a8, p8) ((epAt 0 1 >>> 10) &&& 1) 1
    let (a10, p10) := bc6hEncPut (a9, p9) (epAt 3 2 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (epAt 3 1 &&& 0xF) 4
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hEncPackDelta5 (d 1 2)) 4
    let (a13, p13) := bc6hEncPut (a12, p12) ((epAt 0 2 >>> 10) &&& 1) 1
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 3 2 >>> 1) &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (epAt 2 2 &&& 0xF) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a17, p17) := bc6hEncPut (a16, p16) ((epAt 3 2 >>> 2) &&& 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a19, p19) := bc6hEncPut (a18, p18) ((epAt 3 2 >>> 3) &&& 1) 1
    let bits := bc6hEncTail (a19, p19) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode234_uf16` for mode 3 (R4G5B4 deltas). -/
def bc6hEncMode3Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 2047 [4, 5, 4] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x06 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0 &&& 1023) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (epAt 0 1 &&& 1023) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (epAt 0 2 &&& 1023) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 4
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 0 0 >>> 10) &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 3 1 >>> 4) &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (epAt 2 1 &&& 0xF) 4
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 0 1 >>> 10) &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (epAt 3 1 &&& 0xF) 4
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hEncPackDelta5 (d 1 2)) 4
    let (a13, p13) := bc6hEncPut (a12, p12) ((epAt 0 2 >>> 10) &&& 1) 1
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 3 2 >>> 1) &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (epAt 2 2 &&& 0xF) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (epAt 3 2 &&& 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 3 2 >>> 2) &&& 1) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 4
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 2 1 >>> 4) &&& 1) 1
    let (a21, p21) := bc6hEncPut (a20, p20) ((epAt 3 2 >>> 3) &&& 1) 1
    let bits := bc6hEncTail (a21, p21) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode234_uf16` for mode 4 (R4G4B5 deltas). -/
def bc6hEncMode4Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 2047 [4, 4, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x0A 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0 &&& 1023) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (epAt 0 1 &&& 1023) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (epAt 0 2 &&& 1023) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 4
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 0 0 >>> 10) &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 2 2 >>> 4) &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (epAt 2 1 &&& 0xF) 4
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hEncPackDelta5 (d 1 1)) 4
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 0 1 >>> 10) &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (epAt 3 2 &&& 1) 1
    let (a12, p12) := bc6hEncPut (a11, p11) (epAt 3 1 &&& 0xF) 4
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 0 2 >>> 10) &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (epAt 2 2 &&& 0xF) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 4
    let (a17, p17) := bc6hEncPut (a16, p16) ((epAt 3 2 >>> 1) &&& 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 3 2 >>> 2) &&& 1) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 4
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 3 2 >>> 4) &&& 1) 1
    let (a21, p21) := bc6hEncPut (a20, p20) ((epAt 3 2 >>> 3) &&& 1) 1
    let bits := bc6hEncTail (a21, p21) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

end Texcomp
