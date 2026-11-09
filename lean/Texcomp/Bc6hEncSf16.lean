/-
  TinyEXR - Lean 4 formalization of the BC6H signed (`sf16`) encoders.

  Ports the `_sf16` block encoders in `tools/texcomp/src/texcomp_bc6h.c`
  (modes 0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13) on top of the shared
  two-region delta search. The C code stores endpoints as `int32_t` and
  reaches for their two's-complement bits with `(uint32_t)` casts, so the
  bit fields are extracted from the 32-bit two's-complement image here
  (`bc6hBits32`) rather than from the mathematical value.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode234

namespace Texcomp

set_option linter.unusedVariables false

/-! ## Two's-complement bit access -/

/-- The 32-bit two's-complement image of a signed value (`(uint32_t)v`). -/
def bc6hBits32 (x : Int) : Nat := (x.emod 0x100000000).toNat

/-- `(uint32_t)v & ((1 << n) - 1)`. -/
def bc6hLowBits (x : Int) (n : Nat) : Nat := bc6hBits32 x &&& ((1 <<< n) - 1)

/-- `((uint32_t)v >> n) & 1`. -/
def bc6hBitAt (x : Int) (n : Nat) : Nat := (bc6hBits32 x >>> n) &&& 1

/-! ## Signed selector kernels -/

/-- `tc_bc6h_pal16_sf16`: the 16 interpolated signed magnitudes. -/
def bc6hPal16Sf16 (lo hi : List Int) : List (List Int) :=
  (List.range 16).map (fun s =>
    let w := bc7Weights4.getD s 0
    (List.range 3).map (fun c =>
      bc6hUnquantSf16ToSmag
        (((Int.ofNat (64 - w)) * lo.getD c 0 + (Int.ofNat w) * hi.getD c 0 + 32) / 64)))

/-- `tc_bc6h_choose_selectors_sf16_scalar`: nearest of 16 palette entries. -/
def bc6hChooseSelectorsSf16 (target : List (List Int)) (lo hi : List Int) :
    List Nat × Nat :=
  let pal := bc6hPal16Sf16 lo hi
  (List.range 16).foldl (fun (acc : List Nat × Nat) i =>
    let t := target.getD i [0, 0, 0]
    let best := (List.range 16).foldl (fun (bacc : Nat × Nat) s =>
      let p := pal.getD s [0, 0, 0]
      let e := bc6hErr3Smag t (p.getD 0 0) (p.getD 1 0) (p.getD 2 0)
      if e < bacc.2 then (s, e) else bacc) (0, 0xFFFFFFFF)
    (acc.1 ++ [best.1], acc.2 + best.2)) ([], 0)

/-- `tc_bc6h_mode0_selectors_sf16`: 8-entry per-region palette with 3-bit
  weights and the 10-bit signed reconstruction. -/
def bc6hEncMode0SelectorsSf16 (target : List (List Int)) (part : List Nat)
    (ep : List (List Int)) : List Nat × Nat :=
  let w3 := bc7Weights3
  let pal : List (List (List Int)) := (List.range 2).map (fun r =>
    (List.range 8).map (fun s =>
      (List.range 3).map (fun c =>
        bc6hUnquantSf16ToSmag
          ((((Int.ofNat (64 - w3.getD s 0)) * (ep.getD (r * 2) [0, 0, 0]).getD c 0 +
             (Int.ofNat (w3.getD s 0)) * (ep.getD (r * 2 + 1) [0, 0, 0]).getD c 0 + 32) / 64)))))
  (List.range 16).foldl (fun (acc : List Nat × Nat) i =>
    let reg := part.getD i 0
    let t := target.getD i [0, 0, 0]
    let best := (List.range 8).foldl (fun (bacc : Nat × Nat) s =>
      let p := (pal.getD reg []).getD s [0, 0, 0]
      let e := bc6hErr3Smag t (p.getD 0 0) (p.getD 1 0) (p.getD 2 0)
      if e < bacc.2 then (s, e) else bacc) (0, 0xFFFFFFFF)
    (acc.1 ++ [best.1], acc.2 + best.2)) ([], 0)

/-! ## Signed region bounds, refinement, anchor fix-up -/

/-- Region min/max of the signed quantised endpoints. The "no texel yet"
  sentinels are `halfMax - 1` / `-halfMax`. -/
def bc6hEncRegionBoundsS (halfMax : Nat) (q : List (List Int)) (part : List Nat) :
    List (List Int) × List (List Int) × Bool × Bool :=
  let loS : Int := Int.ofNat halfMax - 1
  let hiS : Int := -(Int.ofNat halfMax)
  let initLo : List (List Int) := [[loS, loS, loS], [loS, loS, loS]]
  let initHi : List (List Int) := [[hiS, hiS, hiS], [hiS, hiS, hiS]]
  (List.range 16).foldl (fun (acc : List (List Int) × List (List Int) × Bool × Bool) i =>
    let reg := part.getD i 0
    let (lo, hi, h0, h1) := acc
    let row := q.getD i [0, 0, 0]
    let lo := (List.range 2).map (fun r =>
      if r != reg then lo.getD r [loS, loS, loS]
      else (List.range 3).map (fun c =>
        min ((lo.getD r [loS, loS, loS]).getD c loS) (row.getD c 0)))
    let hi := (List.range 2).map (fun r =>
      if r != reg then hi.getD r [hiS, hiS, hiS]
      else (List.range 3).map (fun c =>
        max ((hi.getD r [hiS, hiS, hiS]).getD c hiS) (row.getD c 0)))
    (lo, hi, h0 || reg == 0, h1 || reg == 1)) (initLo, initHi, false, false)

/-- `tc_bc6h_refine_sf16`: three least-squares rounds on one region pair.
  The C code clamps to ±511 regardless of the mode's own range, so the
  clamp is hard-coded here too. -/
def bc6hRefineSf16 (q target : List (List Int)) (lo hi : List Int) (sel0 : List Nat) :
    List Int × List Int × List Nat × Nat :=
  let best0 := bc6hChooseSelectorsSf16 target lo hi
  let round (st : List Int × List Int × List Nat × Nat) (_ : Nat) :=
    let (clo, chi, csel, cerr) := st
    let sums := (List.range 3).map (fun c =>
      (List.range 16).foldl (fun (acc : Int × Int × Int × Int × Int) i =>
        let b : Int := Int.ofNat (bc7Weights4.getD (csel.getD i 0) 0)
        let a : Int := 64 - b
        let p : Int := (q.getD i [0, 0, 0]).getD c 0
        (acc.1 + a * a, acc.2.1 + a * b, acc.2.2.1 + b * b,
         acc.2.2.2.1 + a * p, acc.2.2.2.2 + b * p)) (0, 0, 0, 0, 0))
    let cl : Int → Int := fun (x : Int) =>
      if x < -511 then -511 else if x > 511 then 511 else x
    let nep : List Int × List Int :=
      ((List.range 3).map (fun c =>
          let (saa, sab, sbb, sap, sbp) := sums.getD c (0, 0, 0, 0, 0)
          let det := saa * sbb - sab * sab
          if det ≤ 0 then clo.getD c 0
          else cl (bc6hRdiv ((sap * sbb - sbp * sab) * 64) det)),
       (List.range 3).map (fun c =>
          let (saa, sab, sbb, sap, sbp) := sums.getD c (0, 0, 0, 0, 0)
          let det := saa * sbb - sab * sab
          if det ≤ 0 then chi.getD c 0
          else cl (bc6hRdiv ((sbp * saa - sap * sab) * 64) det)))
    let (nlo, nhi) := nep
    let (nsel, ne) := bc6hChooseSelectorsSf16 target nlo nhi
    if ne < cerr then (nlo, nhi, nsel, ne) else (clo, chi, csel, cerr)
  let (lo', hi', sel', err') := (List.range 3).foldl round (lo, hi, best0.1, best0.2)
  (lo', hi', sel', err')

/-- Anchor fix-up for signed endpoints: swap the pair and invert selectors
  when the region anchor's top selector bit is set. -/
def bc6hEncAnchorFixS (part anchor : Nat) (bep0 : List (List Int)) (bsel0 : List Nat) :
    List (List Int) × List Nat :=
  let step (st : List (List Int) × List Nat) (r : Nat) : List (List Int) × List Nat :=
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

/-! ## Signed two-region delta search -/

/-- Shared signed search used by modes 0/1/2/3/4/5/6/7/8: `qbits`-bit signed
  quantisation, region bounds with the `halfMax` sentinels, TOPK partition
  prefilter, delta-fit test, two refinement rounds clamped to
  `[-halfMax, halfMax - 1]`, and the anchor fix-up. -/
def bc6hEncDeltaSearchS (qbits halfMax : Nat) (dbits : List Nat)
    (pix : List (List UInt32)) :
    Option (Nat × List (List Int) × List Nat × Nat) :=
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantSf16N ((pix.getD i []).getD c 0) qbits))
  let target := (List.range 16).map (fun i =>
    (List.range 3).map (fun c =>
      bc6hUnquantSf16ToSmag (bc6hQuantSf16 ((pix.getD i []).getD c 0))))
  let loS : Int := Int.ofNat halfMax - 1
  let hiS : Int := -(Int.ofNat halfMax)
  let bounds (p : Nat) := bc6hEncRegionBoundsS halfMax q (bc6hEncPart2.getD p [])
  let inRange (c : Nat) (d : Int) : Bool :=
    let lim : Int := Int.ofNat (1 <<< ((dbits.getD c 5) - 1))
    (-lim) ≤ d && d ≤ lim - 1
  let fitsAt (ep : List (List Int)) : Bool :=
    (List.range 3).all (fun c =>
      let d1 := (ep.getD 1 [0, 0, 0]).getD c 0 - (ep.getD 0 [0, 0, 0]).getD c 0
      let d2 := (ep.getD 2 [0, 0, 0]).getD c 0 - (ep.getD 0 [0, 0, 0]).getD c 0
      let d3 := (ep.getD 3 [0, 0, 0]).getD c 0 - (ep.getD 0 [0, 0, 0]).getD c 0
      inRange c d1 && inRange c d2 && inRange c d3)
  let slots := (List.range 32).foldl (fun (slots : List (Option (Nat × Int))) p =>
    let (lo, hi, h0, h1) := bounds p
    if !h0 || !h1 then slots
    else
      let score := (List.range 3).foldl (fun (acc : Int) c =>
        let e0 := (hi.getD 0 [0, 0, 0]).getD c 0 - (lo.getD 0 [loS, loS, loS]).getD c 0
        let e1 := (hi.getD 1 [0, 0, 0]).getD c 0 - (lo.getD 1 [loS, loS, loS]).getD c 0
        acc + e0 * e0 + e1 * e1) 0
      if slots.any (fun s => s.isNone) then
        let idx := (slots.findIdx? (fun s => s.isNone)).getD 0
        slots.set idx (some (p, score))
      else
        let worst := (List.range 5).foldl (fun (w : Nat) k =>
          let cw := ((slots.getD w none).map (fun (x : Nat × Int) => x.2)).getD 0
          let ck := ((slots.getD k none).map (fun (x : Nat × Int) => x.2)).getD 0
          if ck > cw then k else w) 0
        let cworst := ((slots.getD worst none).map (fun (x : Nat × Int) => x.2)).getD 0
        if score < cworst then slots.set worst (some (p, score)) else slots)
    ([none, none, none, none, none] : List (Option (Nat × Int)))
  let cands : List (Nat × Int) := slots.filterMap id
  let best := cands.foldl
    (fun (acc : Option (Nat × List (List Int) × List Nat × Nat)) (p, _) =>
      let (lo, hi, _, _) := bounds p
      let ep : List (List Int) := [lo.getD 0 [loS, loS, loS], hi.getD 0 [hiS, hiS, hiS],
                                   lo.getD 1 [loS, loS, loS], hi.getD 1 [hiS, hiS, hiS]]
      if !fitsAt ep then acc
      else
        let (sel, err) := bc6hEncMode0SelectorsSf16 target (bc6hEncPart2.getD p []) ep
        match acc with
        | none => some (p, ep, sel, err)
        | some (_, _, _, e0) => if err < e0 then some (p, ep, sel, err) else acc)
    none
  match best with
  | none => none
  | some (bestP, ep0, sel0, err0) =>
    let refineRound (st : List (List Int) × List Nat × Nat) :
        Option (List (List Int) × List Nat × Nat) :=
      let (bep, bsel, berr) := st
      let cl : Int → Int := fun (x : Int) =>
        if x < -Int.ofNat halfMax then -Int.ofNat halfMax
        else if x > Int.ofNat halfMax - 1 then Int.ofNat halfMax - 1 else x
      let nep : List (List Int) := (List.range 4).map (fun row =>
        let rr := row / 2
        (List.range 3).map (fun c =>
          let (saa, sab, sbb, sap, sbp) :=
            (List.range 16).foldl (fun (acc : Int × Int × Int × Int × Int) i =>
              if (bc6hEncPart2.getD bestP []).getD i 0 != rr then acc
              else
                let bb : Int := Int.ofNat (bc7Weights3.getD (bsel.getD i 0) 0)
                let a : Int := 64 - bb
                let pp : Int := (q.getD i [0, 0, 0]).getD c 0
                (acc.1 + a * a, acc.2.1 + a * bb, acc.2.2.1 + bb * bb,
                 acc.2.2.2.1 + a * pp, acc.2.2.2.2 + bb * pp)) (0, 0, 0, 0, 0)
          let det := saa * sbb - sab * sab
          if det ≤ 0 then (bep.getD row [0, 0, 0]).getD c 0
          else if row % 2 == 0 then cl (bc6hRdiv ((sap * sbb - sbp * sab) * 64) det)
          else cl (bc6hRdiv ((sbp * saa - sap * sab) * 64) det)))
      if !fitsAt nep then none
      else
        let (nsel, ne) := bc6hEncMode0SelectorsSf16 target (bc6hEncPart2.getD bestP []) nep
        if ne < berr then some (nep, nsel, ne) else none
    let refined := (List.range 2).foldl (fun (acc : List (List Int) × List Nat × Nat) _ =>
      match refineRound acc with
      | some next => next
      | none => acc) (ep0, sel0, err0)
    let (bep0, bsel0, berr) := refined
    let (bep, bsel) := bc6hEncAnchorFixS bestP (bc6hEncPart2Anchor.getD bestP 15) bep0 bsel0
    some (bestP, bep, bsel, berr)

/-! ## Signed one-region prelude (modes 12/13) -/

/-- Quantise, pick the better of the box and luma endpoint pairs, run the
  signed refinement, then the anchor swap. Returns `(q, target, lo, hi, sel)`. -/
def bc6hEncOneRegionS (qbits halfMax : Nat) (pix : List (List UInt32)) :
    List (List Int) × List (List Int) × List Int × List Int × List Nat :=
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantSf16N ((pix.getD i []).getD c 0) qbits))
  let target := (List.range 16).map (fun i =>
    (List.range 3).map (fun c =>
      bc6hUnquantSf16ToSmag (bc6hQuantSf16 ((pix.getD i []).getD c 0))))
  let loS : Int := Int.ofNat halfMax - 1
  let hiS : Int := -(Int.ofNat halfMax)
  let box := (List.range 16).foldl (fun (acc : List Int × List Int) i =>
    let row := q.getD i [0, 0, 0]
    ((List.range 3).map (fun c => min (acc.1.getD c loS) (row.getD c 0)),
     (List.range 3).map (fun c => max (acc.2.getD c hiS) (row.getD c 0))))
    ((List.range 3).map (fun _ => loS), (List.range 3).map (fun _ => hiS))
  -- Luma is the signed sum cast to uint32, compared unsigned.
  let luma := (List.range 16).foldl (fun (acc : Nat × Nat × Nat × Nat) i =>
    let t := target.getD i [0, 0, 0]
    let l := bc6hBits32 (t.getD 0 0 * 38 + t.getD 1 0 * 76 + t.getD 2 0 * 14)
    let (minL, maxL, minI, maxI) := acc
    let minI := if l < minL then i else minI
    let minL := if l < minL then l else minL
    let maxI := if l ≥ maxL then i else maxI
    let maxL := if l ≥ maxL then l else maxL
    (minL, maxL, minI, maxI)) (0xFFFFFFFF, 0, 0, 0)
  let lumaLo := q.getD luma.2.2.1 [0, 0, 0]
  let lumaHi := q.getD luma.2.2.2 [0, 0, 0]
  let lsel := bc6hChooseSelectorsSf16 target lumaLo lumaHi
  let bsel := bc6hChooseSelectorsSf16 target box.1 box.2
  let (lo0, hi0, sel0) : List Int × List Int × List Nat :=
    if lsel.2 < bsel.2 then (lumaLo, lumaHi, lsel.1) else (box.1, box.2, bsel.1)
  let (rlo, rhi, rsel, _) := bc6hRefineSf16 q target lo0 hi0 sel0
  if (rsel.getD 0 0) &&& 8 != 0 then
    ((List.range 3).map (fun c => rhi.getD c 0),
     (List.range 3).map (fun c => rlo.getD c 0),
     (List.range 16).map (fun i => 15 - rsel.getD i 0))
    |> fun (a, b, c) => (q, target, a, b, c)
  else (q, target, rlo, rhi, rsel)

/-! ## Two-region signed mode encoders -/

/-- `tc_bc6h_mode0_sf16`: 10-bit signed primary + 5-bit deltas. -/
def bc6hEncMode0Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 10 512 [5, 5, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0 2
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hBitAt (epAt 2 1) 4) 1
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hBitAt (epAt 2 2) 4) 1
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hBitAt (epAt 3 2) 4) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hPackSigned10 (epAt 0 0)) 10
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hPackSigned10 (epAt 0 1)) 10
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hPackSigned10 (epAt 0 2)) 10
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hBitAt (epAt 3 1) 4) 1
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hLowBits (epAt 2 1) 4) 4
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hLowBits (epAt 3 2) 1) 1
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hLowBits (epAt 3 1) 4) 4
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hBitAt (epAt 3 2) 1) 1
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hLowBits (epAt 2 2) 4) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hBitAt (epAt 3 2) 2) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hBitAt (epAt 3 2) 3) 1
    let bits := bc6hEncTail (a20, p20) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode1_sf16`: 7-bit signed primary + 6-bit deltas (clamped to
  5 bits by `pack_delta5`, as in the unsigned mode 1). -/
def bc6hEncMode1Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 7 64 [6, 6, 6] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 1 2
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hBitAt (epAt 2 1) 5) 1
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hBitAt (epAt 3 1) 4) 1
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hBitAt (epAt 3 1) 5) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hPackSignedN (epAt 0 0) 7) 7
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hLowBits (epAt 3 2) 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hBitAt (epAt 3 2) 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hBitAt (epAt 2 2) 4) 1
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hPackSignedN (epAt 0 1) 7) 7
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hBitAt (epAt 2 2) 5) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hBitAt (epAt 3 2) 2) 1
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hBitAt (epAt 2 1) 4) 1
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hPackSignedN (epAt 0 2) 7) 7
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hBitAt (epAt 3 2) 3) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hBitAt (epAt 3 2) 5) 1
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hBitAt (epAt 3 2) 4) 1
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hEncPackDelta5 (d 1 0)) 6
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hLowBits (epAt 2 1) 4) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 1 1)) 6
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hLowBits (epAt 3 1) 4) 4
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hEncPackDelta5 (d 1 2)) 6
    let (a22, p22) := bc6hEncPut (a21, p21) (bc6hLowBits (epAt 2 2) 4) 4
    let (a23, p23) := bc6hEncPut (a22, p22) (bc6hEncPackDelta5 (d 2 0)) 6
    let (a24, p24) := bc6hEncPut (a23, p23) (bc6hEncPackDelta5 (d 3 0)) 6
    let bits := bc6hEncTail (a24, p24) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode234_sf16` for mode 2 (R5G4B4). -/
def bc6hEncMode2Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 11 1024 [5, 4, 4] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x02 5
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hLowBits (epAt 0 0) 10) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hLowBits (epAt 0 1) 10) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hLowBits (epAt 0 2) 10) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hBitAt (epAt 0 0) 10) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hLowBits (epAt 2 1) 4) 4
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hEncPackDelta5 (d 1 1)) 4
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hBitAt (epAt 0 1) 10) 1
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hLowBits (epAt 3 2) 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hLowBits (epAt 3 1) 4) 4
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hEncPackDelta5 (d 1 2)) 4
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hBitAt (epAt 0 2) 10) 1
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hBitAt (epAt 3 2) 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hLowBits (epAt 2 2) 4) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hBitAt (epAt 3 2) 2) 1
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hBitAt (epAt 3 2) 3) 1
    let bits := bc6hEncTail (a19, p19) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode234_sf16` for mode 3 (R4G5B4). -/
def bc6hEncMode3Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 11 1024 [4, 5, 4] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x06 5
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hLowBits (epAt 0 0) 10) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hLowBits (epAt 0 1) 10) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hLowBits (epAt 0 2) 10) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 4
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hBitAt (epAt 0 0) 10) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hBitAt (epAt 3 1) 4) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hLowBits (epAt 2 1) 4) 4
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hBitAt (epAt 0 1) 10) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hLowBits (epAt 3 1) 4) 4
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hEncPackDelta5 (d 1 2)) 4
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hBitAt (epAt 0 2) 10) 1
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hBitAt (epAt 3 2) 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hLowBits (epAt 2 2) 4) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hLowBits (epAt 3 2) 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hBitAt (epAt 3 2) 2) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 4
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hBitAt (epAt 2 1) 4) 1
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hBitAt (epAt 3 2) 3) 1
    let bits := bc6hEncTail (a21, p21) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode234_sf16` for mode 4 (R4G4B5). -/
def bc6hEncMode4Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 11 1024 [4, 4, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x0A 5
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hLowBits (epAt 0 0) 10) 10
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hLowBits (epAt 0 1) 10) 10
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hLowBits (epAt 0 2) 10) 10
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) 4
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hBitAt (epAt 0 0) 10) 1
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hBitAt (epAt 2 2) 4) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hLowBits (epAt 2 1) 4) 4
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hEncPackDelta5 (d 1 1)) 4
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hBitAt (epAt 0 1) 10) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hLowBits (epAt 3 2) 1) 1
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hLowBits (epAt 3 1) 4) 4
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hBitAt (epAt 0 2) 10) 1
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hLowBits (epAt 2 2) 4) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 2 0)) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hBitAt (epAt 3 2) 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hBitAt (epAt 3 2) 2) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 4
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hBitAt (epAt 3 2) 4) 1
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hBitAt (epAt 3 2) 3) 1
    let bits := bc6hEncTail (a21, p21) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode5_sf16`: 9-bit signed primary + 5-bit deltas. -/
def bc6hEncMode5Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS 9 256 [5, 5, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x0E 5
    let (a2, p2) := bc6hEncPut (a1, p1) (bc6hPackSignedN (epAt 0 0) 9) 9
    let (a3, p3) := bc6hEncPut (a2, p2) (bc6hBitAt (epAt 2 2) 4) 1
    let (a4, p4) := bc6hEncPut (a3, p3) (bc6hPackSignedN (epAt 0 1) 9) 9
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hBitAt (epAt 2 1) 4) 1
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hPackSignedN (epAt 0 2) 9) 9
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hBitAt (epAt 3 2) 4) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a9, p9) := bc6hEncPut (a8, p8) (bc6hBitAt (epAt 3 1) 4) 1
    let (a10, p10) := bc6hEncPut (a9, p9) (bc6hLowBits (epAt 2 1) 4) 4
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a12, p12) := bc6hEncPut (a11, p11) (bc6hLowBits (epAt 3 2) 1) 1
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hLowBits (epAt 3 1) 4) 4
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a15, p15) := bc6hEncPut (a14, p14) (bc6hBitAt (epAt 3 2) 1) 1
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hLowBits (epAt 2 2) 4) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a18, p18) := bc6hEncPut (a17, p17) (bc6hBitAt (epAt 3 2) 2) 1
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hBitAt (epAt 3 2) 3) 1
    let bits := bc6hEncTail (a20, p20) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode678_sf16` shared packing: two hi bits + 8-bit primary per
  channel, then only the three endpoint-1 deltas (the C layout, which drops
  endpoints 2/3 from the bitstream). -/
def bc6hEncMode678Sf16 (qbits : Nat) (dbits : List Nat) (modeCode : Nat)
    (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearchS qbits 128 dbits pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Int := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => epAt r c - epAt 0 c
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let ch := fun (c : Nat) (acc : Nat × Nat) =>
      let x := epAt 0 c
      let hi := (bc6hBits32 x >>> 8) &&& 3
      let lo := bc6hLowBits x 8
      let (a, p) := bc6hEncPut acc (hi >>> 1 &&& 1) 1
      let (a, p) := bc6hEncPut (a, p) (hi &&& 1) 1
      bc6hEncPut (a, p) lo 8
    let (a1, p1) := bc6hEncPut (0, 0) modeCode 5
    let (a2, p2) := ch 0 (a1, p1)
    let (a3, p3) := ch 1 (a2, p2)
    let (a4, p4) := ch 2 (a3, p3)
    let (a5, p5) := bc6hEncPut (a4, p4) (bc6hEncPackDelta5 (d 1 0)) (dbits.getD 0 5)
    let (a6, p6) := bc6hEncPut (a5, p5) (bc6hEncPackDelta5 (d 1 1)) (dbits.getD 1 5)
    let (a7, p7) := bc6hEncPut (a6, p6) (bc6hEncPackDelta5 (d 1 2)) (dbits.getD 2 5)
    let bits := bc6hEncTail (a7, p7) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode678_sf16` for mode 6. -/
def bc6hEncMode6Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  bc6hEncMode678Sf16 8 [6, 5, 5] 0x12 pix

/-- `tc_bc6h_mode678_sf16` for mode 7. -/
def bc6hEncMode7Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  bc6hEncMode678Sf16 8 [5, 6, 5] 0x16 pix

/-- `tc_bc6h_mode678_sf16` for mode 8. -/
def bc6hEncMode8Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  bc6hEncMode678Sf16 8 [5, 5, 6] 0x1A pix

/-! ## One-region signed modes 12/13 -/

/-- `tc_bc6h_mode12_sf16`: 12-bit signed primary + 8-bit signed deltas. -/
def bc6hEncMode12Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegionS 12 2048 pix
  let dr := hi.getD 0 0 - lo.getD 0 0
  let dg := hi.getD 1 0 - lo.getD 1 0
  let db := hi.getD 2 0 - lo.getD 2 0
  if dr < -128 || dr > 127 || dg < -128 || dg > 127 || db < -128 || db > 127 then none
  else
    let r0 := bc6hPackSignedN (lo.getD 0 0) 12
    let g0 := bc6hPackSignedN (lo.getD 1 0) 12
    let b0 := bc6hPackSignedN (lo.getD 2 0) 12
    let r0lo := r0 &&& 1023
    let g0lo := g0 &&& 1023
    let b0lo := b0 &&& 1023
    let r0hi := (r0 >>> 10) &&& 3
    let g0hi := (g0 >>> 10) &&& 3
    let b0hi := (b0 >>> 10) &&& 3
    let step := fun (acc : Nat × Nat) (v n : Nat) =>
      (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
    let (a1, p1) := step (0, 0) 0x0B 5
    let (a2, p2) := step (a1, p1) r0lo 10
    let (a3, p3) := step (a2, p2) g0lo 10
    let (a4, p4) := step (a3, p3) b0lo 10
    let (a5, p5) := step (a4, p4) (dr.emod 256).toNat 8
    let (a6, p6) := step (a5, p5) r0hi 2
    let (a7, p7) := step (a6, p6) (dg.emod 256).toNat 8
    let (a8, p8) := step (a7, p7) g0hi 2
    let (a9, p9) := step (a8, p8) (db.emod 256).toNat 8
    let (a10, p10) := step (a9, p9) b0hi 2
    let (a11, p11) := step (a10, p10) (sel.getD 0 0) 3
    let (aF, _) := (List.range 15).foldl (fun (st : Nat × Nat) k =>
      step st (sel.getD (k + 1) 0) 4) (a11, p11)
    let err := (bc6hChooseSelectorsSf16 target lo hi).2
    some ((List.range 16).map (fun i => (aF >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode13_sf16`: 16-bit signed primary + 4-bit signed deltas. -/
def bc6hEncMode13Sf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegionS 16 32768 pix
  let dr := hi.getD 0 0 - lo.getD 0 0
  let dg := hi.getD 1 0 - lo.getD 1 0
  let db := hi.getD 2 0 - lo.getD 2 0
  if dr < -8 || dr > 7 || dg < -8 || dg > 7 || db < -8 || db > 7 then none
  else
    let r0 := bc6hPackSignedN (lo.getD 0 0) 16
    let g0 := bc6hPackSignedN (lo.getD 1 0) 16
    let b0 := bc6hPackSignedN (lo.getD 2 0) 16
    let r0lo := r0 &&& 1023
    let g0lo := g0 &&& 1023
    let b0lo := b0 &&& 1023
    let r0hi := (r0 >>> 10) &&& 63
    let g0hi := (g0 >>> 10) &&& 63
    let b0hi := (b0 >>> 10) &&& 63
    let step := fun (acc : Nat × Nat) (v n : Nat) =>
      (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
    let (a1, p1) := step (0, 0) 0x0F 5
    let (a2, p2) := step (a1, p1) r0lo 10
    let (a3, p3) := step (a2, p2) g0lo 10
    let (a4, p4) := step (a3, p3) b0lo 10
    let (a5, p5) := step (a4, p4) (dr.emod 16).toNat 4
    let (a6, p6) := step (a5, p5) r0hi 6
    let (a7, p7) := step (a6, p6) (dg.emod 16).toNat 4
    let (a8, p8) := step (a7, p7) g0hi 6
    let (a9, p9) := step (a8, p8) (db.emod 16).toNat 4
    let (a10, p10) := step (a9, p9) b0hi 6
    let (a11, p11) := step (a10, p10) (sel.getD 0 0) 3
    let (aF, _) := (List.range 15).foldl (fun (st : Nat × Nat) k =>
      step st (sel.getD (k + 1) 0) 4) (a11, p11)
    let err := (bc6hChooseSelectorsSf16 target lo hi).2
    some ((List.range 16).map (fun i => (aF >>> (8 * i)) &&& 0xFF), err)

end Texcomp
