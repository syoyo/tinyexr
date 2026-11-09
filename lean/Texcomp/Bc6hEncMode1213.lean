/-
  TinyEXR - Lean 4 formalization of the BC6H single-region encoders
  (modes 12 and 13) and the shared endpoint refinement.

  Ports `tc_bc6h_refine_uf16`, `tc_bc6h_mode12_uf16` and
  `tc_bc6h_mode13_uf16` in `tools/texcomp/src/texcomp_bc6h.c`. Both modes
  are single-region: quantise to 12/16 bits, pick the better of the
  bounding-box and luma-extreme endpoint pairs, run the three refinement
  rounds, apply the anchor swap when the first selector's top bit is set,
  then emit the mode-specific layout (12-bit primary + 8-bit signed delta
  for mode 12; 16-bit primary + 4-bit signed delta for mode 13).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hKernels

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc6h_refine_uf16`: three least-squares refinement rounds on the two
  endpoints of a single region. Returns the improved `(lo, hi, sel, err)`;
  `err` is the best selector error seen (C returns that value). -/
def bc6hRefineUf16 (q target : List (List Nat)) (lo hi : List Nat)
    (sel0 : List Nat) : List Nat × List Nat × List Nat × Nat :=
  let best0 := bc6hChooseSelectorsUf16 target lo hi
  let round (st : List Nat × List Nat × List Nat × Nat) (_ : Nat) :=
    let (clo, chi, csel, cerr) := st
    let sums := (List.range 3).map (fun c =>
      (List.range 16).foldl (fun (acc : Int × Int × Int × Int × Int) i =>
        let b : Int := Int.ofNat (bc7Weights4.getD (csel.getD i 0) 0)
        let a : Int := 64 - b
        let p : Int := Int.ofNat ((q.getD i [0, 0, 0]).getD c 0)
        (acc.1 + a * a, acc.2.1 + a * b, acc.2.2.1 + b * b,
         acc.2.2.2.1 + a * p, acc.2.2.2.2 + b * p)) (0, 0, 0, 0, 0))
    let cl := fun (x : Int) => if x < 0 then 0 else if x > 1023 then 1023 else x.toNat
    let nep : List Nat × List Nat :=
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
    let (nsel, ne) := bc6hChooseSelectorsUf16 target nlo nhi
    if ne < cerr then (nlo, nhi, nsel, ne) else (clo, chi, csel, cerr)
  (List.range 3).foldl round (lo, hi, best0.1, best0.2)

/-- One-region prelude shared by modes 12/13: quantise, choose the better of
  the box and luma endpoint pairs, refine, and apply the anchor swap.
  Returns `(q, target, lo, hi, sel)`. -/
def bc6hEncOneRegion (qbits maxv : Nat) (pix : List (List UInt32)) :
    List (List Nat) × List (List Nat) × List Nat × List Nat × List Nat :=
  let q := (List.range 16).map (fun i =>
    (List.range 3).map (fun c => bc6hQuantUf16N ((pix.getD i []).getD c 0) qbits))
  let target := (List.range 16).map (fun i =>
    (List.range 3).map (fun c =>
      bc6hUnquantUf16ToMag (bc6hQuantUf16 ((pix.getD i []).getD c 0))))
  -- Bounding box of the quantised endpoints.
  let box := (List.range 16).foldl (fun (acc : List Nat × List Nat) i =>
    let row := q.getD i [0, 0, 0]
    ((List.range 3).map (fun c => Nat.min (acc.1.getD c maxv) (row.getD c 0)),
     (List.range 3).map (fun c => Nat.max (acc.2.getD c 0) (row.getD c 0))))
    ((List.range 3).map (fun _ => maxv), (List.range 3).map (fun _ => 0))
  -- Luma extremes over the reconstructed target values (min: first wins,
  -- max: last wins, as C's `<` / `>=`).
  let luma := (List.range 16).foldl (fun (acc : Nat × Nat × Nat × Nat) i =>
    let t := target.getD i [0, 0, 0]
    let l := t.getD 0 0 * 38 + t.getD 1 0 * 76 + t.getD 2 0 * 14
    let (minL, maxL, minI, maxI) := acc
    let minI := if l < minL then i else minI
    let minL := if l < minL then l else minL
    let maxI := if l ≥ maxL then i else maxI
    let maxL := if l ≥ maxL then l else maxL
    (minL, maxL, minI, maxI)) (0xFFFFFFFF, 0, 0, 0)
  let lumaLo := q.getD luma.2.2.1 [0, 0, 0]
  let lumaHi := q.getD luma.2.2.2 [0, 0, 0]
  let lsel := bc6hChooseSelectorsUf16 target lumaLo lumaHi
  let bsel := bc6hChooseSelectorsUf16 target box.1 box.2
  let (lo0, hi0, sel0) :=
    if lsel.2 < bsel.2 then (lumaLo, lumaHi, lsel.1) else (box.1, box.2, bsel.1)
  let refined := bc6hRefineUf16 q target lo0 hi0 sel0
  let (rlo, rhi, rsel) := (refined.1, refined.2.1, refined.2.2.1)
  -- Anchor swap: selector 0's top bit (bit 3 of a 4-bit index) must be 0.
  if (rsel.getD 0 0) &&& 8 != 0 then
    ((List.range 3).map (fun c => rhi.getD c 0),
     (List.range 3).map (fun c => rlo.getD c 0),
     (List.range 16).map (fun i => 15 - rsel.getD i 0))
    |> fun (a, b, c) => (q, target, a, b, c)
  else (q, target, rlo, rhi, rsel)

/-- `tc_bc6h_mode12_uf16`: 12-bit primary + 8-bit signed delta, one region. -/
def bc6hEncMode12Uf16 (pix : List (List UInt32)) :
    Option (List Nat × Nat) :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegion 12 4095 pix
  let dr := Int.ofNat (hi.getD 0 0) - Int.ofNat (lo.getD 0 0)
  let dg := Int.ofNat (hi.getD 1 0) - Int.ofNat (lo.getD 1 0)
  let db := Int.ofNat (hi.getD 2 0) - Int.ofNat (lo.getD 2 0)
  if dr < -128 || dr > 127 || dg < -128 || dg > 127 || db < -128 || db > 127 then none
  else
    let r0lo := (lo.getD 0 0) &&& 1023
    let g0lo := (lo.getD 1 0) &&& 1023
    let b0lo := (lo.getD 2 0) &&& 1023
    let r0hi := (lo.getD 0 0) >>> 10 &&& 3
    let g0hi := (lo.getD 1 0) >>> 10 &&& 3
    let b0hi := (lo.getD 2 0) >>> 10 &&& 3
    let rev2 := fun (v : Nat) => ((v &&& 1) <<< 1) ||| ((v >>> 1) &&& 1)
    let step := fun (acc : Nat × Nat) (v n : Nat) =>
      (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
    let (a1, p1) := step (0, 0) 0x0B 5
    let (a2, p2) := step (a1, p1) r0lo 10
    let (a3, p3) := step (a2, p2) g0lo 10
    let (a4, p4) := step (a3, p3) b0lo 10
    let (a5, p5) := step (a4, p4) (Int32.ofInt dr).toUInt32.toNat 8
    let (a6, p6) := step (a5, p5) (rev2 r0hi) 2
    let (a7, p7) := step (a6, p6) (Int32.ofInt dg).toUInt32.toNat 8
    let (a8, p8) := step (a7, p7) (rev2 g0hi) 2
    let (a9, p9) := step (a8, p8) (Int32.ofInt db).toUInt32.toNat 8
    let (a10, p10) := step (a9, p9) (rev2 b0hi) 2
    let (a11, p11) := step (a10, p10) (sel.getD 0 0) 3
    let (aF, _) := (List.range 15).foldl (fun (st : Nat × Nat) k =>
      step st (sel.getD (k + 1) 0) 4) (a11, p11)
    let err := (bc6hChooseSelectorsUf16 target lo hi).2
    some ((List.range 16).map (fun i => (aF >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode13_uf16`: 16-bit primary + 4-bit signed delta, one region. -/
def bc6hEncMode13Uf16 (pix : List (List UInt32)) :
    Option (List Nat × Nat) :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegion 16 65535 pix
  let dr := Int.ofNat (hi.getD 0 0) - Int.ofNat (lo.getD 0 0)
  let dg := Int.ofNat (hi.getD 1 0) - Int.ofNat (lo.getD 1 0)
  let db := Int.ofNat (hi.getD 2 0) - Int.ofNat (lo.getD 2 0)
  if dr < -8 || dr > 7 || dg < -8 || dg > 7 || db < -8 || db > 7 then none
  else
    let r0lo := (lo.getD 0 0) &&& 1023
    let g0lo := (lo.getD 1 0) &&& 1023
    let b0lo := (lo.getD 2 0) &&& 1023
    let rev6 := fun (lo6 : Nat) =>
      (List.range 6).foldl (fun acc bi => acc ||| (((lo6 >>> bi) &&& 1) <<< (5 - bi))) 0
    let r0hi := rev6 ((lo.getD 0 0) >>> 10 &&& 63)
    let g0hi := rev6 ((lo.getD 1 0) >>> 10 &&& 63)
    let b0hi := rev6 ((lo.getD 2 0) >>> 10 &&& 63)
    let step := fun (acc : Nat × Nat) (v n : Nat) =>
      (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
    let (a1, p1) := step (0, 0) 0x0F 5
    let (a2, p2) := step (a1, p1) r0lo 10
    let (a3, p3) := step (a2, p2) g0lo 10
    let (a4, p4) := step (a3, p3) b0lo 10
    let (a5, p5) := step (a4, p4) (Int32.ofInt dr).toUInt32.toNat 4
    let (a6, p6) := step (a5, p5) r0hi 6
    let (a7, p7) := step (a6, p6) (Int32.ofInt dg).toUInt32.toNat 4
    let (a8, p8) := step (a7, p7) g0hi 6
    let (a9, p9) := step (a8, p8) (Int32.ofInt db).toUInt32.toNat 4
    let (a10, p10) := step (a9, p9) b0hi 6
    let (a11, p11) := step (a10, p10) (sel.getD 0 0) 3
    let (aF, _) := (List.range 15).foldl (fun (st : Nat × Nat) k =>
      step st (sel.getD (k + 1) 0) 4) (a11, p11)
    let err := (bc6hChooseSelectorsUf16 target lo hi).2
    some ((List.range 16).map (fun i => (aF >>> (8 * i)) &&& 0xFF), err)

end Texcomp
