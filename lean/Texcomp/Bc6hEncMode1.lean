/-
  TinyEXR - Lean 4 formalization of the BC6H mode-1 encoder.

  Ports `tc_bc6h_mode1_uf16` in `tools/texcomp/src/texcomp_bc6h.c`: a
  7-bit primary per channel with 6-bit signed deltas, sharing the
  two-region TOPK search, refinement and anchor fix-up with modes 2/3/4
  (same `dbits` delta limits). Note the C writer feeds the 6-bit delta
  fields through `tc_bc6h_pack_delta5`, which clamps to [-16, 15] even
  though the search admits [-32, 31]; the model reproduces that quirk.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode234

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc6h_mode1_uf16`: two regions, 7-bit primary, 6-bit deltas. -/
def bc6hEncMode1Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 7 127 [6, 6, 6] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 1 2
    let (a2, p2) := bc6hEncPut (a1, p1) ((epAt 2 1) >>> 5 &&& 1) 1
    let (a3, p3) := bc6hEncPut (a2, p2) ((epAt 3 1) >>> 4 &&& 1) 1
    let (a4, p4) := bc6hEncPut (a3, p3) ((epAt 3 1) >>> 5 &&& 1) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (epAt 0 0) 7
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 3 2) &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 3 2) >>> 1 &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) ((epAt 2 2) >>> 4 &&& 1) 1
    let (a9, p9) := bc6hEncPut (a8, p8) (epAt 0 1) 7
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 2 2) >>> 5 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) ((epAt 3 2) >>> 2 &&& 1) 1
    let (a12, p12) := bc6hEncPut (a11, p11) ((epAt 2 1) >>> 4 &&& 1) 1
    let (a13, p13) := bc6hEncPut (a12, p12) (epAt 0 2) 7
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 3 2) >>> 3 &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) ((epAt 3 2) >>> 5 &&& 1) 1
    let (a16, p16) := bc6hEncPut (a15, p15) ((epAt 3 2) >>> 4 &&& 1) 1
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hEncPackDelta5 (d 1 0)) 6
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 2 1) &&& 0xF) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 1 1)) 6
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 3 1) &&& 0xF) 4
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hEncPackDelta5 (d 1 2)) 6
    let (a22, p22) := bc6hEncPut (a21, p21) ((epAt 2 2) &&& 0xF) 4
    let (a23, p23) := bc6hEncPut (a22, p22) (bc6hEncPackDelta5 (d 2 0)) 6
    let (a24, p24) := bc6hEncPut (a23, p23) (bc6hEncPackDelta5 (d 3 0)) 6
    let bits := bc6hEncTail (a24, p24) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

end Texcomp
