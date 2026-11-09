/-
  TinyEXR - Lean 4 formalization of the BC6H generic two-region delta
  encoders (modes 6, 7, 8).

  Ports `tc_bc6h_mode678_uf16` in `tools/texcomp/src/texcomp_bc6h.c`: an
  8-bit primary per channel plus a 6/5/5-bit signed delta set (mode 6 =
  R6G5B5, mode 7 = R5G6B5, mode 8 = R5G5B6). Everything up to the bit
  layout is the shared delta search already used by modes 2/3/4/5.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode234

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_bc6h_mode678_uf16` for mode 6 (R6G5B5 deltas). -/
def bc6hEncMode6Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 8 255 [6, 5, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x12 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0) 8
    let (a3, p3) := bc6hEncPut (a2, p2) ((epAt 3 1) >>> 4 &&& 1) 1
    let (a4, p4) := bc6hEncPut (a3, p3) ((epAt 2 2) >>> 4 &&& 1) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (epAt 0 1) 8
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 3 2) >>> 2 &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 2 1) >>> 4 &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (epAt 0 2) 8
    let (a9, p9) := bc6hEncPut (a8, p8) ((epAt 3 2) >>> 3 &&& 1) 1
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 3 2) >>> 4 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hEncPackDelta5 (d 1 0)) 6
    let (a12, p12) := bc6hEncPut (a11, p11) ((epAt 2 1) &&& 0xF) 4
    let (a13, p13) := bc6hEncPut (a12, p12) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a14, p14) := bc6hEncPut (a13, p13) ((epAt 3 2) &&& 1) 1
    let (a15, p15) := bc6hEncPut (a14, p14) ((epAt 3 1) &&& 0xF) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a17, p17) := bc6hEncPut (a16, p16) ((epAt 3 2) >>> 1 &&& 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 2 2) &&& 0xF) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 2 0)) 6
    let (a20, p20) := bc6hEncPut (a19, p19) (bc6hEncPackDelta5 (d 3 0)) 6
    let bits := bc6hEncTail (a20, p20) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode678_uf16` for mode 7 (R5G6B5 deltas). -/
def bc6hEncMode7Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 8 255 [5, 6, 5] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x16 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0) 8
    let (a3, p3) := bc6hEncPut (a2, p2) ((epAt 3 2) &&& 1) 1
    let (a4, p4) := bc6hEncPut (a3, p3) ((epAt 2 2) >>> 4 &&& 1) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (epAt 0 1) 8
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 2 1) >>> 5 &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 2 1) >>> 4 &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (epAt 0 2) 8
    let (a9, p9) := bc6hEncPut (a8, p8) ((epAt 3 1) >>> 5 &&& 1) 1
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 3 2) >>> 4 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a12, p12) := bc6hEncPut (a11, p11) ((epAt 3 1) >>> 4 &&& 1) 1
    let (a13, p13) := bc6hEncPut (a12, p12) ((epAt 2 1) &&& 0xF) 4
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hEncPackDelta5 (d 1 1)) 6
    let (a15, p15) := bc6hEncPut (a14, p14) ((epAt 3 1) &&& 0xF) 4
    let (a16, p16) := bc6hEncPut (a15, p15) (bc6hEncPackDelta5 (d 1 2)) 5
    let (a17, p17) := bc6hEncPut (a16, p16) ((epAt 3 2) >>> 1 &&& 1) 1
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 2 2) &&& 0xF) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 3 2) >>> 2 &&& 1) 1
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a22, p22) := bc6hEncPut (a21, p21) ((epAt 3 2) >>> 3 &&& 1) 1
    let bits := bc6hEncTail (a22, p22) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

/-- `tc_bc6h_mode678_uf16` for mode 8 (R5G5B6 deltas). -/
def bc6hEncMode8Uf16 (pix : List (List UInt32)) : Option (List Nat × Nat) :=
  match bc6hEncDeltaSearch 8 255 [5, 5, 6] pix with
  | none => none
  | some (bestP, bep, bsel, err) =>
    let epAt (r c : Nat) : Nat := (bep.getD r [0, 0, 0]).getD c 0
    let d := fun (r c : Nat) => Int.ofNat (epAt r c) - Int.ofNat (epAt 0 c)
    let anchor := bc6hEncPart2Anchor.getD bestP 15
    let (a1, p1) := bc6hEncPut (0, 0) 0x1A 5
    let (a2, p2) := bc6hEncPut (a1, p1) (epAt 0 0) 8
    let (a3, p3) := bc6hEncPut (a2, p2) ((epAt 3 2) >>> 1 &&& 1) 1
    let (a4, p4) := bc6hEncPut (a3, p3) ((epAt 2 2) >>> 4 &&& 1) 1
    let (a5, p5) := bc6hEncPut (a4, p4) (epAt 0 1) 8
    let (a6, p6) := bc6hEncPut (a5, p5) ((epAt 2 2) >>> 5 &&& 1) 1
    let (a7, p7) := bc6hEncPut (a6, p6) ((epAt 2 1) >>> 4 &&& 1) 1
    let (a8, p8) := bc6hEncPut (a7, p7) (epAt 0 2) 8
    let (a9, p9) := bc6hEncPut (a8, p8) ((epAt 3 2) >>> 5 &&& 1) 1
    let (a10, p10) := bc6hEncPut (a9, p9) ((epAt 3 2) >>> 4 &&& 1) 1
    let (a11, p11) := bc6hEncPut (a10, p10) (bc6hEncPackDelta5 (d 1 0)) 5
    let (a12, p12) := bc6hEncPut (a11, p11) ((epAt 3 1) >>> 4 &&& 1) 1
    let (a13, p13) := bc6hEncPut (a12, p12) ((epAt 2 1) &&& 0xF) 4
    let (a14, p14) := bc6hEncPut (a13, p13) (bc6hEncPackDelta5 (d 1 1)) 5
    let (a15, p15) := bc6hEncPut (a14, p14) ((epAt 3 2) &&& 1) 1
    let (a16, p16) := bc6hEncPut (a15, p15) ((epAt 3 1) &&& 0xF) 4
    let (a17, p17) := bc6hEncPut (a16, p16) (bc6hEncPackDelta5 (d 1 2)) 6
    let (a18, p18) := bc6hEncPut (a17, p17) ((epAt 2 2) &&& 0xF) 4
    let (a19, p19) := bc6hEncPut (a18, p18) (bc6hEncPackDelta5 (d 2 0)) 5
    let (a20, p20) := bc6hEncPut (a19, p19) ((epAt 3 2) >>> 2 &&& 1) 1
    let (a21, p21) := bc6hEncPut (a20, p20) (bc6hEncPackDelta5 (d 3 0)) 5
    let (a22, p22) := bc6hEncPut (a21, p21) ((epAt 3 2) >>> 3 &&& 1) 1
    let bits := bc6hEncTail (a22, p22) bestP anchor bsel
    some ((List.range 16).map (fun i => (bits >>> (8 * i)) &&& 0xFF), err)

end Texcomp
