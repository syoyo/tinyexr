/-
  TinyEXR - Lean 4 formalization of the BC6H per-block mode selection.

  Ports `tc_encode_bc6h_block_uf16` and `tc_encode_bc6h_block_sf16` in
  `tools/texcomp/src/texcomp_bc6h.c`. Both start from the one-region
  10-bit encoding (packed with the `00011` mode code), then try further
  modes in a fixed order and keep the smallest reconstruction error. The
  unsigned driver only keeps trying while the current error is above
  `48 * 256 * 256`; the signed driver tries modes 12/13 unconditionally
  and everything else under that same threshold.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hEncMode1
import Texcomp.Bc6hEncMode9
import Texcomp.Bc6hEncMode1213
import Texcomp.Bc6hEncMode678
import Texcomp.Bc6hEncSf16

namespace Texcomp

set_option linter.unusedVariables false

/-- The per-block error threshold the C driver uses to stop trying modes. -/
def bc6hModeThreshold : Nat := 48 * 256 * 256

/-- Pack the one-region `00011` block (used as the initial candidate by both
  drivers): mode code, three 10-bit low endpoints, three 10-bit high
  endpoints, then a 3-bit anchor selector and 4-bit indices. -/
def bc6hEncPackOneRegion (lo hi sel : List Nat) : List Nat :=
  let step := fun (acc : Nat × Nat) (v n : Nat) =>
    (acc.1 ||| ((v &&& ((1 <<< n) - 1)) <<< acc.2), acc.2 + n)
  let (a1, p1) := step (0, 0) 0x03 5
  let (a2, p2) := step (a1, p1) (lo.getD 0 0) 10
  let (a3, p3) := step (a2, p2) (lo.getD 1 0) 10
  let (a4, p4) := step (a3, p3) (lo.getD 2 0) 10
  let (a5, p5) := step (a4, p4) (hi.getD 0 0) 10
  let (a6, p6) := step (a5, p5) (hi.getD 1 0) 10
  let (a7, p7) := step (a6, p6) (hi.getD 2 0) 10
  let (a8, p8) := step (a7, p7) (sel.getD 0 0) 3
  let (aF, _) := (List.range 15).foldl (fun (st : Nat × Nat) k =>
    step st (sel.getD (k + 1) 0) 4) (a8, p8)
  (List.range 16).map (fun i => (aF >>> (8 * i)) &&& 0xFF)

/-- Keep a candidate when it beats the current error (C's `e < best_err`,
  where a failed mode returns `UINT64_MAX`). -/
def bc6hTryCandidate (st : Nat × List Nat) (c : Option (List Nat × Nat)) :
    Nat × List Nat :=
  match c with
  | none => st
  | some (b, e) => if e < st.1 then (e, b) else st

/-- Guarded candidate step: only evaluate while the current error is above
  the driver's threshold. -/
def bc6hTryGuarded (st : Nat × List Nat) (c : Option (List Nat × Nat)) :
    Nat × List Nat :=
  if st.1 > bc6hModeThreshold then bc6hTryCandidate st c else st

/-- `tc_encode_bc6h_block_uf16`: one-region 10-bit seed, then modes
  9/0/1/2/3/4/5/10/12/13/6/7/8 in that order. -/
def bc6hEncodeBlockUf16 (pix : List (List UInt32)) : List Nat :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegion 10 1023 pix
  let err0 := (bc6hChooseSelectorsUf16 target lo hi).2
  let base : Nat × List Nat := (err0, bc6hEncPackOneRegion lo hi sel)
  let cands : List (Option (List Nat × Nat)) :=
    [bc6hEncMode9Uf16 pix, bc6hEncMode0Uf16 pix, bc6hEncMode1Uf16 pix,
     bc6hEncMode2Uf16 pix, bc6hEncMode3Uf16 pix, bc6hEncMode4Uf16 pix,
     bc6hEncMode5Uf16 pix, bc6hEncMode10Uf16 pix, bc6hEncMode12Uf16 pix,
     bc6hEncMode13Uf16 pix, bc6hEncMode6Uf16 pix, bc6hEncMode7Uf16 pix,
     bc6hEncMode8Uf16 pix]
  let (_err, out) := cands.foldl bc6hTryGuarded base
  out

/-- `tc_encode_bc6h_block_sf16`: signed one-region 10-bit seed, modes 12/13
  unconditionally, then 9/0/1/5/2/3/4/6/7/8 under the same threshold. -/
def bc6hEncodeBlockSf16 (pix : List (List UInt32)) : List Nat :=
  let (q, target, lo, hi, sel) := bc6hEncOneRegionSeedS 10 1024 pix
  let err0 := (bc6hChooseSelectorsSf16 target lo hi).2
  let loP := lo.map bc6hPackSigned10
  let hiP := hi.map bc6hPackSigned10
  let base : Nat × List Nat := (err0, bc6hEncPackOneRegion loP hiP sel)
  let s1 := bc6hTryCandidate base (bc6hEncMode12Sf16 pix)
  let s2 := bc6hTryCandidate s1 (bc6hEncMode13Sf16 pix)
  let cands : List (Option (List Nat × Nat)) :=
    [bc6hEncMode9Sf16 pix, bc6hEncMode0Sf16 pix, bc6hEncMode1Sf16 pix,
     bc6hEncMode5Sf16 pix, bc6hEncMode2Sf16 pix, bc6hEncMode3Sf16 pix,
     bc6hEncMode4Sf16 pix, bc6hEncMode6Sf16 pix, bc6hEncMode7Sf16 pix,
     bc6hEncMode8Sf16 pix]
  let (_err, out) := cands.foldl bc6hTryGuarded s2
  out

end Texcomp
