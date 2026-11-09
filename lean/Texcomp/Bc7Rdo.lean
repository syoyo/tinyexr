/-
  TinyEXR - Lean 4 formalization of the BC7 decoder-driven RDO pass.

  Ports `tc_bc7_rdo_pass` in `tools/texcomp/src/texcomp_bc7.c`. For each
  block the pass decodes its own encoding and the last `TC_BC7_RDO_WINDOW`
  (64) decoded blocks, then reuses the recent encoding whose *decoded*
  pixels best match the source when the extra error stays within the
  rate-distortion budget `rdo^2 * 16 * 4`. The ring stores decoded pixels,
  so reuse never chains.

  The image gather (`tc_bc7_gather_block`) is modelled by the caller: the
  pass takes the already-gathered 64-byte source blocks.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc7AllModes

namespace Texcomp

set_option linter.unusedVariables false

/-- Number of recent blocks kept for reuse (`TC_BC7_RDO_WINDOW`). -/
def bc7RdoWindow : Nat := 64

/-- Decode a BC7 block to 64 flattened RGBA bytes (texel-major). -/
def bc7DecodeBlockBytes (bytes : Fin 16 → UInt8) : List Nat :=
  ((List.range 16).map (fun k =>
    let (r, g, b, a) := bc7DecodeBlock bytes ⟨k % 16, Nat.mod_lt k (by decide)⟩
    [r.toNat, g.toNat, b.toNat, a.toNat])).flatten

/-- `tc_bc7_block_sse`: squared error over the 64 RGBA bytes. -/
def bc7BlockSse (a b : List Nat) : Int :=
  (List.range 64).foldl (fun (acc : Int) t =>
    let d := Int.ofNat (a.getD t 0) - Int.ofNat (b.getD t 0)
    acc + d * d) 0

/-- `tc_bc7_rdo_pass`: `src` holds the gathered 64-byte source blocks and
  `blk` the 16-byte encodings; returns the (possibly rewritten) encodings. -/
def bc7RdoPass (src blk : List (List Nat)) (rdo : Nat) : List (List Nat) :=
  let thresh : Int := Int.ofNat rdo * Int.ofNat rdo * 16 * 4
  let n := min src.length blk.length
  let step (st : List (List Nat) × List (List Nat) × List Nat × Nat) (i : Nat) :=
    let (outAcc, ring, ringIdx, ringCount) := st
    let cur := src.getD i []
    let ownBytes := blk.getD i []
    let own := bc7DecodeBlockBytes (fun t => UInt8.ofNat (ownBytes.getD t.val 0))
    let ownErr := bc7BlockSse cur own
    let lim := min ringCount bc7RdoWindow
    let pick : Option (Int × Nat) := (List.range lim).foldl (fun acc k =>
      let sse := bc7BlockSse cur (ring.getD k [])
      match acc with
      | none => some (sse, k)
      | some (best, _) => if sse < best then some (sse, k) else acc) none
    let (outBlk, finalDec) : List Nat × List Nat :=
      match pick with
      | some (best, slot) =>
        if best - ownErr ≤ thresh then
          (blk.getD (ringIdx.getD slot i) [], ring.getD slot [])
        else (ownBytes, own)
      | none => (ownBytes, own)
    let slot := ringCount % bc7RdoWindow
    (outAcc ++ [outBlk], ring.set slot finalDec, ringIdx.set slot i, ringCount + 1)
  let init : List (List Nat) × List (List Nat) × List Nat × Nat :=
    ([], List.replicate bc7RdoWindow [], List.replicate bc7RdoWindow 0, 0)
  let (out, _, _, _) := (List.range n).foldl step init
  out

end Texcomp
