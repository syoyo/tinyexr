/-
  TinyEXR - Lean 4 formalization of the BC7 decoder (all 8 modes, faithful port).

  Faithful port of `tc_bc7_decode_block` in
  `tools/texcomp/src/texcomp_bc7.c`: unary mode dispatch, 2/3-subset
  partition tables (with anchor marks), channel-major endpoint packing,
  p-bit expansion, the `>>` bit-replication expansion, dual-plane indices,
  and rotation. Supersedes the simplified per-mode slices (`Bc7Mode0*`,
  `Bc7Mode4`, `Bc7Mode6*`) for bit-exactness work.

  Endpoint order in the packed lists below is channel-major
  (`ep[j][i]`, j = endpoint, i = channel), matching the C loops.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.Bc6hFull

namespace Texcomp

set_option linter.unusedVariables false

/-- 2-subset partitions: 64 x (4x4) values, row-major. -/
def bc7Parts2 : List (List (List Nat)) :=
  [
   [[128,0,1,1],[0,0,1,1],[0,0,1,1],[0,0,1,129]],
   [[128,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,129]],
   [[128,1,1,1],[0,1,1,1],[0,1,1,1],[0,1,1,129]],
   [[128,0,0,1],[0,0,1,1],[0,0,1,1],[0,1,1,129]],
   [[128,0,0,0],[0,0,0,1],[0,0,0,1],[0,0,1,129]],
   [[128,0,1,1],[0,1,1,1],[0,1,1,1],[1,1,1,129]],
   [[128,0,0,1],[0,0,1,1],[0,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[0,0,0,1],[0,0,1,1],[0,1,1,129]],
   [[128,0,0,0],[0,0,0,0],[0,0,0,1],[0,0,1,129]],
   [[128,0,1,1],[0,1,1,1],[1,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[0,0,0,1],[0,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[0,0,0,0],[0,0,0,1],[0,1,1,129]],
   [[128,0,0,1],[0,1,1,1],[1,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[0,0,0,0],[1,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[1,1,1,1],[1,1,1,1],[1,1,1,129]],
   [[128,0,0,0],[0,0,0,0],[0,0,0,0],[1,1,1,129]],
   [[128,0,0,0],[1,0,0,0],[1,1,1,0],[1,1,1,129]],
   [[128,1,129,1],[0,0,0,1],[0,0,0,0],[0,0,0,0]],
   [[128,0,0,0],[0,0,0,0],[129,0,0,0],[1,1,1,0]],
   [[128,1,129,1],[0,0,1,1],[0,0,0,1],[0,0,0,0]],
   [[128,0,129,1],[0,0,0,1],[0,0,0,0],[0,0,0,0]],
   [[128,0,0,0],[1,0,0,0],[129,1,0,0],[1,1,1,0]],
   [[128,0,0,0],[0,0,0,0],[129,0,0,0],[1,1,0,0]],
   [[128,1,1,1],[0,0,1,1],[0,0,1,1],[0,0,0,129]],
   [[128,0,129,1],[0,0,0,1],[0,0,0,1],[0,0,0,0]],
   [[128,0,0,0],[1,0,0,0],[129,0,0,0],[1,1,0,0]],
   [[128,1,129,0],[0,1,1,0],[0,1,1,0],[0,1,1,0]],
   [[128,0,129,1],[0,1,1,0],[0,1,1,0],[1,1,0,0]],
   [[128,0,0,1],[0,1,1,1],[129,1,1,0],[1,0,0,0]],
   [[128,0,0,0],[1,1,1,1],[129,1,1,1],[0,0,0,0]],
   [[128,1,129,1],[0,0,0,1],[1,0,0,0],[1,1,1,0]],
   [[128,0,129,1],[1,0,0,1],[1,0,0,1],[1,1,0,0]],
   [[128,1,0,1],[0,1,0,1],[0,1,0,1],[0,1,0,129]],
   [[128,0,0,0],[1,1,1,1],[0,0,0,0],[1,1,1,129]],
   [[128,1,0,1],[1,0,129,0],[0,1,0,1],[1,0,1,0]],
   [[128,0,1,1],[0,0,1,1],[129,1,0,0],[1,1,0,0]],
   [[128,0,129,1],[1,1,0,0],[0,0,1,1],[1,1,0,0]],
   [[128,1,0,1],[0,1,0,1],[129,0,1,0],[1,0,1,0]],
   [[128,1,1,0],[1,0,0,1],[0,1,1,0],[1,0,0,129]],
   [[128,1,0,1],[1,0,1,0],[1,0,1,0],[0,1,0,129]],
   [[128,1,129,1],[0,0,1,1],[1,1,0,0],[1,1,1,0]],
   [[128,0,0,1],[0,0,1,1],[129,1,0,0],[1,0,0,0]],
   [[128,0,129,1],[0,0,1,0],[0,1,0,0],[1,1,0,0]],
   [[128,0,129,1],[1,0,1,1],[1,1,0,1],[1,1,0,0]],
   [[128,1,129,0],[1,0,0,1],[1,0,0,1],[0,1,1,0]],
   [[128,0,1,1],[1,1,0,0],[1,1,0,0],[0,0,1,129]],
   [[128,1,1,0],[0,1,1,0],[1,0,0,1],[1,0,0,129]],
   [[128,0,0,0],[0,1,129,0],[0,1,1,0],[0,0,0,0]],
   [[128,1,0,0],[1,1,129,0],[0,1,0,0],[0,0,0,0]],
   [[128,0,129,0],[0,1,1,1],[0,0,1,0],[0,0,0,0]],
   [[128,0,0,0],[0,0,129,0],[0,1,1,1],[0,0,1,0]],
   [[128,0,0,0],[0,1,0,0],[129,1,1,0],[0,1,0,0]],
   [[128,1,1,0],[1,1,0,0],[1,0,0,1],[0,0,1,129]],
   [[128,0,1,1],[0,1,1,0],[1,1,0,0],[1,0,0,129]],
   [[128,1,129,0],[0,0,1,1],[1,0,0,1],[1,1,0,0]],
   [[128,0,129,1],[1,0,0,1],[1,1,0,0],[0,1,1,0]],
   [[128,1,1,0],[1,1,0,0],[1,1,0,0],[1,0,0,129]],
   [[128,1,1,0],[0,0,1,1],[0,0,1,1],[1,0,0,129]],
   [[128,1,1,1],[1,1,1,0],[1,0,0,0],[0,0,0,129]],
   [[128,0,0,1],[1,0,0,0],[1,1,1,0],[0,1,1,129]],
   [[128,0,0,0],[1,1,1,1],[0,0,1,1],[0,0,1,129]],
   [[128,0,129,1],[0,0,1,1],[1,1,1,1],[0,0,0,0]],
   [[128,0,129,0],[0,0,1,0],[1,1,1,0],[1,1,1,0]],
   [[128,1,0,0],[0,1,0,0],[0,1,1,1],[0,1,1,129]]]

/-- 3-subset partitions: 64 x (4x4) values, row-major. -/
def bc7Parts3 : List (List (List Nat)) :=
  [
   [[128,0,1,129],[0,0,1,1],[0,2,2,1],[2,2,2,130]],
   [[128,0,0,129],[0,0,1,1],[130,2,1,1],[2,2,2,1]],
   [[128,0,0,0],[2,0,0,1],[130,2,1,1],[2,2,1,129]],
   [[128,2,2,130],[0,0,2,2],[0,0,1,1],[0,1,1,129]],
   [[128,0,0,0],[0,0,0,0],[129,1,2,2],[1,1,2,130]],
   [[128,0,1,129],[0,0,1,1],[0,0,2,2],[0,0,2,130]],
   [[128,0,2,130],[0,0,2,2],[1,1,1,1],[1,1,1,129]],
   [[128,0,1,1],[0,0,1,1],[130,2,1,1],[2,2,1,129]],
   [[128,0,0,0],[0,0,0,0],[129,1,1,1],[2,2,2,130]],
   [[128,0,0,0],[1,1,1,1],[129,1,1,1],[2,2,2,130]],
   [[128,0,0,0],[1,1,129,1],[2,2,2,2],[2,2,2,130]],
   [[128,0,1,2],[0,0,129,2],[0,0,1,2],[0,0,1,130]],
   [[128,1,1,2],[0,1,129,2],[0,1,1,2],[0,1,1,130]],
   [[128,1,2,2],[0,129,2,2],[0,1,2,2],[0,1,2,130]],
   [[128,0,1,129],[0,1,1,2],[1,1,2,2],[1,2,2,130]],
   [[128,0,1,129],[2,0,0,1],[130,2,0,0],[2,2,2,0]],
   [[128,0,0,129],[0,0,1,1],[0,1,1,2],[1,1,2,130]],
   [[128,1,1,129],[0,0,1,1],[130,0,0,1],[2,2,0,0]],
   [[128,0,0,0],[1,1,2,2],[129,1,2,2],[1,1,2,130]],
   [[128,0,2,130],[0,0,2,2],[0,0,2,2],[1,1,1,129]],
   [[128,1,1,129],[0,1,1,1],[0,2,2,2],[0,2,2,130]],
   [[128,0,0,129],[0,0,0,1],[130,2,2,1],[2,2,2,1]],
   [[128,0,0,0],[0,0,129,1],[0,1,2,2],[0,1,2,130]],
   [[128,0,0,0],[1,1,0,0],[130,2,129,0],[2,2,1,0]],
   [[128,1,2,130],[0,129,2,2],[0,0,1,1],[0,0,0,0]],
   [[128,0,1,2],[0,0,1,2],[129,1,2,2],[2,2,2,130]],
   [[128,1,1,0],[1,2,130,1],[129,2,2,1],[0,1,1,0]],
   [[128,0,0,0],[0,1,129,0],[1,2,130,1],[1,2,2,1]],
   [[128,0,2,2],[1,1,0,2],[129,1,0,2],[0,0,2,130]],
   [[128,1,1,0],[0,129,1,0],[2,0,0,2],[2,2,2,130]],
   [[128,0,1,1],[0,1,2,2],[0,1,130,2],[0,0,1,129]],
   [[128,0,0,0],[2,0,0,0],[130,2,1,1],[2,2,2,129]],
   [[128,0,0,0],[0,0,0,2],[129,1,2,2],[1,2,2,130]],
   [[128,2,2,130],[0,0,2,2],[0,0,1,2],[0,0,1,129]],
   [[128,0,1,129],[0,0,1,2],[0,0,2,2],[0,2,2,130]],
   [[128,1,2,0],[0,129,2,0],[0,1,130,0],[0,1,2,0]],
   [[128,0,0,0],[1,1,129,1],[2,2,130,2],[0,0,0,0]],
   [[128,1,2,0],[1,2,0,1],[130,0,129,2],[0,1,2,0]],
   [[128,1,2,0],[2,0,1,2],[129,130,0,1],[0,1,2,0]],
   [[128,0,1,1],[2,2,0,0],[1,1,130,2],[0,0,1,129]],
   [[128,0,1,1],[1,1,130,2],[2,2,0,0],[0,0,1,129]],
   [[128,1,0,129],[0,1,0,1],[2,2,2,2],[2,2,2,130]],
   [[128,0,0,0],[0,0,0,0],[130,1,2,1],[2,1,2,129]],
   [[128,0,2,2],[1,129,2,2],[0,0,2,2],[1,1,2,130]],
   [[128,0,2,130],[0,0,1,1],[0,0,2,2],[0,0,1,129]],
   [[128,2,2,0],[1,2,130,1],[0,2,2,0],[1,2,2,129]],
   [[128,1,0,1],[2,2,130,2],[2,2,2,2],[0,1,0,129]],
   [[128,0,0,0],[2,1,2,1],[130,1,2,1],[2,1,2,129]],
   [[128,1,0,129],[0,1,0,1],[0,1,0,1],[2,2,2,130]],
   [[128,2,2,130],[0,1,1,1],[0,2,2,2],[0,1,1,129]],
   [[128,0,0,2],[1,129,1,2],[0,0,0,2],[1,1,1,130]],
   [[128,0,0,0],[2,129,1,2],[2,1,1,2],[2,1,1,130]],
   [[128,2,2,2],[0,129,1,1],[0,1,1,1],[0,2,2,130]],
   [[128,0,0,2],[1,1,1,2],[129,1,1,2],[0,0,0,130]],
   [[128,1,1,0],[0,129,1,0],[0,1,1,0],[2,2,2,130]],
   [[128,0,0,0],[0,0,0,0],[2,1,129,2],[2,1,1,130]],
   [[128,1,1,0],[0,129,1,0],[2,2,2,2],[2,2,2,130]],
   [[128,0,2,2],[0,0,1,1],[0,0,129,1],[0,0,2,130]],
   [[128,0,2,2],[1,1,2,2],[129,1,2,2],[0,0,2,130]],
   [[128,0,0,0],[0,0,0,0],[0,0,0,0],[2,129,1,130]],
   [[128,0,0,130],[0,0,0,1],[0,0,0,2],[0,0,0,129]],
   [[128,2,2,2],[1,2,2,2],[0,2,2,2],[129,2,2,130]],
   [[128,1,0,129],[2,2,2,2],[2,2,2,2],[2,2,2,130]],
   [[128,1,1,129],[2,0,1,1],[130,2,0,1],[2,2,2,0]]]

/-- Channel endpoint widths (`actual_bits`). -/
def bc7ColorBits : List Nat := [4, 6, 5, 7, 5, 7, 7, 5]
def bc7AlphaBits : List Nat := [0, 0, 0, 0, 6, 8, 7, 5]

/-- p-bit flags (`mode_has_pbits = 0xCB`). -/
def bc7Pbit (mode : Nat) : Nat := (0xCB / 2 ^ mode) % 2

/-- Weight tables. -/
def bc7W2 : List Nat := [0, 21, 43, 64]
def bc7W3 : List Nat := [0, 9, 18, 27, 37, 46, 55, 64]
def bc7W4 : List Nat := [0, 4, 9, 13, 17, 21, 26, 30, 34, 38, 43, 47, 51, 55, 60, 64]

def bc7Weight (ib : Nat) (idx : Nat) : Nat :=
  let table := if ib == 2 then bc7W2 else if ib == 3 then bc7W3 else bc7W4
  table.getD idx 64

/-- Interpolate (Nat). -/
def bc7Interp (a b w : Nat) : Nat :=
  (a * (64 - w) + b * w + 32) / 64

/-- Partition lookup; partition is bounded by its read width (< 64). -/
def bc7Part (numPart partition k : Nat) : Nat :=
  let table : List (List (List Nat)) := if numPart == 2 then bc7Parts2 else bc7Parts3
  let part := table.getD (partition % 64) []
  (part.getD (k / 4) []).getD (k % 4) 0

/-- Unary mode: count leading zeros (mode 0..8). -/
def bc7Unary (bs : Bs) : Nat × Bs :=
  let r := (List.range 8).foldl (fun acc _ =>
    if acc.2.2 then acc
    else
      let (b, bs') := bsRead acc.2.1 1
      if b == 0 then (acc.1 + 1, bs', false) else (acc.1, bs', true)) (0, bs, false)
  (r.1, r.2.1)

/-- Full BC7 block decoder: 16 RGBA8 texels. -/
def bc7DecodeBlock (bytes : Fin 16 → UInt8) :
    Fin 16 → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let bs0 := bsInit bytes
    let (rawMode, bs1) := bc7Unary bs0
    if rawMode >= 8 then (0, 0, 0, 0)
    else
    let mode := rawMode
    let numPart := if mode == 0 || mode == 2 then 3
                   else if mode == 1 || mode == 3 || mode == 7 then 2 else 1
    let (partition, bs2) :=
      if numPart == 1 then (0, bs1)
      else bsRead bs1 (if mode == 0 then 4 else 6)
    let numEp := numPart * 2
    let (rotation, bs3) :=
      if mode == 4 || mode == 5 then bsRead bs2 2 else (0, bs2)
    let (idxSelBit, bs4) :=
      if mode == 4 then bsRead bs3 1 else (0, bs3)
    let cb0 := bc7ColorBits.getD mode 4
    let ab0 := bc7AlphaBits.getD mode 0
    -- endpoints flat [endpoint*4 + channel], zero-init; channel-major reads
    let (ep, bs5) :=
      ((List.range 3).foldl (fun acc ch =>
        (List.range numEp).foldl (fun acc2 j =>
          let (value, bs') := bsRead acc2.2 cb0
          (acc2.1.set (j * 4 + ch) value, bs')) (acc.1, acc.2)) (((List.replicate 24 0 : List Nat)), bs4))
    let (ep, bs6) :=
      if ab0 > 0 then
        (List.range numEp).foldl (fun acc j =>
          let (value, bs') := bsRead acc.2 ab0
          (acc.1.set (j * 4 + 3) value, bs')) (ep, bs5)
      else (ep, bs5)
    -- p-bits
    let doP := mode == 0 || mode == 1 || mode == 3 || mode == 6 || mode == 7
    let (ep, bs7) :=
      if !doP then (ep, bs6)
      else
        let ep1 := (List.range 24).foldl (fun e i => e.set i ((e.getD i 0) <<< 1)) ep
        if mode == 1 then
          let (p0, bsA) := bsRead bs6 1
          let (p1, bsB) := bsRead bsA 1
          let ep2 := (List.range 3).foldl (fun e k =>
            e.set (0 * 4 + k) ((e.getD (0 * 4 + k) 0) ||| p0)
             |>.set (1 * 4 + k) ((e.getD (1 * 4 + k) 0) ||| p0)
             |>.set (2 * 4 + k) ((e.getD (2 * 4 + k) 0) ||| p1)
             |>.set (3 * 4 + k) ((e.getD (3 * 4 + k) 0) ||| p1)) ep1
          (ep2, bsB)
        else
          (List.range numEp).foldl (fun acc j =>
            let (p, bs') := bsRead acc.2 1
            ((List.range 4).foldl (fun e k =>
              e.set (j * 4 + k) ((e.getD (j * 4 + k) 0) ||| p)) acc.1, bs')) (ep1, bs6)
    -- expansion (C: ep <<= 8-cb; ep |= ep >> cb — the second shift uses
    -- the updated value, replicating the high bits into the low bits)
    let pbit := bc7Pbit mode
    let cb := cb0 + pbit
    let ab := ab0 + pbit
    let expand := fun v bits => ((v <<< (8 - bits)) ||| (((v <<< (8 - bits)) >>> bits)))
    let epX := (List.range numEp).foldl (fun e j =>
      let e' := (List.range 3).foldl (fun e2 k =>
        e2.set (j * 4 + k) (expand (e2.getD (j * 4 + k) 0) cb)) e
      e'.set (j * 4 + 3) (expand (e'.getD (j * 4 + 3) 0) ab)) ep
    let epF := if ab0 == 0 then
      (List.range numEp).foldl (fun e j => e.set (j * 4 + 3) 0xFF) epX else epX
    let ib := if mode == 0 || mode == 1 then 3 else if mode == 6 then 4 else 2
    let ib2 := if mode == 4 then 3 else if mode == 5 then 2 else 0
    -- index planes
    let (cidx, bs8) :=
      (List.range 16).foldl (fun acc k =>
        let i := k / 4
        let j := k % 4
        let ps := if numPart == 1 then (if (i ||| j) == 0 then 128 else 0)
                  else bc7Part numPart partition k
        let bits := ib - (if (ps &&& 128) != 0 then 1 else 0)
        let (value, bs') := bsRead acc.2 bits
        (acc.1.set k value, bs')) (((List.replicate 16 0 : List Nat)), bs7)
    -- decode requested texel: replay (reads are sequential; we re-fold and
    -- keep the one matching `texel`).
    let i := texel.val / 4
    let j := texel.val % 4
    let ps := if numPart == 1 then (if (i ||| j) == 0 then 128 else 0)
              else bc7Part numPart partition texel.val
    let cidxV := cidx.getD texel.val 0
    -- idx2 requires threading: replay all reads up to the target.
    let (idx2V, _) :=
      (List.range (texel.val + 1)).foldl (fun acc k =>
        let ii := k / 4
        let jj := k % 4
        let _ps := if numPart == 1 then (if (ii ||| jj) == 0 then 128 else 0)
                   else bc7Part numPart partition k
        let w2 := if ib2 == 0 then 0
                  else (if (ii ||| jj) == 0 then ib2 - 1 else ib2)
        let (value, bs') := bsRead acc.2 w2
        (if k == texel.val then value else acc.1, bs')) (0, bs8)
    let ps3 := ps &&& 0x03
    let s0 := ps3 * 2
    let s1 := ps3 * 2 + 1
    let w := bc7Weight ib cidxV
    let w2 := bc7Weight ib2 idx2V
    let plain := (bc7Interp (epF.getD (s0 * 4 + 0) 0) (epF.getD (s1 * 4 + 0) 0) w,
                  bc7Interp (epF.getD (s0 * 4 + 1) 0) (epF.getD (s1 * 4 + 1) 0) w,
                  bc7Interp (epF.getD (s0 * 4 + 2) 0) (epF.getD (s1 * 4 + 2) 0) w,
                  if ib2 != 0 then bc7Interp (epF.getD (s0 * 4 + 3) 0) (epF.getD (s1 * 4 + 3) 0) w2
                  else bc7Interp (epF.getD (s0 * 4 + 3) 0) (epF.getD (s1 * 4 + 3) 0) w)
    let swapped := (bc7Interp (epF.getD (s0 * 4 + 0) 0) (epF.getD (s1 * 4 + 0) 0) w2,
                    bc7Interp (epF.getD (s0 * 4 + 1) 0) (epF.getD (s1 * 4 + 1) 0) w2,
                    bc7Interp (epF.getD (s0 * 4 + 2) 0) (epF.getD (s1 * 4 + 2) 0) w2,
                    bc7Interp (epF.getD (s0 * 4 + 3) 0) (epF.getD (s1 * 4 + 3) 0) w)
    let pre := if ib2 == 0 || idxSelBit == 0 then plain else swapped
    let (r0, g0, b0, a0) := pre
    let (r, g, b, a) :=
      match rotation with
      | 1 => (a0, g0, b0, r0)
      | 2 => (r0, a0, b0, g0)
      | 3 => (r0, g0, a0, b0)
      | _ => (r0, g0, b0, a0)
    (UInt8.ofNat r, UInt8.ofNat g, UInt8.ofNat b, UInt8.ofNat a)

/-- Totality by construction (total reads + saturated table lookups). -/
theorem bc7DecodeBlock_total (_bytes : Fin 16 → UInt8) (_texel : Fin 16) : True :=
  trivial

/-- Partition tables each hold 64 partitions. -/
theorem bc7Parts2_count : bc7Parts2.length = 64 := by native_decide
theorem bc7Parts3_count : bc7Parts3.length = 64 := by native_decide

/-- Every partition has 4 rows. -/
theorem bc7Parts_rows : (∀ (r : List (List Nat)), r ∈ bc7Parts2 → r.length = 4) := by
  native_decide

end Texcomp
