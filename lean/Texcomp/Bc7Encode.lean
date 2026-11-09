/-
  TinyEXR - Lean 4 formalization of the BC7 encoder's pack path.

  Ports the deterministic half of `tools/texcomp/src/texcomp_bc7.c`:
  the block-mode tables, `tc_unquant`/`tc_quant`, endpoint
  decode/quantise, `tc_recon_color`, `tc_fill_palette` and
  `tc_pack_candidate` (including the anchor-selector endpoint swap and
  the separate-alpha plane). The partition/subset *search* heuristics
  (PCA/luma extremes, candidate scoring) are the remaining boundary; they
  only choose which candidate is packed, so this module covers the whole
  bit-layout side of the encoder.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- `bc7Weights4` (transcribed from `texcomp_bc7.c`). -/
def bc7Weights4 : List Nat :=
  [0, 4, 9, 13, 17, 21, 26, 30, 34, 38, 43, 47, 51, 55, 60, 64]
/-- `bc7Weights3` (transcribed from `texcomp_bc7.c`). -/
def bc7Weights3 : List Nat :=
  [0, 9, 18, 27, 37, 46, 55, 64]
/-- `bc7Weights2` (transcribed from `texcomp_bc7.c`). -/
def bc7Weights2 : List Nat :=
  [0, 21, 43, 64]
/-- `bc7IndexFromT` (transcribed from `texcomp_bc7.c`). -/
def bc7IndexFromT : List Nat :=
  [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3,
   4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7,
   7, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11,
   11, 11, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15,
   15]
/-- `bc7NumSubsets` (transcribed from `texcomp_bc7.c`). -/
def bc7NumSubsets : List Nat :=
  [3, 2, 3, 2, 1, 1, 1, 2]
/-- `bc7PartitionBits` (transcribed from `texcomp_bc7.c`). -/
def bc7PartitionBits : List Nat :=
  [4, 6, 6, 6, 0, 0, 0, 6]
/-- `bc7ColorIndexBits` (transcribed from `texcomp_bc7.c`). -/
def bc7ColorIndexBits : List Nat :=
  [3, 3, 2, 2, 2, 2, 4, 2]
/-- `bc7AlphaIndexBits` (transcribed from `texcomp_bc7.c`). -/
def bc7AlphaIndexBits : List Nat :=
  [0, 0, 0, 0, 3, 2, 4, 2]
/-- `bc7ColorPrecision` (transcribed from `texcomp_bc7.c`). -/
def bc7ColorPrecision : List Nat :=
  [4, 6, 5, 7, 5, 7, 7, 5]
/-- `bc7AlphaPrecision` (transcribed from `texcomp_bc7.c`). -/
def bc7AlphaPrecision : List Nat :=
  [0, 0, 0, 0, 6, 8, 7, 5]
/-- `bc7HasPbits` (transcribed from `texcomp_bc7.c`). -/
def bc7HasPbits : List Nat :=
  [1, 1, 0, 1, 0, 0, 1, 1]
/-- `bc7SharedPbits` (transcribed from `texcomp_bc7.c`). -/
def bc7SharedPbits : List Nat :=
  [0, 1, 0, 0, 0, 0, 0, 0]
/-- `bc7SepAlpha` (transcribed from `texcomp_bc7.c`). -/
def bc7SepAlpha : List Nat :=
  [0, 0, 0, 0, 1, 1, 0, 0]
/-- `bc7Partition1` (transcribed from `texcomp_bc7.c`). -/
def bc7Partition1 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- `bc7Partition2` (transcribed from `texcomp_bc7.c`). -/
def bc7Partition2 : List Nat :=
  [0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
   0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1,
   0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
   0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1,
   0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1,
   0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1,
   0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
   0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1,
   0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0,
   0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0,
   0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0,
   0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1,
   0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0,
   0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0,
   0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0,
   0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
   0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0,
   0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0,
   0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
   0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1,
   0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0,
   0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0,
   0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0,
   0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0,
   0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1,
   0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1,
   0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0,
   0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0,
   0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0,
   0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0,
   0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0,
   0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1,
   0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1,
   0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
   0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0,
   0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0,
   0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1,
   0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1,
   0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0,
   0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0,
   0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1,
   0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1,
   0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1,
   0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1,
   0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
   0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
   0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
   0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1]
/-- `bc7Partition3_0` (transcribed from `texcomp_bc7.c`). -/
def bc7Partition3_0 : List Nat :=
  [0, 0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 1, 2, 2, 2, 2]
/-- `bc7Anchor2` (transcribed from `texcomp_bc7.c`). -/
def bc7Anchor2 : List Nat :=
  [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
   15, 2, 8, 2, 2, 8, 8, 15, 2, 8, 2, 2, 8, 8, 2, 2,
   15, 15, 6, 8, 2, 8, 15, 15, 2, 8, 2, 2, 2, 15, 15, 6,
   6, 2, 6, 8, 15, 15, 2, 2, 15, 15, 15, 15, 15, 2, 2, 15]
/-- `bc7Anchor3_0` (transcribed from `texcomp_bc7.c`). -/
def bc7Anchor3_0 : List Nat :=
  [3, 15]

/-- `tc_unquant`: `bits`-bit value → 8-bit. -/
def bc7Unquant (q bits : Nat) : Nat :=
  if bits ≥ 8 then q &&& 0xFF
  else
    let maxv := (1 <<< bits) - 1
    ((q * 255 + maxv / 2) / maxv) &&& 0xFF

/-- `tc_quant`: 8-bit value → `bits`-bit. -/
def bc7Quant (v bits : Nat) : Nat :=
  let maxv := (1 <<< bits) - 1
  (v * maxv + 127) / 255

/-- `tc_partition_for`: the 16-entry subset map for this mode/partition. -/
def bc7PartitionFor (mode partition : Nat) : List Nat :=
  let ns := bc7NumSubsets.getD mode 1
  if ns == 1 then bc7Partition1
  else if ns == 2 then
    (List.range 16).map (fun i => bc7Partition2.getD ((partition &&& 63) * 16 + i) 0)
  else bc7Partition3_0

/-- `tc_anchor_for_subset`. -/
def bc7AnchorForSubset (mode partition subset : Nat) : Nat :=
  if subset == 0 then 0
  else if bc7NumSubsets.getD mode 1 == 3 then bc7Anchor3_0.getD (subset - 1) 0
  else bc7Anchor2.getD (partition &&& 63) 15

/-- `tc_weights_for_bits`. -/
def bc7WeightsForBits (bits : Nat) : List Nat :=
  if bits == 2 then bc7Weights2 else if bits == 3 then bc7Weights3 else bc7Weights4

/-- `tc_decode_endpoint`. -/
def bc7DecodeEndpoint (q p precision hasPbit : Nat) : Nat :=
  if hasPbit != 0 then bc7Unquant ((q <<< 1) ||| (p &&& 1)) (precision + 1)
  else bc7Unquant q precision

/-- `tc_quant_endpoint`: returns `(q, p)`. -/
def bc7QuantEndpoint (v precision hasPbit sharedPbit sharedP : Nat) : Nat × Nat :=
  if hasPbit != 0 then
    let u := bc7Quant v (precision + 1)
    if sharedPbit != 0 then (u >>> 1, sharedP &&& 1)
    else (u >>> 1, u &&& 1)
  else (bc7Quant v precision, 0)

/-- A BC7 candidate block (`tc_bc7_candidate`). -/
structure Bc7Candidate where
  (mode partition indexSelector rotation : Nat)
  (lo hi : List (List Nat))     -- [subset][component] (3 x 4)
  (pbits : List (List Nat))     -- [subset][0..1] (3 x 2)
  (selectors alphaSelectors : List Nat) -- 16 each
  deriving Repr, Inhabited

/-- `lo[subset][comp]` / `hi[subset][comp]` access. -/
def Bc7Candidate.loAt (c : Bc7Candidate) (s comp : Nat) : Nat :=
  (c.lo.getD s []).getD comp 0
def Bc7Candidate.hiAt (c : Bc7Candidate) (s comp : Nat) : Nat :=
  (c.hi.getD s []).getD comp 0
def Bc7Candidate.pAt (c : Bc7Candidate) (s k : Nat) : Nat :=
  (c.pbits.getD s []).getD k 0

/-- `tc_recon_color` for one subset and selector pair. -/
def bc7ReconColor (c : Bc7Candidate) (subset sel asel : Nat) : List Nat :=
  let cbits := bc7ColorIndexBits.getD c.mode 0 + c.indexSelector
  let abits := bc7AlphaIndexBits.getD c.mode 0 - c.indexSelector
  let cw := bc7WeightsForBits cbits
  let aw := bc7WeightsForBits (if abits != 0 then abits else cbits)
  let w := cw.getD sel 0
  let awv0 := aw.getD asel 0
  let colPrec := bc7ColorPrecision.getD c.mode 0
  let hasP := bc7HasPbits.getD c.mode 0
  let rgb := (List.range 3).map (fun comp =>
    let a := bc7DecodeEndpoint (c.loAt subset comp) (c.pAt subset 0) colPrec hasP
    let bb := bc7DecodeEndpoint (c.hiAt subset comp) (c.pAt subset 1) colPrec hasP
    (((64 - w) * a + w * bb + 32) >>> 6) &&& 0xFF)
  if c.mode < 4 then rgb ++ [255]
  else
    let sepA := bc7SepAlpha.getD c.mode 0
    let ap := if hasP != 0 && sepA == 0 then 1 else 0
    let alphaPrec := bc7AlphaPrecision.getD c.mode 0
    let a := bc7DecodeEndpoint (c.loAt subset 3) (c.pAt subset 0) alphaPrec ap
    let bb := bc7DecodeEndpoint (c.hiAt subset 3) (c.pAt subset 1) alphaPrec ap
    let awv := if sepA == 0 then w else awv0
    rgb ++ [(((64 - awv) * a + awv * bb + 32) >>> 6) &&& 0xFF]

/-- `tc_fill_palette`: per-subset reconstruction palette. -/
def bc7FillPalette (c : Bc7Candidate) : List (List (List Nat)) :=
  let maxSel := 1 <<< (bc7ColorIndexBits.getD c.mode 0 + c.indexSelector)
  let aBits := bc7AlphaIndexBits.getD c.mode 0
  let maxASel := if aBits > c.indexSelector then 1 <<< (aBits - c.indexSelector) else maxSel
  let n := max maxSel maxASel
  (List.range (bc7NumSubsets.getD c.mode 1)).map (fun subset =>
    (List.range n).map (fun sel =>
      let cs := if sel < maxSel then sel else maxSel - 1
      let as := if sel < maxASel then sel else maxASel - 1
      bc7ReconColor c subset cs as))

/-- Pack `val : nbits` at `bitpos` into a little-endian bit accumulator
  (mirrors `tc_set_bits`). -/
def bc7SetBits (acc : Nat) (bitpos val nbits : Nat) : Nat × Nat :=
  (acc ||| ((val &&& ((1 <<< nbits) - 1)) <<< bitpos), bitpos + nbits)

/-- `tc_pack_candidate`: candidate → 16 block bytes. -/
def bc7PackCandidate (c : Bc7Candidate) : List Nat :=
  let part := bc7PartitionFor c.mode c.partition
  let subsets := bc7NumSubsets.getD c.mode 1
  let cidxBits := bc7ColorIndexBits.getD c.mode 0 + c.indexSelector
  let ncolor := 1 <<< cidxBits
  let sepA := bc7SepAlpha.getD c.mode 0
  let sharedP := bc7SharedPbits.getD c.mode 0
  -- Per-subset endpoint/selector normalisation (the C code copies the
  -- candidate and mutates the copy, so mirror it as an accumulator).
  let step (st : Bc7Candidate × List Nat) (subset : Nat) : Bc7Candidate × List Nat :=
    let (cand, anchors) := st
    let anchor := bc7AnchorForSubset cand.mode cand.partition subset
    let flip := ((cand.selectors.getD anchor 0) &&& (ncolor >>> 1)) != 0
    let cand := if flip then
        { cand with
          selectors := (List.range 16).map (fun i =>
            if part.getD i 0 == subset then (ncolor - 1) - cand.selectors.getD i 0
            else cand.selectors.getD i 0)
          lo := (List.range 3).map (fun s =>
            (List.range 4).map (fun comp =>
              if s == subset && comp < (if sepA != 0 then 3 else 4) then cand.hiAt s comp
              else cand.loAt s comp))
          hi := (List.range 3).map (fun s =>
            (List.range 4).map (fun comp =>
              if s == subset && comp < (if sepA != 0 then 3 else 4) then cand.loAt s comp
              else cand.hiAt s comp))
          pbits := if sharedP != 0 then cand.pbits
            else (List.range 3).map (fun s =>
              if s == subset then [cand.pAt s 1, cand.pAt s 0] else cand.pbits.getD s []) }
      else cand
    -- Separate-alpha plane: invert when the alpha anchor selector's high bit is set.
    let aBits := bc7AlphaIndexBits.getD cand.mode 0
    let nalpha := 1 <<< (aBits - cand.indexSelector)
    let cand := if sepA != 0 && ((cand.alphaSelectors.getD anchor 0) &&& (nalpha >>> 1)) != 0 then
        { cand with
          alphaSelectors := (List.range 16).map (fun i =>
            if part.getD i 0 == subset then (nalpha - 1) - cand.alphaSelectors.getD i 0
            else cand.alphaSelectors.getD i 0)
          lo := (List.range 3).map (fun s =>
            (List.range 4).map (fun comp =>
              if s == subset && comp == 3 then cand.hiAt s 3 else cand.loAt s comp))
          hi := (List.range 3).map (fun s =>
            (List.range 4).map (fun comp =>
              if s == subset && comp == 3 then cand.loAt s 3 else cand.hiAt s comp)) }
      else cand
    (cand, anchors ++ [anchor])
  let (cand, anchors) := (List.range subsets).foldl step (c, [])
  -- Header.
  let (acc0, pos0) := bc7SetBits 0 0 (1 <<< c.mode) (c.mode + 1)
  let (acc1, pos1) := if cand.mode == 4 || cand.mode == 5 then
      bc7SetBits acc0 pos0 cand.rotation 2 else (acc0, pos0)
  let (acc2, pos2) := if cand.mode == 4 then bc7SetBits acc1 pos1 cand.indexSelector 1
      else (acc1, pos1)
  let (acc3, pos3) := if bc7PartitionBits.getD cand.mode 0 != 0 then
      bc7SetBits acc2 pos2 cand.partition (bc7PartitionBits.getD cand.mode 0)
      else (acc2, pos2)
  -- Endpoints: components 0..3 (modes >= 4 carry alpha), per subset.
  let emitComp (st : Nat × Nat) (comp : Nat) : Nat × Nat :=
    let (acc, pos) := st
    let prec := if comp == 3 then bc7AlphaPrecision.getD cand.mode 0
                else bc7ColorPrecision.getD cand.mode 0
    (List.range subsets).foldl (fun (p : Nat × Nat) subset =>
      let (a1, p1) := bc7SetBits p.1 p.2 (cand.loAt subset comp) prec
      bc7SetBits a1 p1 (cand.hiAt subset comp) prec) (acc, pos)
  let (acc4, pos4) := (List.range (if cand.mode ≥ 4 then 4 else 3)).foldl emitComp (acc3, pos3)
  -- pbits
  let (acc5, pos5) := if bc7HasPbits.getD cand.mode 0 != 0 then
      (List.range subsets).foldl (fun (p : Nat × Nat) subset =>
        let (a1, p1) := bc7SetBits p.1 p.2 (cand.pAt subset 0) 1
        if sharedP != 0 then (a1, p1)
        else bc7SetBits a1 p1 (cand.pAt subset 1) 1) (acc4, pos4)
    else (acc4, pos4)
  -- Primary index plane.
  let (acc6, pos6) := (List.range 16).foldl (fun (p : Nat × Nat) i =>
    let n0 := if cand.indexSelector != 0 then bc7AlphaIndexBits.getD cand.mode 0 - cand.indexSelector
              else bc7ColorIndexBits.getD cand.mode 0 + cand.indexSelector
    let n := if anchors.contains i then n0 - 1 else n0
    let v := if cand.indexSelector != 0 then cand.alphaSelectors.getD i 0
             else cand.selectors.getD i 0
    bc7SetBits p.1 p.2 v n) (acc5, pos5)
  -- Secondary (separate-alpha) plane.
  let (acc7, _) := if sepA != 0 then
      (List.range 16).foldl (fun (p : Nat × Nat) i =>
        let n0 := if cand.indexSelector != 0 then bc7ColorIndexBits.getD cand.mode 0 + cand.indexSelector
                  else bc7AlphaIndexBits.getD cand.mode 0 - cand.indexSelector
        let n := if anchors.contains i then n0 - 1 else n0
        let v := if cand.indexSelector != 0 then cand.selectors.getD i 0
                 else cand.alphaSelectors.getD i 0
        bc7SetBits p.1 p.2 v n) (acc6, pos6)
    else (acc6, pos6)
  (List.range 16).map (fun i => (acc7 >>> (8 * i)) &&& 0xFF)

/-- `tc_luma_u8`: fixed-point luma. -/
def bc7LumaU8 (r g b : Nat) : Nat := r * 38 + g * 76 + b * 14

/-- `tc_err4` with the default {1,1,1,1} channel weights (shared with the
  mode-6 encoder). -/
def bc7Err4 (a : List Nat) (r g b al : Nat) (hasAlpha : Bool) : Nat :=
  let dr := (Int.ofNat (a.getD 0 0)) - (Int.ofNat r)
  let dg := (Int.ofNat (a.getD 1 0)) - (Int.ofNat g)
  let db := (Int.ofNat (a.getD 2 0)) - (Int.ofNat b)
  let da := if hasAlpha then (Int.ofNat (a.getD 3 0)) - (Int.ofNat al) else 0
  (dr * dr + dg * dg + db * db + da * da).toNat

end Texcomp
