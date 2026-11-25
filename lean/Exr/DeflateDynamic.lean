/-
  TinyEXR - DEFLATE dynamic-Huffman block decoder model.

  Extends `Exr.Deflate` with BTYPE=2 blocks: HLIT/HDIST/HCLEN header, the
  code-length code (with repeat symbols 16/17/18), canonical Huffman
  construction for the literal/length and distance alphabets, and the
  shared LZ77 symbol loop. Totality is by explicit fuel and Option returns;
  all hostile-input arithmetic is Nat with bounds checked before indexing.

  The decoder is checked bit-exactly against `exr_inflate_zlib` over the
  dynamic blocks emitted by `src/exr_deflate.c` (`make deflate-diff`).
  Encoder-side LZ77 choices remain a documented boundary.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Deflate

namespace Exr

set_option linter.unusedVariables false

def clAlphabetOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the three dynamic header counts. -/
def readDynCounts (r : BitR) : Option (Nat × Nat × Nat × BitR) := do
  let (hlit, r1) ← readBitsLE r 5
  let (hdist, r2) ← readBitsLE r1 5
  let (hclen, r3) ← readBitsLE r2 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  let ncl := hclen + 4
  if nlit > 286 || ndist > 32 || ncl > 19 then none
  else some (nlit, ndist, ncl, r3)

/-- Read HCLEN 3-bit code lengths in the DEFLATE order. -/
def readClLens : Nat → BitR → List Nat → Option (List Nat × BitR)
  | 0, r, acc => some (acc, r)
  | n + 1, r, acc => do
      let (v, r') ← readBitsLE r 3
      readClLens n r' (acc ++ [v])

/-- Expand one run symbol from the code-length alphabet. -/
def clRun (sym : Nat) (clLens : List Nat) (r : BitR) (prev : Nat) :
    Option (List Nat × BitR) :=
  if sym <= 15 then some ([sym], r)
  else if sym == 16 then do
    if prev == 0 then none  -- no previous length to repeat (consumed as error)
    let (x, r') ← readBitsLE r 2
    some (List.replicate (x + 3) prev, r')
  else if sym == 17 then do
    let (x, r') ← readBitsLE r 3
    some (List.replicate (x + 3) 0, r')
  else if sym == 18 then do
    let (x, r') ← readBitsLE r 7
    some (List.replicate (x + 11) 0, r')
  else none

/-- Decode the literal/length and distance code lengths. -/
def readDynLens (nlit ndist : Nat) (clLens : List Nat) : Nat → BitR → Nat → List Nat
    → Option (List Nat × BitR)
  | 0, r, _, acc => some (acc, r)
  | fuel + 1, r, prev, acc => do
      if acc.length >= nlit + ndist then some (acc, r)
      else do
        let (sym, r') ← decodeSym clLens r
        let (runs, r'') ← clRun sym clLens r' (acc.getD (acc.length - 1) 0)
        readDynLens nlit ndist clLens fuel r'' (acc.getD (acc.length + runs.length - 1) 0)
          (acc ++ runs)

/-- Read the dynamic tables; result is litlen/distance code-length lists. -/
def readDynamicTables (r : BitR) : Option (List Nat × List Nat × BitR) := do
  let (nlit, ndist, ncl, r1) ← readDynCounts r
  let (clRaw, r2) ← readClLens ncl r1 []
  let clLens : List Nat :=
    (List.range 19).map (fun i => clRaw.getD (clAlphabetOrder.findIdx? (fun x => x == i) |>.getD 0) 0)
  let (allLens, r3) ← readDynLens nlit ndist clLens (r2.data.length * 8 + 1) r2 0 []
  if allLens.length != nlit + ndist then none
  else
    let lit := allLens.take nlit
    let dist := allLens.drop nlit
    if lit.getD 256 0 == 0 then none else some (lit, dist, r3)

/-- Shared LZ77 symbol loop over arbitrary Huffman tables. -/
def decodeSyms (litLens distLens : List Nat) : Nat → BitR → List UInt8 → Option (List UInt8 × BitR)
  | 0, _, _ => none
  | fuel + 1, r, o => do
      let (sym, r') ← decodeSym litLens r
      if sym < 256 then decodeSyms litLens distLens fuel r' (o ++ [UInt8.ofNat sym])
      else if sym == 256 then some (o, r')
      else if sym <= 285 then do
        let li := sym - 257
        if li >= lenBase.length then none
        let (ex, r'') ← readBitsLE r' (lenExtra.getD li 0)
        let L := lenBase.getD li 0 + ex
        let (ds, r3) ← decodeSym distLens r''
        if ds >= distBase.length then none else do
          let (dex, r4) ← readBitsLE r3 (distExtra.getD ds 0)
          let D := distBase.getD ds 0 + dex
          let more ← lzCopy o D L
          decodeSyms litLens distLens fuel r4 (o ++ more)
      else none

/-- One dynamic block (after BFINAL/BTYPE have been consumed). -/
def decodeDynamicBlock (r : BitR) (out : List UInt8) : Option (List UInt8 × BitR) := do
  let (lit, dist, r') ← readDynamicTables r
  decodeSyms lit dist (r'.data.length * 8 + 1) r' out

/-- Full zlib decode including BTYPE=2. -/
def inflateDynamicAux : Nat → BitR → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | n + 1, r, out => do
      let (final, r1) ← readBit r
      let (btype, r2) ← readBitsLE r1 2
      if btype == 0 || btype == 1 then do
        let (_, r', out') ← decodeBlock r out
        if final == 1 then some out' else inflateDynamicAux n r' out'
      else if btype == 2 then do
        let (out', r') ← decodeDynamicBlock r2 out
        if final == 1 then some out' else inflateDynamicAux n r' out'
      else none

def inflateDynamic (payload : List UInt8) : Option (List UInt8) :=
  inflateDynamicAux (payload.length + 1) ⟨payload, 0, 0⟩ []

def decodeZlibDynamic (data : List UInt8) : Option (List UInt8) :=
  if data.length < 6 then none else
  let hdr := (data.getD 0 0, data.getD 1 0)
  if !Zip.zlibHeaderValid hdr then none else
  let payload := data.drop 2 |>.take (data.length - 6)
  let trailer := data.drop (data.length - 4)
  match inflateDynamic payload with
  | none => none
  | some out =>
      let want : Nat := ((trailer.getD 0 0).toNat <<< 24) |||
        ((trailer.getD 1 0).toNat <<< 16) |||
        ((trailer.getD 2 0).toNat <<< 8) ||| (trailer.getD 3 0).toNat
      if Zip.adler32 out == UInt32.ofNat want then some out else none

theorem clAlphabetOrder_length : clAlphabetOrder.length = 19 := by decide
theorem clAlphabetOrder_nodup : clAlphabetOrder.Nodup := by decide

end Exr
