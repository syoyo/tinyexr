/-
  TinyEXR - Lean 4 model of the DEFLATE payload subset used by the ZIP
  wrapper gates: stored blocks and fixed-Huffman blocks (the two canonical
  forms that do not require a dynamic code-length table).

  Dynamic Huffman remains a documented boundary. The decoder is checked
  bit-exactly against `exr_inflate_zlib` by `make deflate-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Zip

namespace Exr

set_option linter.unusedVariables false

/-- Bit cursor: bytes are consumed LSB-first, as DEFLATE requires. -/
structure BitR where
  data : List UInt8
  pos : Nat       -- byte index
  bit : Nat       -- bit index within the byte (0..7)
  deriving Repr

def bitAt (r : BitR) : Option Nat :=
  if r.pos < r.data.length ∧ r.bit < 8 then
    some (((r.data.getD r.pos 0).toNat >>> r.bit) &&& 1)
  else none

def readBit (r : BitR) : Option (Nat × BitR) := do
  let b ← bitAt r
  if r.bit == 7 then some (b, { r with pos := r.pos + 1, bit := 0 })
  else some (b, { r with bit := r.bit + 1 })

def alignByte (r : BitR) : BitR :=
  if r.bit == 0 then r else { r with pos := r.pos + 1, bit := 0 }

def readBitsAux : Nat → Nat → Nat → BitR → Option (Nat × BitR)
  | 0, val, _, r => some (val, r)
  | n + 1, val, shift, r => do
      let (b, r') ← readBit r
      readBitsAux n (val + (b <<< shift)) (shift + 1) r'

def readBitsLE (r : BitR) (n : Nat) : Option (Nat × BitR) := readBitsAux n 0 0 r

/-- Canonical Huffman code for a symbol (MSB-first code value). -/
def huffNextCode (lens : List Nat) (l : Nat) : Nat :=
  (List.range (l - 1)).foldl (fun acc k => (acc + (lens.filter (fun x => x == k + 1)).length) * 2) 0

def huffCode (lens : List Nat) (sym : Nat) : Nat :=
  let l := lens.getD sym 0
  if l == 0 then 0 else
  huffNextCode lens l + ((lens.take sym).filter (fun x => x == l)).length

def maxCodeLen (lens : List Nat) : Nat := lens.foldl Nat.max 0

/-- Decode one symbol: accumulate bits MSB-first and match the canonical code. -/
def decodeSym (lens : List Nat) (r0 : BitR) : Option (Nat × BitR) :=
  let maxLen := maxCodeLen lens
  let syms := List.range lens.length
  let rec go (len : Nat) (code : Nat) (r : BitR) : Option (Nat × BitR) :=
    if len > maxLen then none else do
      let (b, r') ← readBit r
      let code' := code * 2 + b
      match syms.find? (fun s => lens.getD s 0 == len && huffCode lens s == code') with
      | some s => some (s, r')
      | none => go (len + 1) code' r'
  termination_by maxLen + 1 - len
  go 1 0 r0

/-- Fixed literal/length and distance code lengths. -/
def fixedLitLen : List Nat :=
  (List.range 288).map (fun s =>
    if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8)

def fixedDistLen : List Nat := List.replicate 32 5

def lenBase : List Nat :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27,
   31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def lenExtra : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2,
   2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

def distBase : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129,
   193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
   8193, 12289, 16385, 24577]

def distExtra : List Nat :=
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6,
   6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

theorem len_tables_length : lenBase.length = 29 ∧ lenExtra.length = 29 := by decide
theorem dist_tables_length : distBase.length = 30 ∧ distExtra.length = 30 := by decide

/-- LZ77 overlap copy: the source window includes bytes emitted so far. -/
def lzCopy (out : List UInt8) (dist n : Nat) : Option (List UInt8) :=
  if dist == 0 || dist > out.length then none
  else
    let rec go : Nat → Nat → List UInt8 → List UInt8
      | 0, _, acc => acc
      | k + 1, src, acc =>
          let v := (out ++ acc).getD src 0
          go k (src + 1) (acc ++ [v])
    some (go n (out.length - dist) [])

/-- One DEFLATE block: returns the produced bytes and the cursor after it. -/
def decodeBlock (r : BitR) (out : List UInt8) : Option (List Nat × BitR × List UInt8) := do
  let (final, r1) ← readBit r
  let (btype, r2) ← readBitsLE r1 2
  if btype == 0 then
    let r3 := alignByte r2
    let (len, r4) ← readBitsLE r3 16
    let (nlen, r5) ← readBitsLE r4 16
    if nlen != (len ^^^ 0xffff) || r5.pos + len > r5.data.length then none
    let bytes := (List.range len).map (fun i => r5.data.getD (r5.pos + i) 0)
    some ([final, btype], { r5 with pos := r5.pos + len }, out ++ bytes)
  else if btype == 1 then
    let rec syms : Nat → BitR → List UInt8 → Option (List UInt8 × BitR)
      | 0, _, _ => none
      | fuel + 1, r, o => do
      let (sym, r') ← decodeSym fixedLitLen r
      if sym < 256 then syms fuel r' (o ++ [UInt8.ofNat sym])
      else if sym == 256 then some (o, r')
      else if sym <= 285 then
        let li := sym - 257
        let (ex, r'') ← readBitsLE r' (lenExtra.getD li 0)
        let L := lenBase.getD li 0 + ex
        let (ds, r3) ← decodeSym fixedDistLen r''
        if ds >= 30 then none else do
          let (dex, r4) ← readBitsLE r3 (distExtra.getD ds 0)
          let D := distBase.getD ds 0 + dex
          let more ← lzCopy o D L
          syms fuel r4 (o ++ more)
      else none
    let (o', r') ← syms (r2.data.length * 8 + 1) r2 out
    some ([final, btype], r', o')
  else none

/-- Decode the DEFLATE payload (after the two-byte zlib header). -/
def inflateAux : Nat → BitR → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | n + 1, r, out => do
      let (hdr, r', out') ← decodeBlock r out
      if hdr.getD 0 0 == 1 then some out'
      else inflateAux n r' out'

def inflate (payload : List UInt8) : Option (List UInt8) :=
  inflateAux (payload.length + 1) ⟨payload, 0, 0⟩ []

/-- Decode a complete zlib stream: header, payload and Adler-32 trailer. -/
def decodeZlib (data : List UInt8) : Option (List UInt8) :=
  if data.length < 6 then none else
  let hdr := (data.getD 0 0, data.getD 1 0)
  if !Zip.zlibHeaderValid hdr then none else
  let payload := data.drop 2 |>.take (data.length - 6)
  let trailer := data.drop (data.length - 4)
  match inflate payload with
  | none => none
  | some out =>
      let want : Nat := ((trailer.getD 0 0).toNat <<< 24) |||
        ((trailer.getD 1 0).toNat <<< 16) |||
        ((trailer.getD 2 0).toNat <<< 8) ||| (trailer.getD 3 0).toNat
      if Zip.adler32 out == UInt32.ofNat want then some out else none

end Exr
