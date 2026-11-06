/-
  TinyEXR - `codecgen`: emits codec test vectors for the differential harness
  (`test/v3/codec_diff.c` + `test/v3/codec_diff.py`).

  File format (little endian):

    u32 magic 'TEXV' (0x56584554)
    u32 recordCount
    per record:
      u8  kind       (0 = PXR24 UINT, 1 = PXR24 HALF, 2 = PXR24 FLOAT,
                      3 = B44 block)
      u8  reserved
      u32 count      (samples for PXR24; 16 for B44)
      count × u32 input values (raw half bits / u32 / float bits)
      u32 encodedLen
      encodedLen bytes (PXR24 plane bytes / B44 14-or-3 byte block)
      u32 decodedLen
      decodedLen bytes (expected canonical output)

  The generator uses a small xorshift PRNG so the corpus is reproducible from
  the seed.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.B44
import Exr.Rle
import Exr.Zip

namespace CodecGen

/-- xorshift64 PRNG state. -/
def next (s : UInt64) : UInt64 :=
  let x := s ^^^ (s <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

structure Rng where
  state : UInt64

def Rng.step (r : Rng) : UInt64 × Rng :=
  let s := next r.state
  (s, ⟨s⟩)

def Rng.bits (r : Rng) (n : Nat) : UInt64 × Rng :=
  let (s, r') := r.step
  (if n = 0 then 0 else s >>> (UInt64.ofNat (64 - n)), r')

/-- Build `n` values with the given bit width. -/
def genValues (r : Rng) (n bits : Nat) : List UInt32 × Rng :=
  let rec go (k : Nat) (r : Rng) (acc : List UInt32) : List UInt32 × Rng :=
    match k with
    | 0 => (acc.reverse, r)
    | k + 1 =>
      let (s, r') := r.step
      let v : UInt32 := UInt32.ofNat (if bits = 0 then 0
        else (s >>> (UInt64.ofNat (64 - bits))).toNat)
      go k r' (v :: acc)
  go n r []

def u32le (n : Nat) : Exr.Bytes :=
  Exr.putU32LE (UInt32.ofNat n) ByteArray.empty

def u8 (n : Nat) : Exr.Bytes := ByteArray.mk #[UInt8.ofNat n]

/-- The plane-major PXR24 row stream as bytes. -/
def planeBytes (vals : List UInt32) (bytes : Nat) : Exr.Bytes :=
  ByteArray.mk ((Exr.Pxr24.packPlanes vals bytes).map (fun p => p.toUInt8)).toArray

/-- Canonical decoded bytes (4 bytes/sample for UINT/FLOAT, 2 for HALF). -/
def decodedBytes (vals : List UInt32) (bytes : Nat) : Exr.Bytes :=
  ByteArray.mk ((vals.map (fun v =>
    (List.range bytes).map (fun i =>
      ((v >>> UInt32.ofNat (8 * i)).toUInt8)))).flatten.toArray)

/-- One PXR24 record. -/
def pxrRecord (kind : Nat) (vals : List UInt32) : Exr.Bytes :=
  let enc := match kind with
    | 0 => planeBytes vals 4
    | 1 => planeBytes vals 2
    | _ => planeBytes (vals.map Exr.Pxr24.float24) 3
  let dec := match kind with
    | 0 => decodedBytes vals 4
    | 1 => decodedBytes vals 2
    | _ => decodedBytes (vals.map (fun v => Exr.Pxr24.float24 v <<< 8)) 4
  u8 kind ++ u8 0 ++ u32le vals.length ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.size ++ enc ++ u32le dec.size ++ dec

/-- Encode a `UInt64` as 8 LE bytes (offsets etc. not needed here). -/
def u64le (n : UInt64) : Exr.Bytes :=
  Exr.putU64LE n ByteArray.empty

/-- One B44 block record: 16 half values in, packed bytes, decoded halves. -/
def b44Record (kind : Nat) (vals : List UInt32) : Exr.Bytes :=
  let blk : Fin 16 → UInt16 := fun i => UInt16.ofNat (vals.getD i.val 0).toNat
  let flat := kind == 4
  let enc := Exr.B44.packBlock blk flat
  let dec := Exr.B44.decodeBlock enc
  let decBytes := ByteArray.mk ((dec.map (fun (h : UInt16) =>
    ([h.toUInt8, (h >>> 8).toUInt8] : List UInt8))).flatten.toArray)
  u8 kind ++ u8 0 ++ u32le 16 ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.length ++ ByteArray.mk enc.toArray ++
    u32le decBytes.size ++ decBytes

/-- One RLE record (kind 5): raw row bytes (each as a u32), the Lean
    `rleCompress` output, and the raw bytes as the expected decode. -/
def rleRecord (vals : List UInt8) : Exr.Bytes :=
  let enc := Exr.Rle.rleCompress vals
  u8 5 ++ u8 0 ++ u32le vals.length ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.length ++ ByteArray.mk enc.toArray ++
    u32le vals.length ++ ByteArray.mk vals.toArray

/-- One ADLER32 record (kind 6): raw bytes, the Lean `adler32` value
    (little-endian) in the encoded slot, and the raw bytes decoded. -/
def adlerRecord (vals : List UInt8) : Exr.Bytes :=
  let v := Exr.Zip.adler32 vals
  u8 6 ++ u8 0 ++ u32le vals.length ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le 4 ++ ByteArray.mk ([v.toUInt8, ((v >>> 8)).toUInt8,
      ((v >>> 16)).toUInt8, ((v >>> 24)).toUInt8] : List UInt8).toArray ++
    u32le vals.length ++ ByteArray.mk vals.toArray

/-- Build the vector file for a seed. -/
def build (seed : UInt64) : Exr.Bytes :=
  let r0 : Rng := ⟨seed * 2654435761 + 1⟩
  let rec gen (k : Nat) (r : Rng) (acc : Exr.Bytes) : Exr.Bytes :=
    match k with
    | 0 => acc
    | k + 1 =>
      -- cycle through the kinds with varying lengths
      let kind := k % 3
      let count := 1 + (k * 7) % 40
      let bits := match kind with
        | 0 => 32
        | 1 => 16
        | _ => 32
      let (vals, r') := genValues r count bits
      gen k r' (acc ++ pxrRecord kind vals)
  let body := gen 120 r0 ByteArray.empty
  -- B44 blocks (B44 = kind 3, B44A = kind 4), 60 each
  let rec genB (kind : Nat) (n : Nat) (r : Rng) (acc : Exr.Bytes) : Exr.Bytes :=
    match n with
    | 0 => acc
    | n + 1 =>
      let (vals, r') := genValues r 16 16
      genB kind n r' (acc ++ b44Record kind vals)
  let body := genB 3 60 r0 body
  let body := genB 4 60 r0 body
  -- Edge-case blocks: constants (flat 3-byte form under B44A), near-constant,
  -- NaNs, infinities, signed zeros, subnormals and the half extremes.
  let edgeBlocks : List (List UInt32) :=
    [ List.replicate 16 0x3c00,       -- constant 1.0
      List.replicate 16 0x0000,       -- constant +0
      List.replicate 16 0x8000,       -- constant -0
      List.replicate 16 0x7c00,       -- constant +inf
      List.replicate 16 0xfc00,       -- constant -inf
      List.replicate 16 0x7e00,       -- constant NaN
      List.replicate 16 0x3bff,       -- constant just below 1.0
      List.replicate 16 0x0001,       -- constant smallest subnormal
      List.replicate 16 0x7bff,       -- constant max finite
      List.replicate 16 0xfbff,       -- constant min finite
      [0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00,
       0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c00, 0x3c01],
      [0x0000, 0x7c00, 0xfc00, 0x7e00, 0x8000, 0x0001, 0x7bff, 0xfbff,
       0x3c00, 0xbc00, 0x4000, 0xc000, 0x3555, 0x3555, 0x3555, 0x3755],
      [0x7fff, 0x7ffe, 0x7ffd, 0x7ffc, 0x7ffb, 0x7ffa, 0x7ff9, 0x7ff8,
       0x7ff7, 0x7ff6, 0x7ff5, 0x7ff4, 0x7ff3, 0x7ff2, 0x7ff1, 0x7ff0],
      [0x8001, 0x8002, 0x8003, 0x8004, 0x8005, 0x8006, 0x8007, 0x8008,
       0x8009, 0x800a, 0x800b, 0x800c, 0x800d, 0x800e, 0x800f, 0x8010] ]
  let rec genE (flat : Bool) (bs : List (List UInt32)) (acc : Exr.Bytes) : Exr.Bytes :=
    match bs with
    | [] => acc
    | b :: tl => genE flat tl (acc ++ b44Record (if flat then 4 else 3) b)
  let body := genE false edgeBlocks body
  let body := genE true edgeBlocks body
  -- RLE records: random byte streams plus edge run structures.
  let rec genR (k : Nat) (r : Rng) (acc : Exr.Bytes) : Exr.Bytes :=
    match k with
    | 0 => acc
    | k + 1 =>
      let len := 1 + (k * 13) % 200
      let (vals, r') := genValues r len 8
      genR k r' (acc ++ rleRecord (vals.map (fun v => v.toUInt8)))
  let body := genR 60 r0 body
  let rleEdge : List (List UInt8) :=
    [ List.replicate 4 0x41,                                  -- 4-run
      List.replicate 3 0x41,                                  -- 3-run (min run)
      List.replicate 128 0x41,                                -- 128-run (max run)
      List.replicate 129 0x41,                                -- 129-run (capped)
      List.replicate 300 0x00,                                -- long run
      List.replicate 2 0x05,                                  -- 2-run (stays literal)
      List.replicate 5 0x91,                                  -- 5-run
      ([0x10] : List UInt8) ++ List.replicate 4 0x42 ++ [0x20],
      [0x01, 0x02, 0x03, 0x04, 0x04, 0x04, 0x04, 0x06, 0x07],
      (List.range 128).map UInt8.ofNat,                       -- 128 distinct (max lit)
      (List.range 130).map UInt8.ofNat,                       -- 130 distinct (split lit)
      List.replicate 127 0x30 ++ [0x31] ++ List.replicate 127 0x30,
      ([0xAA] : List UInt8) ++ List.replicate 2 0xAA ++ [0xBB] ++ List.replicate 3 0xAA ++ [0xBB, 0xBB] ]
  let rec genRE (bs : List (List UInt8)) (acc : Exr.Bytes) : Exr.Bytes :=
    match bs with
    | [] => acc
    | b :: tl => genRE tl (acc ++ rleRecord b)
  let body := genRE rleEdge body
  -- ADLER32 records: random byte streams plus long streams that cross the
  -- C's deferred-modulo boundary (5552 bytes).
  let rec genA (k : Nat) (r : Rng) (acc : Exr.Bytes) : Exr.Bytes :=
    match k with
    | 0 => acc
    | k + 1 =>
      let len := 1 + (k * 17) % 200
      let (vals, r') := genValues r len 8
      genA k r' (acc ++ adlerRecord (vals.map (fun v => v.toUInt8)))
  let body := genA 12 r0 body
  let longA : List (List UInt8) :=
    [ (List.range 5552).map UInt8.ofNat,
      (List.range 5553).map UInt8.ofNat,
      (List.range 1105).map UInt8.ofNat,
      List.replicate 6000 0xFF,
      List.replicate 11107 0x00 ]
  let rec genLA (bs : List (List UInt8)) (acc : Exr.Bytes) : Exr.Bytes :=
    match bs with
    | [] => acc
    | b :: tl => genLA tl (acc ++ adlerRecord b)
  let body := genLA longA body
  -- magic + record count
  ByteArray.mk #[84, 69, 88, 86] ++
    u32le (120 + 120 + 2 * edgeBlocks.length + 60 + rleEdge.length + 12 + longA.length) ++ body

end CodecGen

def main (args : List String) : IO UInt32 := do
  match args with
  | [out, seed] =>
    let s : UInt64 := (seed.toList.foldl (fun acc c =>
      acc * 10 + (c.toNat - '0'.toNat)) 0).toUInt64
    let bytes := CodecGen.build s
    IO.FS.writeBinFile out bytes
    IO.println s!"wrote {out} ({bytes.size} bytes)"
    return 0
  | _ =>
    IO.eprintln "usage: codecgen <out.bin> <seed>"
    return 2
