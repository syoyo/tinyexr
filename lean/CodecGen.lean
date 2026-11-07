/-
  TinyEXR - `codecgen`: emits codec test vectors for the differential harness
  (`test/v3/codec_diff.c` + `test/v3/codec_diff.py`).

  File format (little endian):

    u32 magic 'TEXV' (0x56584554)
    u32 recordCount
    per record:
      u8  kind       (0 = PXR24 UINT, 1 = PXR24 HALF, 2 = PXR24 FLOAT,
                      3/4 = B44/B44A, 5 = RLE, 6 = ADLER32, 7 = ZIP,
                      8/9 = PIZ lifting, 10 = PIZ LUT, 11 = PIZ codes,
                      12 = PIZ lengths, 13 = PIZ payload, 14 = mixed PXR24,
                      15/16 = full PIZ traversal, 17 = frequency-derived PIZ tables,
                      18 = Huffman packets, 19 = packet parser verdicts)
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
import Exr.Piz
import Exr.PizTraversal
import Exr.PizHeap
import Exr.PizHistogram
import Exr.PizTable
import Exr.PizPacket
import Exr.PizPacketEmit
import Exr.PizBlock
import Exr.PizReconstruct
import Exr.PizBitmap
import Exr.PizFrameEmit

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
  let dec := (List.ofFn (Exr.B44.quantized blk)).map Exr.B44.unt8
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

/-- ZIP intermediate stream plus its checksum; DEFLATE bytes remain external. -/
def zipRecord (vals : List UInt8) : Exr.Bytes :=
  let intermediate := Exr.Zip.preprocess vals
  let enc := intermediate ++ Exr.Zip.adler32Trailer intermediate
  u8 7 ++ u8 0 ++ u32le vals.length ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.length ++ ByteArray.mk enc.toArray ++
    u32le vals.length ++ ByteArray.mk vals.toArray

def halfBytes (vals : List UInt16) : Exr.Bytes :=
  ByteArray.mk (vals.flatMap (fun (v : UInt16) => [v.toUInt8, (v >>> 8).toUInt8])).toArray

/-- PIZ lifting cell and pair, expected decode from the original samples. -/
def pizWaveRecord (small : Bool) (vals : List UInt32) : Exr.Bytes :=
  let a := (vals.getD 0 0).toUInt16
  let b := (vals.getD 1 0).toUInt16
  let c := (vals.getD 2 0).toUInt16
  let d := (vals.getD 3 0).toUInt16
  let enc := if small then Exr.Piz.wenc14 else Exr.Piz.wenc16
  let cell := Exr.Piz.encodeCell enc ((a, b), (c, d))
  let pair := enc a b
  let packed := halfBytes [cell.1.1, cell.1.2, cell.2.1, cell.2.2, pair.1, pair.2]
  let raw := halfBytes [a, b, c, d]
  u8 (if small then 8 else 9) ++ u8 0 ++ u32le 4 ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le packed.size ++ packed ++ u32le raw.size ++ raw

/-- PIZ's bitmap omits zero; rank zero is reserved even when absent in input. -/
def pizBitmap (vals : List UInt32) : List UInt8 :=
  (vals.foldl (fun (bm : Array UInt8) v =>
    let n := v.toNat
    if n = 0 then bm else bm.set! (n / 8) (bm[n / 8]! ||| (1 <<< UInt8.ofNat (n % 8))))
    (Array.replicate 8192 0)).toList

def pizLutRecord (vals : List UInt32) : Exr.Bytes :=
  let bitmap := pizBitmap vals
  let alphabet := Exr.Piz.alphabet bitmap
  let ranks := vals.map (fun v => UInt16.ofNat (Exr.Piz.forward alphabet v.toNat))
  let packed := ByteArray.mk bitmap.toArray ++ halfBytes ranks
  let raw := halfBytes (vals.map UInt32.toUInt16)
  u8 10 ++ u8 0 ++ u32le vals.length ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le packed.size ++ packed ++ u32le raw.size ++ raw

def pizCodeRecord (lengths : List Nat) : Exr.Bytes :=
  let packed := (Exr.Piz.canonicalTable lengths).foldl
    (fun acc v => acc ++ u64le (UInt64.ofNat v)) ByteArray.empty
  u8 11 ++ u8 0 ++ u32le lengths.length ++
    (lengths.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le packed.size ++ packed ++ u32le 0

def pizLengthRecord (lengths : List Nat) : Exr.Bytes :=
  let packed := Exr.Piz.Huffman.tableBytes lengths
  let decoded := match Exr.Piz.Table.readTable lengths.length (Exr.Piz.Bits.unpack packed) with
    | some (values, _) => values
    | none => []
  u8 12 ++ u8 0 ++ u32le lengths.length ++
    (lengths.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le packed.length ++ ByteArray.mk packed.toArray ++
    u32le decoded.length ++ ByteArray.mk (decoded.map UInt8.ofNat).toArray

/-- A supplied balanced codebook isolates symbol/RLE coding from the
frequency-heap code-length selection algorithm. The last symbol is RLE. -/
def pizPayloadRecord (symbols : List Nat) : Exr.Bytes :=
  let bits := Exr.Piz.Huffman.payloadBits (List.replicate 17 5) symbols 16
  let packed := Exr.Piz.Huffman.packBits bits
  let decoded := (Exr.Piz.Entropy.decode (List.replicate 17 5) 16 symbols.length bits).getD []
  let raw := halfBytes (decoded.map UInt16.ofNat)
  u8 13 ++ u8 0 ++ u32le symbols.length ++
    (symbols.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le (packed.length + 4) ++ u32le bits.length ++ ByteArray.mk packed.toArray ++
    u32le raw.size ++ raw

/-- Three mixed-type channels over three rows at (-4,-2), with x/y
subsampling. Each channel row restarts its own delta accumulator. -/
def pxrMixedRecord (vals : List UInt32) : Exr.Bytes :=
  let groups : List (Nat × Nat) := [(1,6), (2,12), (0,4), (2,12), (0,4), (1,6), (2,12), (0,4)]
  let (_, input, enc, dec) := groups.foldl
    (fun (state : Nat × List UInt32 × Exr.Bytes × Exr.Bytes) (g : Nat × Nat) =>
      let (offset, input, enc, dec) := state
      let xs := ((vals.drop offset).take g.2).map (fun v => if g.1 = 1 then v &&& 65535 else v)
      let planes := match g.1 with
        | 0 => planeBytes xs 4
        | 1 => planeBytes xs 2
        | _ => planeBytes (xs.map Exr.Pxr24.float24) 3
      let raw := match g.1 with
        | 0 => decodedBytes xs 4
        | 1 => decodedBytes xs 2
        | _ => decodedBytes (xs.map (fun v => Exr.Pxr24.float24 v <<< 8)) 4
      (offset + g.2, input ++ xs, enc ++ planes, dec ++ raw))
    (0, [], ByteArray.empty, ByteArray.empty)
  u8 14 ++ u8 0 ++ u32le input.length ++
    (input.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.size ++ enc ++ u32le dec.size ++ dec

/-- Full multilevel PIZ traversal, including lane strides and prefix/tail
canaries. Every model access is covered by Traversal.allocation_bounds. -/
def pizTraversalRecord (small : Bool) (w h lanes : Nat) (vals : List UInt32) : Exr.Bytes :=
  let original := (vals.map UInt32.toUInt16).toArray
  let encoded := (List.range lanes).foldl (fun a lane =>
    Exr.Piz.Traversal.run false small 3 w h lanes lane a) original
  let decoded := (List.range lanes).foldl (fun a lane =>
    Exr.Piz.Traversal.run true small 3 w h lanes lane a) encoded
  let metadata := [w, h, lanes, 3]
  let enc := halfBytes encoded.toList
  let dec := halfBytes decoded.toList
  u8 (if small then 15 else 16) ++ u8 0 ++ u32le (vals.length + 4) ++
    (metadata.map u32le).foldl (· ++ ·) ByteArray.empty ++
    (vals.map (fun v => u32le v.toNat)).foldl (· ++ ·) ByteArray.empty ++
    u32le enc.size ++ enc ++ u32le dec.size ++ dec

/-- Frequency-derived Huffman code lengths and canonical words, including
C's synthetic run marker and its exact strict-comparison tie behavior. -/
def pizFrequencyRecord (frequencies : List Nat) : Exr.Bytes :=
  let (packed, decoded) := match Exr.Piz.Frequency.lengths frequencies with
    | none => (ByteArray.empty, ByteArray.empty)
    | some lengths =>
      ((Exr.Piz.canonicalTable lengths).foldl
        (fun acc word => acc ++ u64le (UInt64.ofNat word)) ByteArray.empty,
        ByteArray.mk (lengths.map UInt8.ofNat).toArray)
  u8 17 ++ u8 0 ++ u32le frequencies.length ++
    (frequencies.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le packed.size ++ packed ++ u32le decoded.size ++ decoded

/-- Full frequency-derived Huffman packet, including the real 20-byte
header, sliced length table, payload bits and the composed Lean parser. -/
def pizPacketBytes (symbols : List Nat) : Exr.Bytes := if symbols.isEmpty then ByteArray.empty else Id.run do
    let largest := symbols.foldl max 0
    let first := symbols.foldl min 65536
    let marker := largest+1
    let frequencies := Exr.Piz.Frequency.countSymbols symbols marker
    let some lengths := Exr.Piz.Frequency.lengths frequencies.toList | return ByteArray.empty
    return Exr.Piz.Packet.emit first marker (lengths.drop first) symbols

def pizPacketRecord (symbols : List Nat) : Exr.Bytes :=
  let encoded := pizPacketBytes symbols
  let decoded := match Exr.Piz.Packet.parse encoded symbols.length with
    | some packet => packet.samples
    | none => []
  let raw := halfBytes (decoded.map UInt16.ofNat)
  u8 18 ++ u8 0 ++ u32le symbols.length ++
    (symbols.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le encoded.size ++ encoded ++ u32le raw.size ++ raw

def setWordAt (bytes : Exr.Bytes) (offset value : Nat) : Exr.Bytes :=
  (List.range 4).foldl (fun b i => b.set! (offset+i) (UInt8.ofNat (value / 2^(8*i)))) bytes

/-- Malformed and deliberately lenient packet cases compare the composed
Lean parser's verdict and samples directly with C's Huffman decoder. -/
def pizPacketParseRecord (symbols : List Nat) (bytes : Exr.Bytes) : Exr.Bytes :=
  let decoded := match Exr.Piz.Packet.parse bytes symbols.length with
    | some packet => packet.samples
    | none => []
  let raw := halfBytes (decoded.map UInt16.ofNat)
  u8 19 ++ u8 0 ++ u32le symbols.length ++
    (symbols.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le bytes.size ++ bytes ++ u32le raw.size ++ raw

/-- Entire PIZ block: model bitmap, planar gather, forward wavelets and
frequency-derived Huffman framing, decoded by both the model and C. -/
def pizBlockRecord (ctx : Exr.Piz.Layout.Context) (raw : List UInt16) : Exr.Bytes :=
  let bitmap := Exr.Piz.Bitmap.make raw
  let transformed := Exr.Piz.Block.coefficients ctx bitmap.toList raw
  let packet := pizPacketBytes (transformed.toList.map UInt16.toNat)
  let encoded := Exr.Piz.Block.emitFraming bitmap packet
  let parsed := Exr.Piz.Block.decodeCompressed ctx encoded
  let decoded := parsed.getD ByteArray.empty
  let dispatched := Exr.Piz.Block.decode ctx encoded
  let fields := [ctx.x.toInt32.toUInt32.toNat,ctx.y.toInt32.toUInt32.toNat,ctx.width,ctx.lines,
    ctx.channels.length] ++ ctx.channels.flatMap (fun c =>
      [match c.pixelType with | .uint => 0 | .half => 1 | .float => 2,c.xSampling,c.ySampling]) ++
    [if parsed.isSome then 1 else 0,if dispatched.isSome then 1 else 0] ++ raw.map UInt16.toNat
  u8 20 ++ u8 0 ++ u32le fields.length ++
    (fields.map u32le).foldl (· ++ ·) ByteArray.empty ++
    u32le encoded.size ++ encoded ++ u32le decoded.size ++ decoded

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
  -- Compression and raw-fallback paths, odd byte counts and long predictors.
  let zipCases := rleEdge ++ [(List.range 5553).map UInt8.ofNat, List.replicate 8193 0]
  let body := zipCases.foldl (fun acc xs => acc ++ zipRecord xs) body
  let pxrCases : List (List UInt32) :=
    [List.replicate 257 0, List.replicate 257 0x3c00,
     (List.range 513).map UInt32.ofNat]
  let body := ([0, 1, 2] : List Nat).foldl (fun acc kind =>
    pxrCases.foldl (fun acc xs => acc ++ pxrRecord kind xs) acc) body
  let waveEdges : List (List UInt32) :=
    [[0,0,0,0], [0,16383,16383,0], [16383,0,0,16383],
     [1,2,3,4], [16383,16383,16382,16381]]
  let wideEdges : List (List UInt32) :=
    [[0,65535,32768,32767], [65535,0,0,65535], [65535,65535,65535,65535]]
  let body := waveEdges.foldl (fun acc xs => acc ++ pizWaveRecord true xs) body
  let body := (waveEdges ++ wideEdges).foldl (fun acc xs => acc ++ pizWaveRecord false xs) body
  let rec genP (k : Nat) (r : Rng) (acc : Exr.Bytes) : Exr.Bytes :=
    match k with
    | 0 => acc
    | k + 1 =>
      let (small, r) := genValues r 4 14
      let (wide, r) := genValues r 4 16
      genP k r (acc ++ pizWaveRecord true small ++ pizWaveRecord false wide)
  let body := genP 32 r0 body
  let (lutRandom, _) := genValues r0 257 16
  let lutCases : List (List UInt32) :=
    [[], [0], [65535], [0, 1, 7, 8, 255, 256, 32768, 65535, 8, 0],
     List.replicate 128 0, lutRandom, (List.range 512).map UInt32.ofNat]
  let body := lutCases.foldl (fun acc xs => acc ++ pizLutRecord xs) body
  let codeCases : List (List Nat) :=
    [[1, 1], [1, 2, 3, 3], [0, 1, 0, 2, 3, 0, 3], [58], [58, 58],
     List.replicate 16 4, List.replicate 256 8, [0, 0, 0],
     [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,20]]
  let body := codeCases.foldl (fun acc xs => acc ++ pizCodeRecord xs) body
  let lengthCases := codeCases ++
    [List.replicate 2 0 ++ [1], List.replicate 5 0 ++ [1],
     List.replicate 6 0 ++ [1], List.replicate 261 0 ++ [1],
     List.replicate 262 0 ++ [1], List.replicate 523 0 ++ [1]]
  let body := lengthCases.foldl (fun acc xs => acc ++ pizLengthRecord xs) body
  let (randomSymbols, _) := genValues r0 513 4
  let payloadCases : List (List Nat) :=
    [[0], [15], [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
     List.replicate 4 7, List.replicate 5 7, List.replicate 255 7,
     List.replicate 256 7, List.replicate 257 7, List.replicate 1025 0,
     [1] ++ List.replicate 300 2 ++ [3] ++ List.replicate 5 4,
     randomSymbols.map UInt32.toNat]
  let body := payloadCases.foldl (fun acc xs => acc ++ pizPayloadRecord xs) body
  let (mixedValues, _) := genValues r0 60 32
  let body := body ++ pxrMixedRecord mixedValues
  let geometries : List (Nat × Nat) :=
    [(0,0), (1,9), (9,1), (2,3), (3,2), (3,3), (5,7), (7,5), (14,19), (17,33), (32,32)]
  let body := geometries.foldl (fun acc wh =>
    ([1,2] : List Nat).foldl (fun acc lanes =>
      let (small, _) := genValues r0 (wh.1 * wh.2 * lanes + 8) 14
      let (wide, _) := genValues r0 (wh.1 * wh.2 * lanes + 8) 16
      acc ++ pizTraversalRecord true wh.1 wh.2 lanes small ++
        pizTraversalRecord false wh.1 wh.2 lanes wide) acc) body
  let (randomFrequencies, _) := genValues r0 512 8
  let frequencyCases : List (List Nat) :=
    [[], [0,0,0], [1], [5,0,0], [0,0,7], [1,1], [1,1,1,1,1,1,1],
     [1,2,3,5,8,13,21,34,55,89,144,233,377,610],
     List.replicate 128 1, List.replicate 256 5,
     randomFrequencies.map UInt32.toNat,
     List.replicate 1024 0 ++ [1]]
  let body := frequencyCases.foldl (fun acc fs => acc ++ pizFrequencyRecord fs) body
  let (packetRandom, _) := genValues r0 1025 8
  let packetCases : List (List Nat) :=
    [[], [0], [7], [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
     List.replicate 1025 7, [5,7,15,5,7,15,5],
     (List.range 128), packetRandom.map UInt32.toNat,
     List.replicate 300 0 ++ List.replicate 128 1 ++ [2,3,4] ++ List.replicate 256 5]
  let body := packetCases.foldl (fun acc symbols => acc ++ pizPacketRecord symbols) body
  let parseSymbols := (List.range 16) ++ List.replicate 300 7 ++ [1,2,3]
  let parsePacket := pizPacketBytes parseSymbols
  let parseMarker := parseSymbols.foldl max 0 + 1
  let parseCases : List (List Nat × Exr.Bytes) :=
    [(parseSymbols, parsePacket.extract 0 (parsePacket.size-1)),
     (parseSymbols, setWordAt parsePacket 0 (parseMarker+1)),
     (parseSymbols, setWordAt parsePacket 12 0x80000000),
     (parseSymbols.take (parseSymbols.length-1), parsePacket),
     (parseSymbols ++ [0], parsePacket),
     (parseSymbols, setWordAt parsePacket 8 0xffffffff),
     (parseSymbols, setWordAt parsePacket 16 0x12345678),
     (parseSymbols, parsePacket.push 0xff),
     ([0,1,0,0], pizPacketBytes [0,1,0]),
     ((List.range 128) ++ [0], pizPacketBytes (List.range 128)),
     ((List.range 128).take 127, pizPacketBytes (List.range 128))]
  let body := parseCases.foldl (fun acc p => acc ++ pizPacketParseRecord p.1 p.2) body
  let blockContexts : List Exr.Piz.Layout.Context :=
    [⟨0,0,9,7,[⟨.half,1,1⟩]⟩,
     ⟨0,0,17,9,[⟨.float,1,1⟩]⟩,
     ⟨-4,-2,12,3,[⟨.half,2,2⟩,⟨.float,1,1⟩,⟨.uint,3,1⟩]⟩,
     ⟨-1,-1,1,3,[⟨.half,2,1⟩,⟨.half,1,2⟩]⟩,
     ⟨0,0,14,19,[⟨.uint,1,1⟩]⟩,
     ⟨-1,-1,1,1,[⟨.half,2,2⟩]⟩]
  let body := blockContexts.foldl (fun acc ctx =>
    let (words,_) := genValues r0 (Exr.Piz.Layout.wordCount ctx.planes) 4
    acc ++ pizBlockRecord ctx (words.map (fun w => UInt16.ofNat w.toNat))) body
  let zeroContext : Exr.Piz.Layout.Context := ⟨0,0,31,32,[⟨.half,1,1⟩]⟩
  let body := body ++ pizBlockRecord zeroContext (List.replicate (31*32) 0)
  -- Once per default seed sweep, exercise the complete full-range PIZ
  -- path with an alphabet exceeding 2^14, rather than only isolated kernels.
  let wideBlocks : List (Exr.Piz.Layout.Context × List UInt16) :=
    if seed == 12345 then
      [(⟨0,0,129,129,[⟨.half,1,1⟩]⟩,(List.range (129*129)).map UInt16.ofNat)]
    else []
  let body := wideBlocks.foldl (fun acc p => acc ++ pizBlockRecord p.1 p.2) body
  -- magic + record count
  ByteArray.mk #[84, 69, 88, 86] ++
    u32le (120 + 120 + 2 * edgeBlocks.length + 60 + rleEdge.length + 12 + longA.length + zipCases.length + 3 * pxrCases.length +
      2 * waveEdges.length + wideEdges.length + 64 + lutCases.length + codeCases.length + lengthCases.length + payloadCases.length + 1 + 4 * geometries.length + frequencyCases.length + packetCases.length + parseCases.length + blockContexts.length + 1 + wideBlocks.length) ++ body

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
