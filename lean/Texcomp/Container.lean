/-
  TinyEXR - Lean 4 formalization of the texcomp texture-container formats.

  The DDS (BC1/BC3/BC5/BC6H/BC7), KTX (ETC2/EAC) and ASTC file headers that
  `tools/texcomp` writes (`tc_dds_write_bc_memory`,
  `tc_ktx_write_compressed_memory`), modelled as fixed-width little-endian
  word layouts with size equations and a full parse/emit round trip.
  Block payloads are treated as opaque byte runs; their codecs are
  formalized separately.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Bytes

namespace Texcomp

open Exr

def ddsHeaderSize : Nat := 148
def ktxHeaderSize : Nat := 68
def ktxMagicSize : Nat := 12
def ktxEndianMarker : UInt32 := 0x04030201

/-! ### Little-endian word concatenation

`wordsConcat ws` is the byte image of a little-endian word list: it is
exactly what a chain of `putU32LE` calls produces, but as a list fold
so that offset lookups can be proven by induction. -/

def wordsConcat : List UInt32 → Bytes
  | [] => ByteArray.empty
  | w :: ws => putU32LE w ByteArray.empty ++ wordsConcat ws

@[simp] theorem wordsConcat_nil : wordsConcat [] = ByteArray.empty := rfl

theorem wordsConcat_cons (w : UInt32) (ws : List UInt32) :
    wordsConcat (w :: ws) = putU32LE w ByteArray.empty ++ wordsConcat ws := rfl

/-- One emitted word occupies exactly four bytes. -/
theorem putU32LE_empty_size (v : UInt32) : (putU32LE v ByteArray.empty).size = 4 := by
  simp [putU32LE]

/-- `wordsConcat` has exactly four bytes per word. -/
theorem wordsConcat_size (ws : List UInt32) : (wordsConcat ws).size = 4 * ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    rw [wordsConcat_cons, ByteArray.size_append, putU32LE_empty_size, ih]
    simp only [List.length_cons]
    omega

/-- The `k`-th word of a word list, read back at byte offset `4*k`. -/
theorem getU32LE_wordsConcat {ws : List UInt32} {k : Nat} (h : k < ws.length) :
    getU32LE (wordsConcat ws) (4 * k) = some (ws.get ⟨k, h⟩) := by
  induction ws generalizing k with
  | nil => exact absurd h (Nat.not_lt_zero k)
  | cons w ws ih =>
    cases k with
    | zero =>
      rw [wordsConcat_cons]
      rw [getU32LE_append_left (i := 0) (by
        rw [putU32LE_empty_size]; omega)]
      simpa using getU32LE_putU32LE ByteArray.empty w
    | succ k =>
      rw [wordsConcat_cons]
      have hk : k < ws.length := by simpa using h
      have hpos : 4 * (k + 1) = (putU32LE w ByteArray.empty).size + 4 * k := by
        rw [putU32LE_empty_size]; omega
      rw [hpos, getU32LE_append_right' (a := putU32LE w ByteArray.empty)]
      rw [ih hk]
      simp only [List.get_cons_succ]

/-- `l[i]? = some v` implies `l[i] = v`. -/
theorem list_getElem_eq_of_getElem? {α : Type} {l : List α} {i : Nat}
    {h : i < l.length} {v : α} (hv : l[i]? = some v) : l[i] = v := by
  have hsome := List.getElem?_eq_getElem (l := l) (i := i) h
  rw [hv] at hsome
  exact (Option.some.inj hsome).symm

/-- Read word `k` of an emitted word list, given its `[k]?` value. -/
theorem word_read {ws : List UInt32} (k : Nat) (hk : k < ws.length) (v : UInt32)
    (hv : ws[k]? = some v) : getU32LE (wordsConcat ws) (4 * k) = some v := by
  rw [getU32LE_wordsConcat hk]
  congr 1
  rw [List.get_eq_getElem]
  exact list_getElem_eq_of_getElem? hv

/-! ### DDS -/

structure DdsHeader where
  width      : UInt32
  height     : UInt32
  dxgi       : UInt32
  blockBytes : UInt32
  deriving Repr, DecidableEq

/-- Row pitch in bytes: one 4-column block row. -/
def ddsPitch (h : DdsHeader) : Nat :=
  ((h.width.toNat + 3) / 4) * h.blockBytes.toNat

def ddsFileSize (h : DdsHeader) : Nat :=
  ddsHeaderSize +
    ((h.width.toNat + 3) / 4) * ((h.height.toNat + 3) / 4) * h.blockBytes.toNat

/-- The 37 little-endian words of the DDS header written by
  `tc_dds_write_bc_memory` (offsets 0,4,…,144). -/
def ddsWords (h : DdsHeader) : List UInt32 :=
  [0x20534444,        --  0: "DDS "
   124,               --  4: dwSize
   0x0002100F,        --  8: flags
   h.height,          -- 12
   h.width,           -- 16
   UInt32.ofNat (ddsPitch h), -- 20: pitch
   0,                 -- 24
   1,                 -- 28: mip count
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  -- 32..72
   32,                -- 76: pixel-format size
   0x00000004,        -- 80: DDPF_FOURCC
   0x30315844,        -- 84: "DX10"
   0, 0, 0, 0, 0,     -- 88..104
   0x00001000,        --108
   h.dxgi,            --112
   3,                 --116: D3D10_RESOURCE_DIMENSION_TEXTURE2D
   0,                 --120
   1,                 --124: array size
   0, 0, 0, 0, 0]     --128..144

def emitDdsHeader (h : DdsHeader) : Emit := fun _ => wordsConcat (ddsWords h)

/-- Parse a DDS header back out. `blockBytes` is recovered from the row
  pitch and width, so 8-byte (BC1/BC5) and 16-byte (BC3/BC6H/BC7) layouts
  both round trip. -/
def parseDdsHeader (b : Bytes) : Option DdsHeader := do
  let magic ← getU32LE b 0
  if magic ≠ 0x20534444 then none else pure ()
  let dwSize ← getU32LE b 4
  if dwSize ≠ 124 then none else pure ()
  let fourcc ← getU32LE b 84
  if fourcc ≠ 0x30315844 then none else pure ()
  let height ← getU32LE b 12
  let width ← getU32LE b 16
  let pitch ← getU32LE b 20
  let dxgi ← getU32LE b 112
  let bx := (width.toNat + 3) / 4
  if bx = 0 then none else pure ()
  if pitch.toNat % bx ≠ 0 then none else pure ()
  pure { width := width, height := height, dxgi := dxgi,
         blockBytes := UInt32.ofNat (pitch.toNat / bx) }

/-- Emitted DDS header has exactly 148 bytes. -/
theorem emitDdsHeader_size (h : DdsHeader) : (emitDdsHeader h ByteArray.empty).size = 148 := by
  show (wordsConcat (ddsWords h)).size = 148
  rw [wordsConcat_size]
  simp [ddsWords]

/-- Header-only reads are unaffected by a trailing payload. -/
theorem dds_read_ext {h : DdsHeader} {p : Bytes} {off : Nat} {v : UInt32}
    (hoff : off + 4 ≤ (wordsConcat (ddsWords h)).size)
    (hv : getU32LE (wordsConcat (ddsWords h)) off = some v) :
    getU32LE (wordsConcat (ddsWords h) ++ p) off = some v := by
  rw [getU32LE_append_left hoff]
  exact hv

/-- Named offsets of the DDS header words the parser reads. -/
theorem dds_read_magic (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 0 = some 0x20534444 := by
  have hk : 0 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 0 hk 0x20534444 (by simp [ddsWords])
  rwa [show 4 * 0 = 0 from rfl] at h

theorem dds_read_dwsize (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 4 = some 124 := by
  have hk : 1 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 1 hk 124 (by simp [ddsWords])
  rwa [show 4 * 1 = 4 from rfl] at h

theorem dds_read_height (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 12 = some h.height := by
  have hk : 3 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 3 hk h.height (by simp [ddsWords])
  rwa [show 4 * 3 = 12 from rfl] at h

theorem dds_read_width (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 16 = some h.width := by
  have hk : 4 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 4 hk h.width (by simp [ddsWords])
  rwa [show 4 * 4 = 16 from rfl] at h

theorem dds_read_pitch (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 20 = some (UInt32.ofNat (ddsPitch h)) := by
  have hk : 5 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 5 hk (UInt32.ofNat (ddsPitch h)) (by simp [ddsWords])
  rwa [show 4 * 5 = 20 from rfl] at h

theorem dds_read_fourcc (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 84 = some 0x30315844 := by
  have hk : 21 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 21 hk 0x30315844 (by simp [ddsWords])
  rwa [show 4 * 21 = 84 from rfl] at h

theorem dds_read_dxgi (h : DdsHeader) :
    getU32LE (wordsConcat (ddsWords h)) 112 = some h.dxgi := by
  have hk : 28 < (ddsWords h).length := by simp [ddsWords]
  have h := word_read (ws := ddsWords h) 28 hk h.dxgi (by simp [ddsWords])
  rwa [show 4 * 28 = 112 from rfl] at h

/-- Parsing an emitted header recovers every field, even when more bytes
  (the payload) follow it. Requires a non-zero width and a pitch that fits
  in a `UInt32`. -/
theorem parseDdsHeader_append (h : DdsHeader) (p : Bytes)
    (hw : h.width.toNat ≥ 1) (hp : ddsPitch h < 2 ^ 32) :
    parseDdsHeader (wordsConcat (ddsWords h) ++ p) = some h := by
  have hsz : (wordsConcat (ddsWords h)).size = 148 := by
    rw [wordsConcat_size]; simp [ddsWords]
  have hbxpos : 0 < (h.width.toNat + 3) / 4 := by omega
  have hmod : ddsPitch h % ((h.width.toNat + 3) / 4) = 0 := by
    unfold ddsPitch; exact Nat.mul_mod_right _ _
  have hdiv : ddsPitch h / ((h.width.toNat + 3) / 4) = h.blockBytes.toNat := by
    unfold ddsPitch; exact Nat.mul_div_right _ hbxpos
  have hof : (UInt32.ofNat (ddsPitch h)).toNat = ddsPitch h :=
    Nat.mod_eq_of_lt hp
  have h1 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_magic h)
  have h2 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_dwsize h)
  have h3 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_height h)
  have h4 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_width h)
  have h5 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_pitch h)
  have h6 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_fourcc h)
  have h7 := dds_read_ext (p := p) (by rw [hsz]; omega) (dds_read_dxgi h)
  simp [parseDdsHeader, h1, h2, h3, h4, h5, h6, h7, hof, hdiv, hmod, hw]

/-- General DDS header round trip (no payload). -/
theorem parseDdsHeader_emit (h : DdsHeader) (hw : h.width.toNat ≥ 1)
    (hp : ddsPitch h < 2 ^ 32) :
    parseDdsHeader (emitDdsHeader h ByteArray.empty) = some h := by
  have := parseDdsHeader_append h ByteArray.empty hw hp
  simpa [emitDdsHeader] using this

theorem ddsFileSize_eq (h : DdsHeader) :
    ddsFileSize h = ddsHeaderSize +
      ((h.width.toNat + 3) / 4) * ((h.height.toNat + 3) / 4) * h.blockBytes.toNat := by
  rfl

/-! ### KTX -/

structure KtxHeader where
  width          : UInt32
  height         : UInt32
  internalFormat : UInt32
  baseFormat     : UInt32
  payloadSize    : UInt32
  deriving Repr, DecidableEq

/-- The 17 little-endian words of the KTX 1 header written by
  `tc_ktx_write_compressed_memory` (offsets 0,4,…,64). The first three
  words are the 12-byte identifier 0xAB4B5458 203131BB 0D0A1A0A. -/
def ktxWords (h : KtxHeader) : List UInt32 :=
  [0x58544BAB,        --  0: KTX id bytes 0..3
   0xBB313120,        --  4: KTX id bytes 4..7
   0x0A1A0A0D,        --  8: KTX id bytes 8..11
   ktxEndianMarker,   -- 12
   0,                 -- 16: glType
   1,                 -- 20: glTypeSize
   0,                 -- 24: glFormat
   h.internalFormat,  -- 28
   h.baseFormat,      -- 32
   h.width,           -- 36
   h.height,          -- 40
   0,                 -- 44: glDepth
   0,                 -- 48: numberOfArrayElements
   1,                 -- 52: numberOfFaces
   1,                 -- 56: numberOfMipmapLevels
   0,                 -- 60: bytesOfKeyValueData
   h.payloadSize]     -- 64

def emitKtxHeader (h : KtxHeader) : Emit := fun _ => wordsConcat (ktxWords h)

/-- Parse a KTX 1 header back out. -/
def parseKtxHeader (b : Bytes) : Option KtxHeader := do
  let m0 ← getU32LE b 0
  let m1 ← getU32LE b 4
  let m2 ← getU32LE b 8
  if !(m0 = 0x58544BAB && m1 = 0xBB313120 && m2 = 0x0A1A0A0D) then none else pure ()
  let endian ← getU32LE b 12
  if endian ≠ ktxEndianMarker then none else pure ()
  let internalFormat ← getU32LE b 28
  let baseFormat ← getU32LE b 32
  let width ← getU32LE b 36
  let height ← getU32LE b 40
  let payloadSize ← getU32LE b 64
  pure { width := width, height := height, internalFormat := internalFormat,
         baseFormat := baseFormat, payloadSize := payloadSize }

def ktxFileSize (h : KtxHeader) : Nat := ktxHeaderSize + h.payloadSize.toNat

/-- Emitted KTX header has exactly 68 bytes. -/
theorem emitKtxHeader_size (h : KtxHeader) : (emitKtxHeader h ByteArray.empty).size = 68 := by
  show (wordsConcat (ktxWords h)).size = 68
  rw [wordsConcat_size]
  simp [ktxWords]

/-- Named offsets of the KTX header words the parser reads. -/
theorem ktx_read_magic0 (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 0 = some 0x58544BAB := by
  have hk : 0 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 0 hk 0x58544BAB (by simp [ktxWords])
  rwa [show 4 * 0 = 0 from rfl] at h

theorem ktx_read_magic1 (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 4 = some 0xBB313120 := by
  have hk : 1 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 1 hk 0xBB313120 (by simp [ktxWords])
  rwa [show 4 * 1 = 4 from rfl] at h

theorem ktx_read_magic2 (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 8 = some 0x0A1A0A0D := by
  have hk : 2 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 2 hk 0x0A1A0A0D (by simp [ktxWords])
  rwa [show 4 * 2 = 8 from rfl] at h

theorem ktx_read_endian (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 12 = some ktxEndianMarker := by
  have hk : 3 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 3 hk ktxEndianMarker (by simp [ktxWords])
  rwa [show 4 * 3 = 12 from rfl] at h

theorem ktx_read_internal (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 28 = some h.internalFormat := by
  have hk : 7 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 7 hk h.internalFormat (by simp [ktxWords])
  rwa [show 4 * 7 = 28 from rfl] at h

theorem ktx_read_base (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 32 = some h.baseFormat := by
  have hk : 8 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 8 hk h.baseFormat (by simp [ktxWords])
  rwa [show 4 * 8 = 32 from rfl] at h

theorem ktx_read_width (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 36 = some h.width := by
  have hk : 9 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 9 hk h.width (by simp [ktxWords])
  rwa [show 4 * 9 = 36 from rfl] at h

theorem ktx_read_height (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 40 = some h.height := by
  have hk : 10 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 10 hk h.height (by simp [ktxWords])
  rwa [show 4 * 10 = 40 from rfl] at h

theorem ktx_read_payload (h : KtxHeader) :
    getU32LE (wordsConcat (ktxWords h)) 64 = some h.payloadSize := by
  have hk : 16 < (ktxWords h).length := by simp [ktxWords]
  have h := word_read (ws := ktxWords h) 16 hk h.payloadSize (by simp [ktxWords])
  rwa [show 4 * 16 = 64 from rfl] at h

/-- Header-only reads are unaffected by a trailing payload. -/
theorem ktx_read_ext {h : KtxHeader} {p : Bytes} {off : Nat} {v : UInt32}
    (hoff : off + 4 ≤ (wordsConcat (ktxWords h)).size)
    (hv : getU32LE (wordsConcat (ktxWords h)) off = some v) :
    getU32LE (wordsConcat (ktxWords h) ++ p) off = some v := by
  rw [getU32LE_append_left hoff]
  exact hv

/-- Parsing an emitted KTX header recovers every field, even when the
  image payload follows it. -/
theorem parseKtxHeader_append (h : KtxHeader) (p : Bytes) :
    parseKtxHeader (wordsConcat (ktxWords h) ++ p) = some h := by
  have hsz : (wordsConcat (ktxWords h)).size = 68 := by
    rw [wordsConcat_size]; simp [ktxWords]
  have h0 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_magic0 h)
  have h1 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_magic1 h)
  have h2 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_magic2 h)
  have h3 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_endian h)
  have h4 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_internal h)
  have h5 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_base h)
  have h6 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_width h)
  have h7 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_height h)
  have h8 := ktx_read_ext (p := p) (by rw [hsz]; omega) (ktx_read_payload h)
  simp [parseKtxHeader, h0, h1, h2, h3, h4, h5, h6, h7, h8, ktxEndianMarker]

/-- General KTX header round trip (no payload). -/
theorem parseKtxHeader_emit (h : KtxHeader) :
    parseKtxHeader (emitKtxHeader h ByteArray.empty) = some h := by
  have := parseKtxHeader_append h ByteArray.empty
  simpa [emitKtxHeader] using this

theorem ktxFileSize_eq (h : KtxHeader) :
    ktxFileSize h = ktxHeaderSize + h.payloadSize.toNat := by
  rfl


-- ============================================================
-- Size / block-count equations (Texcomp/Size.lean content)
-- ============================================================

def blocks4 (n : Nat) : Nat := (n + 3) / 4

def blockCount4 (w h : Nat) : Nat := blocks4 w * blocks4 h

def bc16Size (w h : Nat) : Nat := blockCount4 w h * 16

def bc8Size (w h : Nat) : Nat := blockCount4 w h * 8

def astcPayloadSize (bx by_ w h : Nat) : Nat :=
  ((w + bx - 1) / bx) * ((h + by_ - 1) / by_) * 16

def ddsSize16 (w h : Nat) : Nat := 148 + bc16Size w h
def ddsSize8  (w h : Nat) : Nat := 148 + bc8Size w h

def ktxSize (payload : Nat) : Nat := 68 + payload

theorem blocks4_pos (w : Nat) (hw : w ≥ 1) : blocks4 w ≥ 1 := by
  unfold blocks4
  omega

theorem blockCount4_pos (w h : Nat) (hw : w ≥ 1) (hh : h ≥ 1) :
    blockCount4 w h ≥ 1 := by
  unfold blockCount4
  have hb1 : blocks4 w ≥ 1 := blocks4_pos w hw
  have hb2 : blocks4 h ≥ 1 := blocks4_pos h hh
  exact Nat.mul_pos hb1 hb2

/-! ### Sanity: the word lists reproduce the byte layout of the C writers -/

/-- `ddsWords` has the 37 words (148 bytes) of `tc_dds_write_bc_memory`. -/
theorem ddsWords_length (h : DdsHeader) : (ddsWords h).length = 37 := by
  simp [ddsWords]

/-- `ktxWords` has the 17 words (68 bytes) of `tc_ktx_write_compressed_memory`. -/
theorem ktxWords_length (h : KtxHeader) : (ktxWords h).length = 17 := by
  simp [ktxWords]


/-! ### Payload-carrying containers

A DDS/KTX file is the fixed header followed by the codec's block payload.
The models below pair the two and prove that the parse/emit round trip
recovers the payload byte-exactly, so a container writer can be checked
against its reader without modelling the codec itself. -/

/-- Byte size of the DDS block payload implied by this header. -/
def ddsPayloadSize (h : DdsHeader) : Nat :=
  ((h.width.toNat + 3) / 4) * ((h.height.toNat + 3) / 4) * h.blockBytes.toNat

structure DdsFile where
  (header : DdsHeader)
  (payload : Bytes)
  deriving Repr

/-- Emit a complete DDS file: the 148-byte header, then the block payload. -/
def emitDdsFile (f : DdsFile) : Bytes :=
  wordsConcat (ddsWords f.header) ++ f.payload

/-- Parse a complete DDS file. The payload length is derived from the header
  (width/height/block size), so a truncated file is rejected. -/
def parseDdsFile (b : Bytes) : Option DdsFile := do
  let h ← parseDdsHeader b
  if b.size < ddsHeaderSize + ddsPayloadSize h then none else pure ()
  pure ⟨h, b.extract ddsHeaderSize (ddsHeaderSize + ddsPayloadSize h)⟩

/-- A complete DDS file is the header size plus the payload size. -/
theorem emitDdsFile_size (f : DdsFile) :
    (emitDdsFile f).size = ddsHeaderSize + f.payload.size := by
  rw [emitDdsFile, ByteArray.size_append, wordsConcat_size, ddsWords_length]
  rfl

/-- Complete DDS file round trip: parsing an emitted file recovers the header
  fields and the payload bytes exactly, provided the payload length matches
  what the header implies. -/
theorem parseDdsFile_emit (f : DdsFile) (hs : f.payload.size = ddsPayloadSize f.header)
    (hw : f.header.width.toNat ≥ 1) (hp : ddsPitch f.header < 2 ^ 32) :
    parseDdsFile (emitDdsFile f) = some f := by
  have hHdr : parseDdsHeader (wordsConcat (ddsWords f.header) ++ f.payload) = some f.header :=
    parseDdsHeader_append f.header f.payload hw hp
  have hszH : (wordsConcat (ddsWords f.header)).size = ddsHeaderSize := by
    rw [wordsConcat_size, ddsWords_length]; rfl
  have hlen : ByteArray.size (wordsConcat (ddsWords f.header) ++ f.payload)
      = ddsHeaderSize + ddsPayloadSize f.header := by
    rw [ByteArray.size_append, hszH, hs]
  have hnot : ¬ ByteArray.size (wordsConcat (ddsWords f.header) ++ f.payload)
      < ddsHeaderSize + ddsPayloadSize f.header := by omega
  show parseDdsFile (wordsConcat (ddsWords f.header) ++ f.payload) = some f
  have hempty : (wordsConcat (ddsWords f.header)).extract ddsHeaderSize
      (ddsHeaderSize + ddsPayloadSize f.header) = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff, hszH]
    omega
  have hext : (wordsConcat (ddsWords f.header) ++ f.payload).extract ddsHeaderSize
      (ddsHeaderSize + ddsPayloadSize f.header) = f.payload := by
    rw [ByteArray.extract_append, hszH, hempty, ByteArray.empty_append]
    rw [show ddsHeaderSize - ddsHeaderSize = 0 from by simp [ddsHeaderSize]]
    rw [show ddsHeaderSize + ddsPayloadSize f.header - ddsHeaderSize
        = ddsPayloadSize f.header from by simp only [ddsHeaderSize]; omega]
    rw [← hs, ByteArray.extract_zero_size]
  simp [parseDdsFile, hHdr, hext, hlen]

/-- A complete KTX file is the 68-byte header plus the image payload. -/
structure KtxFile where
  (header : KtxHeader)
  (payload : Bytes)
  deriving Repr

def emitKtxFile (f : KtxFile) : Bytes :=
  wordsConcat (ktxWords f.header) ++ f.payload

def parseKtxFile (b : Bytes) : Option KtxFile := do
  let h ← parseKtxHeader b
  if b.size < ktxHeaderSize + h.payloadSize.toNat then none else pure ()
  pure ⟨h, b.extract ktxHeaderSize (ktxHeaderSize + h.payloadSize.toNat)⟩

theorem emitKtxFile_size (f : KtxFile) :
    (emitKtxFile f).size = ktxHeaderSize + f.payload.size := by
  rw [emitKtxFile, ByteArray.size_append, wordsConcat_size, ktxWords_length]
  rfl

/-- Complete KTX file round trip. -/
theorem parseKtxFile_emit (f : KtxFile)
    (hs : f.payload.size = f.header.payloadSize.toNat) :
    parseKtxFile (emitKtxFile f) = some f := by
  have hHdr : parseKtxHeader (wordsConcat (ktxWords f.header) ++ f.payload) = some f.header :=
    parseKtxHeader_append f.header f.payload
  have hszH : (wordsConcat (ktxWords f.header)).size = ktxHeaderSize := by
    rw [wordsConcat_size, ktxWords_length]; rfl
  have hlen : ByteArray.size (wordsConcat (ktxWords f.header) ++ f.payload)
      = ktxHeaderSize + f.header.payloadSize.toNat := by
    rw [ByteArray.size_append, hszH, hs]
  have hnot : ¬ ByteArray.size (wordsConcat (ktxWords f.header) ++ f.payload)
      < ktxHeaderSize + f.header.payloadSize.toNat := by omega
  show parseKtxFile (wordsConcat (ktxWords f.header) ++ f.payload) = some f
  have hempty : (wordsConcat (ktxWords f.header)).extract ktxHeaderSize
      (ktxHeaderSize + f.header.payloadSize.toNat) = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff, hszH]
    omega
  have hext : (wordsConcat (ktxWords f.header) ++ f.payload).extract ktxHeaderSize
      (ktxHeaderSize + f.header.payloadSize.toNat) = f.payload := by
    rw [ByteArray.extract_append, hszH, hempty, ByteArray.empty_append]
    rw [show ktxHeaderSize - ktxHeaderSize = 0 from by simp [ktxHeaderSize]]
    rw [show ktxHeaderSize + f.header.payloadSize.toNat - ktxHeaderSize
        = f.header.payloadSize.toNat from by simp only [ktxHeaderSize]; omega]
    rw [← hs, ByteArray.extract_zero_size]
  simp [parseKtxFile, hHdr, hext, hlen]

end Texcomp
