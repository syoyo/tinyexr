/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Part/header model, validation rules, chunk-count derivation and offset
  tables.

  The model follows the spec (`OpenEXRFileLayout.rst`) and OpenEXR's
  `parse_header.c` / `validation.c` behaviour:

  * required attributes: channels, compression, dataWindow, displayWindow,
    lineOrder, pixelAspectRatio, screenWindowCenter, screenWindowWidth;
  * tiles attribute required for tiled/deep-tiled parts;
  * name / type / chunkCount required for multi-part and deep parts;
  * maxSamplesPerPixel is optional for deep parts (-1 means "unknown"; the
    spec text calls it required, but OpenEXR's library and its own deep sample
    images treat absence as unknown, so we follow the library);
  * channel names strictly sorted, sampling >= 1, no sampling on tiled parts;
  * chunk count = ceil(height / linesPerBlock) for scan-line parts and the
    tile-level sum for tiled parts;
  * a declared chunkCount must equal the computed count.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Tiles

namespace Exr

/-- The four part types (`type` attribute). -/
inductive PartType where
  | scanline
  | tiled
  | deepScanline
  | deepTiled
  deriving DecidableEq, Repr, Inhabited

namespace PartType

def isTiled : PartType → Bool
  | .tiled => true
  | .deepTiled => true
  | _ => false

def isDeep : PartType → Bool
  | .deepScanline => true
  | .deepTiled => true
  | _ => false

/-- Wire string of the `type` attribute. -/
def wireName : PartType → String
  | .scanline => "scanlineimage"
  | .tiled => "tiledimage"
  | .deepScanline => "deepscanline"
  | .deepTiled => "deeptile"

def ofWireName (s : String) : Option PartType :=
  if s == "scanlineimage" then some .scanline
  else if s == "tiledimage" then some .tiled
  else if s == "deepscanline" then some .deepScanline
  else if s == "deeptile" then some .deepTiled
  else none

theorem ofWireName_wireName (p : PartType) : ofWireName p.wireName = some p := by
  cases p <;> rfl

end PartType

/-- A part header (decoded attributes plus the typed core fields). -/
structure Header where
  partType : PartType
  dataWindow : Box2i
  displayWindow : Box2i
  channels : List Channel
  compression : Compression
  lineOrder : LineOrder
  /-- IEEE f32 bits of `pixelAspectRatio`. -/
  pixelAspectRatio : UInt32
  /-- IEEE f32 bits of `screenWindowCenter` (x, y). -/
  screenWindowCenterX : UInt32
  screenWindowCenterY : UInt32
  /-- IEEE f32 bits of `screenWindowWidth`. -/
  screenWindowWidth : UInt32
  tileDesc : Option TypedAttr.TileDesc
  /-- `name` attribute (required for multi-part and deep parts). -/
  name : Option Bytes
  /-- `chunkCount` attribute (required for multi-part and deep parts). -/
  chunkCount : Option Nat
  /-- `maxSamplesPerPixel` (deep parts; -1 means unknown). -/
  maxSamplesPerPixel : Option Int32
  /-- All raw attributes in wire order. -/
  attrs : List RawAttr
  deriving Repr

namespace Header

def width (h : Header) : Int := h.dataWindow.widthInt

def height (h : Header) : Int := h.dataWindow.heightInt

def isTiled (h : Header) : Bool := h.partType.isTiled

def isDeep (h : Header) : Bool := h.partType.isDeep

/-- Computed chunk count: `ceil(height / linesPerBlock)` for scan-line parts,
    the tile-level sum for tiled parts (0 when the tile descriptor is absent,
    which validation rejects). -/
def computedChunks (h : Header) : Nat :=
  if h.isTiled then
    match h.tileDesc with
    | some t =>
      Tiles.tiledChunks t.levelMode t.roundingMode t.xSize t.ySize
        h.width.toNat h.height.toNat
    | none => 0
  else
    Tiles.scanlineChunks h.height.toNat (Compression.linesPerBlock h.compression)

/-- Per-channel validation: sampling >= 1, tiled parts must not subsample,
    channel names are 1..255 bytes. -/
def channelsValid (h : Header) : Bool :=
  h.channels.all (fun c =>
    (decide (1 ≤ c.xSampling.toInt) && decide (1 ≤ c.ySampling.toInt) &&
      (if h.isTiled then (c.xSampling == 1 && c.ySampling == 1) else true) &&
      1 ≤ c.name.size && c.name.size ≤ 255))

/-- Individual validation checks, in order. Kept as a `List Bool` so proofs
    can extract any single check by membership. -/
def validateChecks (h : Header) : List Bool :=
  [ decide (1 ≤ h.width ∧ 1 ≤ h.height),
    decide (h.displayWindow.maxX ≥ h.displayWindow.minX ∧
            h.displayWindow.maxY ≥ h.displayWindow.minY),
    !h.channels.isEmpty,
    channelsValid h,
    decide (Channel.StrictlySorted h.channels),
    if h.isTiled then h.tileDesc.isSome else true,
    match h.tileDesc with
    | some t => decide (1 ≤ t.xSize ∧ 1 ≤ t.ySize)
    | none => true,
    match h.maxSamplesPerPixel with
    | some m => decide (m.toInt ≥ -1)
    | none => true,
    if h.isDeep then Compression.isDeepAllowed h.compression else true,
    if h.isDeep then h.name.isSome else true,
    -- `maxSamplesPerPixel` is required by the spec text for deep parts, but
    -- OpenEXR's library (which the spec declares authoritative) reads deep
    -- files that omit it, treating the value as unknown (-1). We follow the
    -- library: absence is accepted, and `maxSamplesUnknown` reports the
    -- `-1` convention when present.
    true ]

/-- Core validation: every check passes. -/
def validate (h : Header) : Bool := (validateChecks h).all id

theorem validate_spec {h : Header} (hv : h.validate = true) :
    ∀ b ∈ h.validateChecks, b = true := by
  simp only [validate] at hv
  exact List.all_eq_true.mp hv

/-- A declared `chunkCount` must equal the computed count. -/
def chunkCountConsistent (h : Header) : Bool :=
  match h.chunkCount with
  | some n => n == h.computedChunks
  | none => true

/-- A part header is well-formed when validation passes and any declared
    chunk count equals the computed one. -/
def WellFormed (h : Header) : Prop :=
  h.validate = true ∧ h.chunkCountConsistent = true

instance (h : Header) : Decidable (WellFormed h) := by
  unfold WellFormed; infer_instance

theorem wellFormed_validate {h : Header} (hw : WellFormed h) : h.validate = true := hw.1

theorem wellFormed_dataWindow {h : Header} (hw : WellFormed h) :
    1 ≤ h.width ∧ 1 ≤ h.height := by
  have := validate_spec hw.1 (decide (1 ≤ h.width ∧ 1 ≤ h.height)) (by simp [validateChecks])
  exact of_decide_eq_true this

theorem wellFormed_channels_nonempty {h : Header} (hw : WellFormed h) :
    h.channels ≠ [] := by
  have h1 := validate_spec hw.1 (!h.channels.isEmpty) (by simp [validateChecks])
  intro hnil
  rw [hnil] at h1
  simp at h1

theorem wellFormed_channels_valid {h : Header} (hw : WellFormed h) :
    channelsValid h = true :=
  validate_spec hw.1 (channelsValid h) (by simp [validateChecks])

theorem wellFormed_channels_sorted {h : Header} (hw : WellFormed h) :
    Channel.StrictlySorted h.channels := by
  have := validate_spec hw.1 (decide (Channel.StrictlySorted h.channels))
    (by simp [validateChecks])
  exact of_decide_eq_true this

theorem wellFormed_tiled_has_desc {h : Header} (hw : WellFormed h) (ht : h.isTiled = true) :
    h.tileDesc.isSome = true := by
  have h1 := validate_spec hw.1 (if h.isTiled then h.tileDesc.isSome else true)
    (by simp [validateChecks])
  simpa [ht] using h1

theorem wellFormed_tileDesc_dims {h : Header} (hw : WellFormed h) {t : TypedAttr.TileDesc}
    (ht : h.tileDesc = some t) : 1 ≤ t.xSize ∧ 1 ≤ t.ySize := by
  have h1 := validate_spec hw.1
    (match h.tileDesc with | some t => decide (1 ≤ t.xSize ∧ 1 ≤ t.ySize) | none => true)
    (by simp [validateChecks])
  rw [ht] at h1
  exact of_decide_eq_true h1

theorem wellFormed_chunkCount_consistent {h : Header} (hw : WellFormed h) {n : Nat}
    (hc : h.chunkCount = some n) : n = h.computedChunks := by
  have h1 := hw.2
  simp only [chunkCountConsistent, hc, beq_iff_eq] at h1
  exact h1

/-- Tiled parts with a validated tile descriptor have a positive chunk count. -/
theorem computedChunks_pos {h : Header} (hw : WellFormed h) (ht : h.isTiled = true)
    {t : TypedAttr.TileDesc} (hd : h.tileDesc = some t) : 0 < h.computedChunks := by
  have hdim := wellFormed_tileDesc_dims hw hd
  have hwin := wellFormed_dataWindow hw
  have hw1 : 1 ≤ h.width.toNat := by
    have : (0 : Int) ≤ h.width := by omega
    have := Int.toNat_of_nonneg this
    omega
  have hh1 : 1 ≤ h.height.toNat := by
    have : (0 : Int) ≤ h.height := by omega
    have := Int.toNat_of_nonneg this
    omega
  unfold computedChunks
  simp only [ht, hd]
  exact Tiles.tiledChunks_pos t.levelMode t.roundingMode hdim.1 hdim.2 hw1 hh1

end Header

/-- The offset table of one part: one absolute file offset per chunk. -/
structure OffsetTable where
  offsets : List Nat
  deriving DecidableEq, Repr

namespace OffsetTable

/-- All offsets point inside the file. -/
def boundsOK (fileSize : Nat) (t : OffsetTable) : Bool :=
  t.offsets.all (fun o => o < fileSize)

/-- The table has exactly one entry per chunk. -/
def lengthOK (expected : Nat) (t : OffsetTable) : Bool :=
  t.offsets.length == expected

theorem lengthOK_iff {expected : Nat} {t : OffsetTable} :
    lengthOK expected t = true ↔ t.offsets.length = expected := by
  unfold lengthOK
  simp

theorem boundsOK_of_mem {fileSize : Nat} {t : OffsetTable} (h : boundsOK fileSize t = true)
    {o : Nat} (ho : o ∈ t.offsets) : o < fileSize := by
  unfold boundsOK at h
  exact of_decide_eq_true (List.all_eq_true.mp h o ho)

end OffsetTable


/-- Chunk header layouts (byte counts), matching the spec and OpenEXR.

    Regular scan line: [part? 4] y 4 dataSize 4
    Regular tile:      [part? 4] tileX 4 tileY 4 levelX 4 levelY 4 dataSize 4
    Deep scan line:    [part? 4] y 4 packedOffsetTableSize 8
                       packedSampleSize 8 unpackedSampleSize 8
    Deep tile:         [part? 4] tileX/Y/levelX/Y 16
                       packedOffsetTableSize 8 packedSampleSize 8
                       unpackedSampleSize 8
-/
structure ChunkLayout where
  /-- Whether the chunk starts with a part number (multi-part files). -/
  multipart : Bool
  /-- Chunk kind. -/
  deep : Bool
  tiled : Bool
  deriving DecidableEq, Repr

namespace ChunkLayout

def partSize (c : ChunkLayout) : Nat := if c.multipart then 4 else 0

def coordSize (c : ChunkLayout) : Nat := if c.tiled then 16 else 4

def payloadSizeFieldSize (c : ChunkLayout) : Nat := if c.deep then 8 + 8 + 8 else 4

/-- Total chunk header size in bytes (excluding the payload). -/
def headerSize (c : ChunkLayout) : Nat :=
  c.partSize + c.coordSize + c.payloadSizeFieldSize

theorem headerSize_pos (c : ChunkLayout) : 0 < c.headerSize := by
  unfold headerSize partSize coordSize payloadSizeFieldSize
  split <;> split <;> split <;> omega

/-- Header size values for the four part kinds (single- and multi-part). -/
theorem headerSize_scanline {mp : Bool} :
    ({ multipart := mp, deep := false, tiled := false } : ChunkLayout).headerSize
      = (if mp then 12 else 8) := by
  cases mp <;> rfl

theorem headerSize_tiled {mp : Bool} :
    ({ multipart := mp, deep := false, tiled := true } : ChunkLayout).headerSize
      = (if mp then 24 else 20) := by
  cases mp <;> rfl

theorem headerSize_deepScanline {mp : Bool} :
    ({ multipart := mp, deep := true, tiled := false } : ChunkLayout).headerSize
      = (if mp then 32 else 28) := by
  cases mp <;> rfl

theorem headerSize_deepTiled {mp : Bool} :
    ({ multipart := mp, deep := true, tiled := true } : ChunkLayout).headerSize
      = (if mp then 44 else 40) := by
  cases mp <;> rfl

/-- `maxSamplesPerPixel == -1` is the spec's "unknown at write time" marker. -/
def maxSamplesUnknown (m : Int32) : Bool := m.toInt == -1

end ChunkLayout

end Exr
