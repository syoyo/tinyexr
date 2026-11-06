/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Full-file structural parser:

  * magic number and version field,
  * one header per part (attribute lists ended by 0x00; multi-part files end
    the header section with one extra 0x00),
  * one chunk-offset table per part,
  * the start of pixel data.

  Pixel payloads are not decoded here; the parser validates container
  structure only (see `Exr.Pxr24` / `Exr.B44` for the modelled codecs).

  All reads go through the total byte layer, so the parser cannot read out of
  bounds on hostile input; `parseFile_bounds` states the resulting cursor
  invariants.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.File
import Exr.Version

namespace Exr

/-- A structural parse result. -/
structure ParsedFile where
  /-- Decoded version field. -/
  version : Version
  /-- One header per part. -/
  parts : List Header
  /-- One offset table per part. -/
  offsetTables : List OffsetTable
  /-- Absolute offset where pixel data begins. -/
  dataStart : Nat
  deriving Repr

namespace Parse

/-- Find the first attribute with the given type name. -/
def findAttr (attrs : List RawAttr) (name : String) : Option RawAttr :=
  attrs.find? (fun a => TypedAttr.nameEq a.name name)

/-- Decode an attribute expected to have a fixed size. -/
def typedBlob (attrs : List RawAttr) (name : String) (size : Nat) : Option Bytes :=
  (findAttr attrs name).bind fun a =>
    if a.value.size == size then some a.value else none

/-- Read the `channels` attribute into a channel list. -/
def channelsOf (attrs : List RawAttr) : Option (List Channel) :=
  (findAttr attrs "channels").bind fun a =>
    (TypedAttr.decodeChlist a.value).map Prod.fst

def box2iOf (attrs : List RawAttr) (name : String) : Option Box2i :=
  (findAttr attrs name).bind fun a => TypedAttr.decodeBox2i a.value

def compressionOf (attrs : List RawAttr) : Option Compression :=
  (findAttr attrs "compression").bind fun a => TypedAttr.decodeCompression a.value

def lineOrderOf (attrs : List RawAttr) : Option LineOrder :=
  (findAttr attrs "lineOrder").bind fun a => TypedAttr.decodeLineOrder a.value

def u32Of (attrs : List RawAttr) (name : String) : Option UInt32 :=
  (findAttr attrs name).bind fun a => TypedAttr.decodeFloatBits a.value

def v2fOf (attrs : List RawAttr) (name : String) : Option (UInt32 × UInt32) :=
  (findAttr attrs name).bind fun a => TypedAttr.decodeV2f a.value

def tileDescOf (attrs : List RawAttr) : Option TypedAttr.TileDesc :=
  (findAttr attrs "tiles").bind fun a => TypedAttr.decodeTileDesc a.value

def bytesOf (attrs : List RawAttr) (name : String) : Option Bytes :=
  (findAttr attrs name).map RawAttr.value

def int32Of (attrs : List RawAttr) (name : String) : Option Int32 :=
  (findAttr attrs name).bind fun a => TypedAttr.decodeInt a.value

def partTypeOf (attrs : List RawAttr) (fallback : PartType) : Option PartType :=
  match findAttr attrs "type" with
  | some a =>
    -- `type` is a `string` attribute; interpret its raw bytes.
    match String.fromUTF8? a.value with
    | some s => PartType.ofWireName s
    | none => none
  | none => some fallback

/-- Build a `Header` from a decoded attribute list.

    `singleTile` is the version field's tile bit; it is the fallback part
    type when no `type` attribute is present (single-part files). -/
def headerOfAttrs (attrs : List RawAttr) (singleTile deep : Bool) : Option Header := do
  let dataWindow ← box2iOf attrs "dataWindow"
  let displayWindow ← box2iOf attrs "displayWindow"
  let channels ← channelsOf attrs
  let compression ← compressionOf attrs
  let lineOrder ← lineOrderOf attrs
  let pixelAspectRatio ← u32Of attrs "pixelAspectRatio"
  let (centerX, centerY) ← v2fOf attrs "screenWindowCenter"
  let screenWindowWidth ← u32Of attrs "screenWindowWidth"
  let fallback : PartType :=
    if deep then (if singleTile then PartType.deepTiled else PartType.deepScanline)
    else if singleTile then PartType.tiled else PartType.scanline
  let partType ← partTypeOf attrs fallback
  let chunkCount :=
    match int32Of attrs "chunkCount" with
    | some v => if v.toInt ≥ 0 then some v.toInt.toNat else none
    | none => none
  pure
    { partType := partType
      dataWindow := dataWindow
      displayWindow := displayWindow
      channels := channels
      compression := compression
      lineOrder := lineOrder
      pixelAspectRatio := pixelAspectRatio
      screenWindowCenterX := centerX
      screenWindowCenterY := centerY
      screenWindowWidth := screenWindowWidth
      tileDesc := tileDescOf attrs
      name := bytesOf attrs "name"
      chunkCount := chunkCount
      maxSamplesPerPixel := int32Of attrs "maxSamplesPerPixel"
      attrs := attrs }

/-- Read a u64 LE offset. -/
def offsetOf (b : Bytes) (i : Nat) : Option Nat :=
  (getU64LE b i).map UInt64.toNat

/-- Parse `count` u64 offset entries starting at `i` (structural on `count`). -/
private def parseOffsetTableGo (b : Bytes) : Nat → Nat → Option (OffsetTable × Nat)
  | 0, i => some ({ offsets := [] }, i)
  | count + 1, i =>
    match offsetOf b i with
    | none => none
    | some o =>
      match parseOffsetTableGo b count (i + 8) with
      | none => none
      | some (rest, j) => some ({ offsets := o :: rest.offsets }, j)

/-- Parse an offset table of `count` u64 entries starting at `i`. -/
def parseOffsetTable (b : Bytes) (count : Nat) (i : Nat) : Option (OffsetTable × Nat) :=
  parseOffsetTableGo b count i

theorem parseOffsetTableGo_bounds {b : Bytes} {count i : Nat} {t : OffsetTable} {j : Nat}
    (h : parseOffsetTableGo b count i = some (t, j)) :
    j = i + 8 * count ∧ (0 < count → j ≤ b.size) := by
  induction count generalizing i t j with
  | zero =>
    simp only [parseOffsetTableGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    omega
  | succ count ih =>
    simp only [parseOffsetTableGo] at h
    cases ho : offsetOf b i with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      cases hrec : parseOffsetTableGo b count (i + 8) with
      | none => simp [hrec] at h
      | some p =>
        obtain ⟨rest, j⟩ := p
        simp only [hrec] at h
        obtain ⟨_, rfl⟩ := h
        have hidx := ih hrec
        have hoff : i + 8 ≤ b.size := by
          unfold offsetOf at ho
          cases hv : getU64LE b i with
          | none => simp [hv] at ho
          | some v => exact getU64LE_ibounds hv
        constructor
        · omega
        · intro _
          rcases Nat.eq_zero_or_pos count with h0 | hpos
          · subst h0; omega
          · have := hidx.2 hpos; omega

theorem parseOffsetTable_bounds {b : Bytes} {count i : Nat} {t : OffsetTable} {j : Nat}
    (h : parseOffsetTable b count i = some (t, j)) :
    j = i + 8 * count ∧ (0 < count → j ≤ b.size) :=
  parseOffsetTableGo_bounds h

/-- The table built by the parser has exactly `count` entries. -/
theorem parseOffsetTableGo_length {b : Bytes} {count i : Nat} {t : OffsetTable} {j : Nat}
    (h : parseOffsetTableGo b count i = some (t, j)) :
    t.offsets.length = count := by
  induction count generalizing i t j with
  | zero =>
    simp only [parseOffsetTableGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h01, rfl⟩ := h
    subst h01
    rfl
  | succ count ih =>
    simp only [parseOffsetTableGo] at h
    cases ho : offsetOf b i with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      cases hrec : parseOffsetTableGo b count (i + 8) with
      | none => simp [hrec] at h
      | some p =>
        obtain ⟨rest, j⟩ := p
        simp only [hrec] at h
        obtain ⟨_, rfl⟩ := h
        show (o :: rest.offsets).length = count + 1
        rw [List.length_cons, ih hrec]

/-- The table built by the parser has exactly `count` entries. -/
theorem parseOffsetTable_length {b : Bytes} {count i : Nat} {t : OffsetTable} {j : Nat}
    (h : parseOffsetTable b count i = some (t, j)) :
    t.offsets.length = count :=
  parseOffsetTableGo_length h

/-- The zero byte terminating a header section. -/
def headerTerminator : Bytes := ByteArray.mk #[0]

/-- Parse headers until an empty header (multi-part) or the single
    end-of-header byte (single-part) is reached. `fuel` bounds the scan. -/
def parsePartHeaders (b : Bytes) (longNames multipart deep : Bool) (singleTile : Bool)
    (i : Nat) (fuel : Nat) : Option (List Header × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match RawAttr.parseAll b longNames i fuel with
    | none => none
    | some (attrs, j) =>
      if attrs.isEmpty then
        -- empty header: multi-part terminator; single-part files must have
        -- attributes, so an empty list is only valid for multi-part.
        if multipart then some ([], j) else none
      else
        match headerOfAttrs attrs singleTile deep with
        | none => none
        | some h =>
          if multipart then
            match parsePartHeaders b longNames multipart deep singleTile j fuel with
            | none => none
            | some (rest, k) => some (h :: rest, k)
          else
            some ([h], j)

/-- Chunk count for a part: declared value when present, else computed. -/
def chunkCountOf (h : Header) : Nat :=
  match h.chunkCount with
  | some n => n
  | none => h.computedChunks

/-- Parse one offset table per part (structural on the part list). -/
def parseTables (b : Bytes) : List Header → Nat → Option (List OffsetTable × Nat)
  | [], i => some ([], i)
  | h :: rest, i =>
    match parseOffsetTable b (chunkCountOf h) i with
    | none => none
    | some (t, j) =>
      match parseTables b rest j with
      | none => none
      | some (ts, k) => some (t :: ts, k)

theorem parseTables_bounds {b : Bytes} {parts : List Header} {i : Nat}
    {ts : List OffsetTable} {j : Nat}
    (h : parseTables b parts i = some (ts, j)) : j ≤ max i b.size := by
  induction parts generalizing i ts j with
  | nil =>
    simp only [parseTables, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact Nat.le_max_left ..
  | cons hd tl ih =>
    simp only [parseTables] at h
    cases ht : parseOffsetTable b (chunkCountOf hd) i with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, j₁⟩ := p
      simp only [ht] at h
      cases hr : parseTables b tl j₁ with
      | none => simp [hr] at h
      | some p₂ =>
        obtain ⟨ts', j₂⟩ := p₂
        simp only [hr] at h
        obtain ⟨_, rfl⟩ := h
        have hrec := ih hr
        rcases parseOffsetTable_bounds ht with ⟨heq, hpos⟩
        have hj₁ : j₁ ≤ max i b.size := by
          rcases Nat.eq_zero_or_pos (chunkCountOf hd) with hz | hp
          · rw [heq]
            simp only [hz, Nat.mul_zero, Nat.add_zero]
            exact Nat.le_max_left ..
          · exact Nat.le_trans (hpos hp) (Nat.le_max_right ..)
        exact Nat.le_trans hrec (by omega)

/-- One offset table per part. -/
theorem parseTables_length {b : Bytes} {parts : List Header} {i : Nat}
    {ts : List OffsetTable} {j : Nat}
    (h : parseTables b parts i = some (ts, j)) :
    ts.length = parts.length := by
  induction parts generalizing i ts j with
  | nil =>
    simp only [parseTables, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h01, rfl⟩ := h
    subst h01
    rfl
  | cons hd tl ih =>
    simp only [parseTables] at h
    cases ht : parseOffsetTable b (chunkCountOf hd) i with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, j₁⟩ := p
      simp only [ht] at h
      cases hr : parseTables b tl j₁ with
      | none => simp [hr] at h
      | some p₂ =>
        obtain ⟨ts', j₂⟩ := p₂
        simp only [hr] at h
        obtain ⟨_, rfl⟩ := h
        show (t :: ts').length = (hd :: tl).length
        rw [List.length_cons, List.length_cons, ih hr]

/-- The offset tables consume exactly `8 × (total chunk count)` bytes; this is
    the equation the writer relies on to lay out the payload area. -/
theorem parseTables_end {b : Bytes} {parts : List Header} {i : Nat}
    {ts : List OffsetTable} {j : Nat}
    (h : parseTables b parts i = some (ts, j)) :
    j = i + 8 * (parts.map chunkCountOf).sum := by
  induction parts generalizing i ts j with
  | nil =>
    simp only [parseTables, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h01, rfl⟩ := h
    subst h01
    simp
  | cons hd tl ih =>
    simp only [parseTables] at h
    cases ht : parseOffsetTable b (chunkCountOf hd) i with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, j₁⟩ := p
      simp only [ht] at h
      cases hr : parseTables b tl j₁ with
      | none => simp [hr] at h
      | some p₂ =>
        obtain ⟨ts', j₂⟩ := p₂
        simp only [hr] at h
        obtain ⟨_, rfl⟩ := h
        have h1 := (parseOffsetTable_bounds ht).1
        have h2 := ih hr
        simp only [List.map_cons, List.sum_cons]
        rw [h2, h1]
        omega

/-- Parse headers stay in bounds. -/
theorem parsePartHeaders_bounds {b : Bytes} {longNames multipart deep singleTile : Bool}
    {i fuel : Nat} {ps : List Header} {j : Nat}
    (h : parsePartHeaders b longNames multipart deep singleTile i fuel = some (ps, j)) :
    j ≤ b.size := by
  induction fuel generalizing i ps j with
  | zero =>
    have : parsePartHeaders b longNames multipart deep singleTile i 0 = none := rfl
    rw [this] at h
    cases h
  | succ fuel ih =>
    unfold parsePartHeaders at h
    cases ha : RawAttr.parseAll b longNames i fuel with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨attrs, j₁⟩ := p
      simp only [ha] at h
      have hb := RawAttr.parseAll_terminates ha
      by_cases hempty : attrs.isEmpty
      · simp [hempty] at h
        cases multipart with
        | true =>
          simp at h
          obtain ⟨_, rfl⟩ := h
          exact hb
        | false => simp at h
      · simp [hempty] at h
        cases hob : headerOfAttrs attrs singleTile deep with
        | none => simp [hob] at h
        | some hd =>
          simp only [hob] at h
          cases multipart with
          | true =>
            simp at h
            cases hr : parsePartHeaders b longNames true deep singleTile j₁ fuel with
            | none => simp [hr] at h
            | some q =>
              obtain ⟨rest, k⟩ := q
              simp only [hr] at h
              obtain ⟨_, rfl⟩ := h
              exact ih hr
          | false =>
            simp at h
            obtain ⟨_, rfl⟩ := h
            exact hb

def parseFile (b : Bytes) : Option ParsedFile :=
  match getU32LE b 0 with
  | none => none
  | some magic =>
    if magic != magicUInt32LE then none
    else
      match getU32LE b 4 with
      | none => none
      | some u =>
        match Version.ofBits u with
        | none => none
        | some v =>
          let longNames := v.longNames
          let multipart := v.multipart
          let deep := v.nonImage
          let singleTile := v.singleTile
          match parsePartHeaders b longNames multipart deep singleTile 8
              (b.size + 1) with
          | none => none
          | some (parts, i) =>
            match parseTables b parts i with
            | none => none
            | some (tables, j) => some { version := v, parts := parts,
                                         offsetTables := tables, dataStart := j }

theorem parseFile_bounds {b : Bytes} {f : ParsedFile} (h : parseFile b = some f) :
    f.dataStart ≤ b.size := by
  unfold parseFile at h
  cases h0 : getU32LE b 0 with
  | none => simp [h0] at h
  | some magic =>
    simp only [h0] at h
    cases hb : (magic != magicUInt32LE) with
    | true => simp [hb] at h
    | false =>
      simp [hb] at h
      cases h4 : getU32LE b 4 with
      | none => simp [h4] at h
      | some u =>
        simp only [h4] at h
        cases ho : Version.ofBits u with
        | none => simp [ho] at h
        | some v =>
          simp only [ho] at h
          cases hp : parsePartHeaders b v.longNames v.multipart v.nonImage
              v.singleTile 8 (b.size + 1) with
          | none => simp [hp] at h
          | some p =>
            obtain ⟨parts, i⟩ := p
            simp only [hp] at h
            cases ht : parseTables b parts i with
            | none => simp [ht] at h
            | some q =>
              obtain ⟨tables, j⟩ := q
              simp only [ht, Option.some.injEq] at h
              cases h
              show j ≤ b.size
              have hpi := parsePartHeaders_bounds hp
              have htj := parseTables_bounds ht
              omega

/-- Parse one header (attribute list) starting at `i`. -/
def parseHeader (b : Bytes) (longNames : Bool) (i : Nat) (fuel : Nat) :
    Option (List RawAttr × Nat) :=
  RawAttr.parseAll b longNames i fuel

/-- Validate that a decoded parse result is structurally sound:

    * multi-part files require a `name` attribute on every part,
    * every part header passes `Header.validate` and any declared
      `chunkCount` equals the computed count,
    * every offset table has one entry per chunk,
    * every offset points into the payload area (`dataStart ≤ off < fileSize`).

    This mirrors OpenEXR/tinyexr header acceptance; `exrcheck` reports it. -/
def checkParts (fileSize : Nat) (f : ParsedFile) : Bool :=
  (if f.version.multipart then f.parts.all (fun h => h.name.isSome) else true) &&
  f.parts.all (fun h => h.validate && h.chunkCountConsistent) &&
  (f.parts.zip f.offsetTables).all (fun (h, t) =>
    t.offsets.length == h.computedChunks &&
    t.offsets.all (fun o => f.dataStart ≤ o && o < fileSize))

/-- OpenEXR-strict variant of `checkParts`: multi-part files must also agree on
    the shared attributes (`displayWindow`, `pixelAspectRatio`). This models
    OpenEXRCore's `internal_exr_validate_shared_attrs`; tinyexr does not enforce
    it, so the lenient `checkParts` remains the default for the differ. -/
def checkPartsOpenEXR (fileSize : Nat) (f : ParsedFile) : Bool :=
  checkParts fileSize f && Header.sharedAttrsOK f.parts

theorem checkPartsOpenEXR_implies_checkParts {fileSize : Nat} {f : ParsedFile}
    (h : checkPartsOpenEXR fileSize f = true) : checkParts fileSize f = true := by
  unfold checkPartsOpenEXR at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem checkParts_parts_valid {f : ParsedFile} {fileSize : Nat}
    (hc : checkParts fileSize f = true) :
    ∀ h ∈ f.parts, h.validate = true ∧ h.chunkCountConsistent = true := by
  have hB : (f.parts.all (fun h => h.validate && h.chunkCountConsistent)) = true := by
    have h := hc
    simp only [checkParts, Bool.and_eq_true] at h
    exact h.1.2
  exact fun h hm => Bool.and_eq_true_iff.mp (List.all_eq_true.mp hB h hm)

end Parse

end Exr
