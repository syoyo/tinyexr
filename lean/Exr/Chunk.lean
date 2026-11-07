/-
  TinyEXR - bounded chunk headers and offset-table correspondence.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Deep

namespace Exr.Chunk

structure Info where
  part : Option Nat
  coords : List Int32
  packedOffsets : Nat
  packedSamples : Nat
  unpackedSamples : Nat
  payloadStart : Nat
  payloadEnd : Nat
  deriving Repr

/-- Read the four chunk-header layouts. Compressed bytes remain opaque. -/
def readHeader (b : Bytes) (h : Header) (multipart : Bool) (offset : Nat) : Option Info := do
  let (part, pos) ← if multipart then do
      let p ← getI32LE b offset
      if p.toInt < 0 then none else pure (some p.toInt.toNat, offset + 4)
    else pure (none, offset)
  let (coords, pos) ← if h.isTiled then do
      let x ← getI32LE b pos
      let y ← getI32LE b (pos + 4)
      let lx ← getI32LE b (pos + 8)
      let ly ← getI32LE b (pos + 12)
      pure ([x, y, lx, ly], pos + 16)
    else do
      let y ← getI32LE b pos
      pure ([y], pos + 4)
  if h.isDeep then
    let pots ← getU64LE b pos
    let psds ← getU64LE b (pos + 8)
    let usds ← getU64LE b (pos + 16)
    pure
      { part := part, coords := coords,
        packedOffsets := pots.toNat, packedSamples := psds.toNat,
        unpackedSamples := usds.toNat, payloadStart := pos + 24,
        payloadEnd := pos + 24 + pots.toNat + psds.toNat }
  else
    let size ← getI32LE b pos
    if size.toInt < 0 then none else
      pure
        { part := part, coords := coords,
          packedOffsets := 0, packedSamples := size.toInt.toNat,
          unpackedSamples := 0, payloadStart := pos + 4,
          payloadEnd := pos + 4 + size.toInt.toNat }

/-- A parsed chunk's entire declared packed payload must lie in the file. -/
def parse (b : Bytes) (h : Header) (multipart : Bool) (offset : Nat) : Option Info := do
  let info ← readHeader b h multipart offset
  if info.payloadStart ≤ info.payloadEnd ∧ info.payloadEnd ≤ b.size then some info else none

theorem parse_bounds {b : Bytes} {h : Header} {multipart : Bool} {offset : Nat} {info : Info}
    (hp : parse b h multipart offset = some info) :
    info.payloadStart ≤ info.payloadEnd ∧ info.payloadEnd ≤ b.size := by
  unfold parse at hp
  cases hr : readHeader b h multipart offset with
  | none => simp [hr] at hp
  | some parsed =>
    rw [hr] at hp
    change (if parsed.payloadStart ≤ parsed.payloadEnd ∧ parsed.payloadEnd ≤ b.size
      then some parsed else none) = some info at hp
    split at hp
    · cases hp
      assumption
    · contradiction

/-- Check coordinates against their offset-table index; tile levels are
    bounded before any level-dependent computation. -/
def coordinatesOK (h : Header) (index : Nat) (info : Info) : Bool :=
  if h.isTiled then
    match h.tileDesc, info.coords with
    | some td, [x, y, lx, ly] =>
      if x.toInt < 0 ∨ y.toInt < 0 ∨ lx.toInt < 0 ∨ ly.toInt < 0 then false else
      let tx := x.toInt.toNat
      let ty := y.toInt.toNat
      let levelX := lx.toInt.toNat
      let levelY := ly.toInt.toNat
      let levels := match td.levelMode with
        | .oneLevel => levelX == 0 && levelY == 0
        | .mipmap => levelX == levelY && levelX < Tiles.mipmapLevelCount td.roundingMode h.width.toNat h.height.toNat
        | .ripmap => levelX < Tiles.numLevels td.roundingMode h.width.toNat && levelY < Tiles.numLevels td.roundingMode h.height.toNat
      if !levels then false else
      let w := Tiles.levelSize td.roundingMode h.width.toNat levelX
      let ht := Tiles.levelSize td.roundingMode h.height.toNat levelY
      tx < Tiles.tilesIn w td.xSize && ty < Tiles.tilesIn ht td.ySize &&
        Tiles.tileIndex td.levelMode td.roundingMode td.xSize td.ySize
          h.width.toNat h.height.toNat tx ty levelX levelY == index
    | _, _ => false
  else
    match info.coords with
    | [y] => y.toInt == h.dataWindow.minY.toInt + (index * h.compression.linesPerBlock : Nat)
    | _ => false

/-- Actual extent of a chunk after coordinate validation. Tiled channels
    have unit sampling by header validation. -/
def extent (h : Header) (index : Nat) (info : Info) : Option (Nat × Nat) :=
  if h.isTiled then
    match h.tileDesc, info.coords with
    | some td, [x, y, lx, ly] =>
      let w := Tiles.levelSize td.roundingMode h.width.toNat lx.toInt.toNat
      let ht := Tiles.levelSize td.roundingMode h.height.toNat ly.toInt.toNat
      some (min td.xSize (w - x.toInt.toNat * td.xSize),
        min td.ySize (ht - y.toInt.toNat * td.ySize))
    | _, _ => none
  else some (h.width.toNat, min h.compression.linesPerBlock
    (h.height.toNat - index * h.compression.linesPerBlock))

/-- Scan one cumulative-count row using widened signed comparisons. -/
private def readCountRowGo (b : Bytes) : Nat → Nat → Nat → Option Nat
  | 0, _, prev => some prev
  | remaining + 1, pos, prev => do
    let count ← getI32LE b pos
    if count.toInt < (prev : Int) then none else
      readCountRowGo b remaining (pos + 4) count.toInt.toNat

/-- Deep tile cumulative counts restart on every row; total samples use Nat. -/
private def readCountRowsGo (b : Bytes) (width : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, total => some total
  | remaining + 1, pos, total => do
    let rowTotal ← readCountRowGo b width pos 0
    readCountRowsGo b width remaining (pos + width * 4) (total + rowTotal)

def readCountRows (b : Bytes) (pos width lines : Nat) : Option Nat :=
  readCountRowsGo b width lines pos 0

theorem count_rows_reset :
    readCountRows (Emit.u32Bytes 1 ++ Emit.u32Bytes 2 ++ Emit.u32Bytes 1 ++ Emit.u32Bytes 2)
      0 2 2 = some 4 := by decide

theorem count_rows_reject_wrap :
    readCountRows (Emit.u32Bytes 2147483647 ++ Emit.u32Bytes 2147483648) 0 2 1 = none := by decide

/-- NONE payload sizes use the sampling-aware row model. Other compression
    payloads remain opaque, with bounds checked by `parse`. -/
def payloadSizeOK (b : Bytes) (h : Header) (index : Nat) (info : Info) : Bool :=
  if h.compression != .none then true else
  match extent h index info with
  | none => false
  | some (width, lines) =>
    if h.isDeep then
      let fullCountBytes := match h.tileDesc with
        | some td => td.xSize * td.ySize * 4
        | none => width * lines * 4
      if info.packedOffsets != width * lines * 4 && info.packedOffsets != fullCountBytes then false else
      match readCountRows b info.payloadStart width lines with
      | none => false
      | some total =>
        let expected := total * pixelSize h.channels
        info.packedSamples == expected && info.unpackedSamples == expected
    else
      let expected := if h.isTiled then width * lines * pixelSize h.channels else
        match info.coords with
        | [y] => sampledBlockBytesFast h.channels h.dataWindow.minX.toInt y.toInt width lines
        | _ => 0
      info.packedSamples == expected

def checkFile (b : Bytes) (f : ParsedFile) : Bool :=
  Parse.checkParts b.size f && f.parts.length == f.offsetTables.length &&
    (f.parts.zip f.offsetTables).zipIdx.all fun ((h, table), part) =>
      table.offsets.zipIdx.all fun (offset, index) =>
        match parse b h f.version.multipart offset with
        | none => false
        | some info =>
          (if f.version.multipart then info.part == some part else info.part.isNone) &&
            coordinatesOK h index info && payloadSizeOK b h index info

end Exr.Chunk
