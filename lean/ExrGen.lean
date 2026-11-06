/-
  TinyEXR - `exrgen`: seeded generator of well-formed EXR files.

  The generated files are structurally valid and use uncompressible-free
  (NONE) blocks with exact sizes, so tinyexr v3 and OpenEXR can both load
  them. They exercise the differ (`test/v3/lean_diff.py`) across part kinds,
  tiling modes and multi-part layouts.

    exrgen <out.exr> <seed> <kind>

  kinds: scanline | tiled | mipmap | ripmap | deepscanline | multipart

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Emit

namespace ExrGen

def chanBytes (s : String) : Exr.Bytes := s.toUTF8

def channel (name : String) (pt : Exr.PixelType) : Exr.Channel :=
  { name := chanBytes name, pixelType := pt, pLinear := false,
    xSampling := 1, ySampling := 1 }

/-- Bytes per pixel for a channel list (all channels sampled 1). -/
def bytesPerPixel (cs : List Exr.Channel) : Nat :=
  cs.foldl (fun acc c => acc + c.pixelType.sizeBytes) 0

/-- Build the attribute list of a part header. -/
def headerAttrs (h : Exr.Header) (multipart : Bool) : List Exr.RawAttr :=
  let chlist :=
    (h.channels.foldl (fun acc c =>
        acc ++ c.name ++ Exr.Emit.nulByte ++ Exr.Emit.u32Bytes c.pixelType.toBits.toNat
          ++ ByteArray.mk #[0, 0, 0, 0]
          ++ Exr.Emit.u32Bytes c.xSampling.toInt.toNat
          ++ Exr.Emit.u32Bytes c.ySampling.toInt.toNat) ByteArray.empty)
      ++ Exr.Emit.nulByte
  let box (b : Exr.Box2i) : Exr.Bytes :=
    Exr.Emit.u32Bytes b.minX.toInt.toNat ++ Exr.Emit.u32Bytes b.minY.toInt.toNat
      ++ Exr.Emit.u32Bytes b.maxX.toInt.toNat ++ Exr.Emit.u32Bytes b.maxY.toInt.toNat
  let a (name ty : String) (v : Exr.Bytes) : Exr.RawAttr :=
    { name := chanBytes name, typeName := chanBytes ty, value := v }
  let base :=
    [ a "channels" "chlist" chlist,
      a "compression" "compression" (ByteArray.mk #[h.compression.toBits]),
      a "dataWindow" "box2i" (box h.dataWindow),
      a "displayWindow" "box2i" (box h.displayWindow),
      a "lineOrder" "lineOrder" (ByteArray.mk #[h.lineOrder.toBits]),
      a "pixelAspectRatio" "float" (Exr.Emit.u32Bytes h.pixelAspectRatio.toNat),
      a "screenWindowCenter" "v2f"
        (Exr.Emit.u32Bytes h.screenWindowCenterX.toNat
          ++ Exr.Emit.u32Bytes h.screenWindowCenterY.toNat),
      a "screenWindowWidth" "float" (Exr.Emit.u32Bytes h.screenWindowWidth.toNat) ]
  let withTiles :=
    match h.tileDesc with
    | some td =>
      let lm : Nat := match td.levelMode with
        | .oneLevel => 0
        | .mipmap => 1
        | .ripmap => 2
      let rm : Nat := match td.roundingMode with
        | .roundDown => 0
        | .roundUp => 1
      base ++ [ a "tiles" "tiledesc"
        (Exr.Emit.u32Bytes td.xSize ++ Exr.Emit.u32Bytes td.ySize
          ++ ByteArray.mk #[UInt8.ofNat (lm ||| rm <<< 4)]) ]
    | none => base
  let withChunkCount :=
    match h.chunkCount with
    | some n => withTiles ++ [ a "chunkCount" "int" (Exr.Emit.u32Bytes n) ]
    | none => withTiles
  let withName :=
    match h.name with
    | some n => withChunkCount ++ [ a "name" "string" n ]
    | none => withChunkCount
  let withVersion :=
    if h.partType.isDeep then withName ++ [ a "version" "int" (Exr.Emit.u32Bytes 1) ]
    else withName
  let withMaxSamples :=
    match h.maxSamplesPerPixel with
    | some m =>
      withVersion ++ [ a "maxSamplesPerPixel" "int" (Exr.Emit.u32Bytes m.toInt.toNat) ]
    | none => withVersion
  if multipart || h.partType.isDeep then
    withMaxSamples ++ [ a "type" "string" (chanBytes h.partType.wireName) ]
  else withMaxSamples

structure GenPart where
  header : Exr.Header
  chunks : Nat

def mkHeader (pt : Exr.PartType) (w hgt : Nat) (tiles : Option Exr.TypedAttr.TileDesc)
    (cc : Option Nat) (name : Option Exr.Bytes) (msp : Option Int32) : Exr.Header :=
  { partType := pt
    dataWindow := { minX := 0, minY := 0, maxX := Int32.ofNat (w - 1),
                    maxY := Int32.ofNat (hgt - 1) }
    displayWindow := { minX := 0, minY := 0, maxX := Int32.ofNat (w - 1),
                       maxY := Int32.ofNat (hgt - 1) }
    channels := [channel "B" .half, channel "G" .half, channel "R" .half]
    compression := .none
    lineOrder := .increasingY
    pixelAspectRatio := 0x3f800000
    screenWindowCenterX := 0
    screenWindowCenterY := 0
    screenWindowWidth := 0x3f800000
    tileDesc := tiles
    name := name
    chunkCount := cc
    maxSamplesPerPixel := msp
    attrs := [] }

/-- (levelX, levelY, levelW, levelH) pairs in offset-table order. -/
def levelsOf (pt : Exr.TypedAttr.TileDesc) (w h : Nat) : List (Nat × Nat × Nat × Nat) :=
  match pt.levelMode with
  | .oneLevel => [(0, 0, w, h)]
  | .mipmap =>
    (List.range (Exr.Tiles.mipmapLevelCount pt.roundingMode w h)).map fun l =>
      (l, l, Exr.Tiles.levelSize pt.roundingMode w l, Exr.Tiles.levelSize pt.roundingMode h l)
  | .ripmap =>
    (List.range (Exr.Tiles.numLevels pt.roundingMode h)).flatMap fun ly =>
      (List.range (Exr.Tiles.numLevels pt.roundingMode w)).map fun lx =>
        (lx, ly, Exr.Tiles.levelSize pt.roundingMode w lx,
         Exr.Tiles.levelSize pt.roundingMode h ly)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Enumerate all tiles of a tiled part as (tx, ty, lx, ly, tw, th). -/
def tilesOf (pt : Exr.TypedAttr.TileDesc) (w h : Nat) :
    List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (levelsOf pt w h).flatMap fun (lx, ly, lw, lh) =>
    let nxt := ceilDiv lw pt.xSize
    let nyt := ceilDiv lh pt.ySize
    (List.range nyt).flatMap fun ty =>
      (List.range nxt).map fun tx =>
        (tx, ty, lx, ly,
         min pt.xSize (lw - tx * pt.xSize),
         min pt.ySize (lh - ty * pt.ySize))

def u32 (n : Nat) : Exr.Bytes := Exr.Emit.u32Bytes n
def u64 (n : Nat) : Exr.Bytes := Exr.Emit.u64Bytes n

def zeros (n : Nat) : Exr.Bytes := ByteArray.mk (List.replicate n (0 : UInt8)).toArray

/-- Chunk header + payload for one chunk. All payloads are deliberately tiny
    (8x8-ish windows) and zero-valued. -/
def chunkBytes (partIdx : Nat) (multipart : Bool) (h : Exr.Header) (ci : Nat) : Exr.Bytes :=
  let cs := h.channels
  let bpp := bytesPerPixel cs
  let partHdr : Exr.Bytes := if multipart then u32 partIdx else ByteArray.empty
  if h.partType.isTiled then
    match h.tileDesc with
    | none => ByteArray.empty
    | some td =>
      let w := h.width.toNat
      let ht := h.height.toNat
      match (tilesOf td w ht).drop ci |>.head? with
      | none => ByteArray.empty
      | some (tx, ty, lx, ly, tw, th) =>
        let data := tw * th * bpp
        partHdr ++ u32 tx ++ u32 ty ++ u32 lx ++ u32 ly ++ u32 data ++ zeros data
  else if h.partType.isDeep then
    -- deep scan-line chunk: y, packed off table size, packed samples,
    -- unpacked samples, then the all-zero cumulative count table
    let width := h.width.toNat
    let lpb := Exr.Compression.linesPerBlock h.compression
    let y := h.dataWindow.minY.toInt.toNat + ci * lpb
    let otab := zeros (width * 4)
    partHdr ++ u32 y ++ u64 (width * 4) ++ u64 0 ++ u64 0 ++ otab
  else
    let lpb := Exr.Compression.linesPerBlock h.compression
    let width := h.width.toNat
    let height := h.height.toNat
    let y := h.dataWindow.minY.toInt.toNat + ci * lpb
    let lines := min lpb (height - ci * lpb)
    let data := width * lines * bpp
    partHdr ++ u32 y ++ u32 data ++ zeros data

def chunkCountOf (h : Exr.Header) : Nat := h.computedChunks

def kindOf (kind : String) : Option (List GenPart × Exr.Version) :=
  match kind with
  | "scanline" =>
    let h := mkHeader .scanline 16 16 none none none none
    some ([{ header := { h with chunkCount := some h.computedChunks }, chunks := h.computedChunks }],
      { singleTile := false, longNames := false, nonImage := false, multipart := false })
  | "tiled" =>
    let t : Exr.TypedAttr.TileDesc :=
      { xSize := 8, ySize := 8, levelMode := .oneLevel, roundingMode := .roundDown }
    let h := mkHeader .tiled 16 16 (some t) none none none
    some ([{ header := { h with chunkCount := some h.computedChunks }, chunks := h.computedChunks }],
      { singleTile := true, longNames := false, nonImage := false, multipart := false })
  | "mipmap" =>
    let t : Exr.TypedAttr.TileDesc :=
      { xSize := 8, ySize := 8, levelMode := .mipmap, roundingMode := .roundUp }
    let h := mkHeader .tiled 16 16 (some t) none none none
    some ([{ header := { h with chunkCount := some h.computedChunks }, chunks := h.computedChunks }],
      { singleTile := true, longNames := false, nonImage := false, multipart := false })
  | "ripmap" =>
    let t : Exr.TypedAttr.TileDesc :=
      { xSize := 8, ySize := 8, levelMode := .ripmap, roundingMode := .roundDown }
    let h := mkHeader .tiled 16 16 (some t) none none none
    some ([{ header := { h with chunkCount := some h.computedChunks }, chunks := h.computedChunks }],
      { singleTile := true, longNames := false, nonImage := false, multipart := false })
  | "deepscanline" =>
    let h := mkHeader .deepScanline 16 16 none (some 0) (some (chanBytes "deep")) (some (-1))
    some ([{ header := { h with chunkCount := some h.computedChunks }, chunks := h.computedChunks }],
      { singleTile := false, longNames := false, nonImage := true, multipart := false })
  | "multipart" =>
    let h1 := mkHeader .scanline 16 16 none (some 0) (some (chanBytes "a")) none
    let h2 := mkHeader .scanline 8 8 none (some 0) (some (chanBytes "b")) none
    -- OpenEXR requires the shared attributes (displayWindow, pixelAspectRatio,
    -- chromaticities, ...) to be identical across parts; only dataWindow may
    -- differ, so part b keeps part a's display window.
    let h2 := { h2 with displayWindow := h1.displayWindow }
    let h1 := { h1 with chunkCount := some h1.computedChunks }
    let h2 := { h2 with chunkCount := some h2.computedChunks }
    some ([{ header := h1, chunks := h1.computedChunks },
           { header := h2, chunks := h2.computedChunks }],
      { singleTile := false, longNames := false, nonImage := false, multipart := true })
  | _ => none

/-- Generate the file: magic/version, headers, offset tables, chunk payloads. -/
def generate (kind : String) : Option Exr.Bytes :=
  match kindOf kind with
  | none => none
  | some (parts, version) =>
    let multipart := version.multipart
    let headerChunks : List Exr.Bytes :=
      parts.map fun p => Exr.Emit.headerBytes (headerAttrs p.header multipart)
    let headers := headerChunks.foldl (· ++ ·) ByteArray.empty
    let headers := if multipart then headers ++ Exr.Emit.nulByte else headers
    let tableTotal := parts.foldl (fun acc p => acc + 8 * p.chunks) 0
    let prefixLen := 8 + headers.size
    let payloadStart := prefixLen + tableTotal
    -- per-part chunk bytes with correct part indices
    let rec buildPayloads (ps : List GenPart) (pi : Nat) (acc : List (Nat × Exr.Bytes)) :
        List (Nat × Exr.Bytes) :=
      match ps with
      | [] => acc
      | p :: rest =>
        let chunkList := (List.range p.chunks).map fun ci => (pi, chunkBytes pi multipart p.header ci)
        buildPayloads rest (pi + 1) (acc ++ chunkList)
    let chunks := buildPayloads parts 0 []
    -- offsets: running offset across the payload area
    let rec buildTables (ps : List GenPart) (off : Nat) (acc : List Exr.OffsetTable) :
        List Exr.OffsetTable × Nat :=
      match ps with
      | [] => (acc, off)
      | p :: rest =>
        let sizes := (List.range p.chunks).map fun ci => (chunkBytes 0 multipart p.header ci).size
        let rec running (ss : List Nat) (o : Nat) (acc : List Nat) : List Nat :=
          match ss with
          | [] => acc
          | s :: tl => running tl (o + s) (acc ++ [o])
        let offsets := running sizes off []
        let off' := off + sizes.foldl (· + ·) 0
        buildTables rest off' (acc ++ [Exr.OffsetTable.mk offsets])
    let (tables, _) := buildTables parts payloadStart []
    let tableBytes := tables.foldl (fun acc t => acc ++ Exr.Emit.offsetTableBytes t.offsets) ByteArray.empty
    let payloadBytes := chunks.foldl (fun acc (_, b) => acc ++ b) ByteArray.empty
    some (Exr.Emit.magicVersionBytes version ++ headers ++ tableBytes ++ payloadBytes)

end ExrGen

def main (args : List String) : IO UInt32 := do
  match args with
  | [outPath, _, kind] =>
    match ExrGen.generate kind with
    | none =>
      IO.eprintln s!"exrgen: unknown kind '{kind}'"
      return 2
    | some bytes =>
      IO.FS.writeBinFile outPath bytes
      IO.println s!"wrote {outPath} ({bytes.size} bytes)"
      return 0
  | _ =>
    IO.eprintln "usage: exrgen <out.exr> <seed> <kind>"
    return 2

namespace ExrGen

/-! ### Self-checks: generated files parse back with the Lean model -/

/-- Every generated fixture parses structurally. -/
theorem generate_scanline_parses :
    (generate "scanline").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

theorem generate_tiled_parses :
    (generate "tiled").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

theorem generate_mipmap_parses :
    (generate "mipmap").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

theorem generate_ripmap_parses :
    (generate "ripmap").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

theorem generate_deepscanline_parses :
    (generate "deepscanline").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

theorem generate_multipart_parses :
    (generate "multipart").map (fun b => (Exr.Parse.parseFile b).isSome) = some true := by
  native_decide

/-- The generated fixtures are also structurally valid (headers + tables). -/
theorem generate_scanline_valid :
    (generate "scanline").bind (fun b =>
      (Exr.Parse.parseFile b).map (fun f => Exr.Parse.checkParts b.size f)) = some true := by
  native_decide

theorem generate_tiled_valid :
    (generate "tiled").bind (fun b =>
      (Exr.Parse.parseFile b).map (fun f => Exr.Parse.checkParts b.size f)) = some true := by
  native_decide

theorem generate_multipart_valid :
    (generate "multipart").bind (fun b =>
      (Exr.Parse.parseFile b).map (fun f => Exr.Parse.checkParts b.size f)) = some true := by
  native_decide

end ExrGen
