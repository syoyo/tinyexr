/-
  TinyEXR - `exrcheck`: structural conformance checker backed by the Lean
  formalization.

  Prints a machine-readable report (one record per line) for the Python
  differ (`test/v3/lean_diff.py`):

    file <path>
    file-ok <true|false> <parts>
    part <index> <type> <tiled> <deep> <chunks> <declared> <tableLen>
    part-window <index> <minX> <minY> <maxX> <maxY>
    part-tile <index> <xSize> <ySize> <levelMode> <roundingMode>
    part-channels <index> <count> <sorted>
    file-error <message>

  Exit code: 0 if the file parses and all parts validate, 1 otherwise.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Chunk

open System

namespace ExrCheck

def partTypeName : Exr.PartType → String
  | .scanline => "scanlineimage"
  | .tiled => "tiledimage"
  | .deepScanline => "deepscanline"
  | .deepTiled => "deeptile"

def levelModeName : Exr.TypedAttr.LevelMode → String
  | .oneLevel => "one"
  | .mipmap => "mipmap"
  | .ripmap => "ripmap"

def roundingModeName : Exr.TypedAttr.RoundingMode → String
  | .roundDown => "down"
  | .roundUp => "up"

def declaredOrComputed (h : Exr.Header) : Nat :=
  match h.chunkCount with
  | some n => n
  | none => h.computedChunks

def reportPart (idx : Nat) (h : Exr.Header) (t : Option Exr.OffsetTable) : IO Unit := do
  let tableLen := match t with
    | some t => t.offsets.length
    | none => 0
  IO.println s!"part {idx} {partTypeName h.partType} {h.isTiled} {h.isDeep} \
      {h.computedChunks} {declaredOrComputed h} {tableLen}"
  IO.println s!"COMPRESSION {idx} {h.compression.toBits.toNat}"
  let tile := match h.tileDesc with
    | none => "none"
    | some td =>
      let mode := match td.levelMode with | .oneLevel => 0 | .mipmap => 1 | .ripmap => 2
      let rounding := match td.roundingMode with | .roundDown => 0 | .roundUp => 1
      s!"{td.xSize} {td.ySize} {mode} {rounding}"
  IO.println s!"TILE {idx} {tile}"
  for (channel, ci) in h.channels.zipIdx do
    let name := String.intercalate "." (channel.name.data.toList.map fun b => toString b.toNat)
    IO.println s!"CHANNEL {idx} {ci} {name} {channel.pixelType.toBits.toNat} {if channel.pLinear then 1 else 0} {channel.xSampling.toInt} {channel.ySampling.toInt}"
  IO.println s!"part-window {idx} {h.dataWindow.minX} {h.dataWindow.minY} \
      {h.dataWindow.maxX} {h.dataWindow.maxY}"
  match h.tileDesc with
  | some td =>
    IO.println s!"part-tile {idx} {td.xSize} {td.ySize} \
        {levelModeName td.levelMode} {roundingModeName td.roundingMode}"
  | none => IO.println s!"part-tile {idx} none"
  IO.println s!"part-channels {idx} {h.channels.length} \
      {decide (Exr.Channel.StrictlySorted h.channels)}"

def run (path : String) (strictShared : Bool) (checkChunks : Bool := false) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"file {path}"
  match Exr.Parse.parseFile bytes with
  | none =>
    IO.println "file-ok false 0"
    IO.println "file-error parse"
    return 1
  | some f =>
    let ok :=
      if strictShared then Exr.Parse.checkPartsOpenEXR bytes.size f
      else Exr.Parse.checkParts bytes.size f
    let ok := ok && (if checkChunks then Exr.Chunk.checkFile bytes f else true)
    IO.println s!"file-ok {ok} {f.parts.length}"
    let mut idx := 0
    for (h, t) in f.parts.zip f.offsetTables do
      reportPart idx h t
      idx := idx + 1
    if !ok then
      IO.println "file-error validation"
      return 1
    return 0

end ExrCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => ExrCheck.run path false
  | ["--strict", path] => ExrCheck.run path true
  | ["--chunks", path] => ExrCheck.run path false true
  | ["--strict", "--chunks", path] => ExrCheck.run path true true
  | _ =>
    IO.eprintln "usage: exrcheck [--strict] [--chunks] <file.exr>  (--strict = OpenEXR shared-attribute rule)"
    return 2
