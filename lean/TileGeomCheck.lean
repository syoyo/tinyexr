/-
  TinyEXR - tile-geometry differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.TileGeom

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 3 then true else
  let v := (f.getD 0 "0").toInt!
  let d := (f.getD 1 "0").toInt!
  let want := (f.getD 2 "0").toInt!
  Exr.ceilDivPos v d == want

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tile_geom_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} tile-geometry vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "tile geometry differential mismatch")
