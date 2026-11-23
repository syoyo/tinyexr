/-
  TinyEXR - shared header-validator differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.HeaderValidate

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def chans (xs : List String) : List Exr.ChanView :=
  match xs with
  | a :: b :: c :: d :: e :: rest =>
      { nameLen := a.toNat!, pixelType := b.toInt!, xSampling := c.toInt!,
        ySampling := d.toInt!, pLinear := e.toInt! } :: chans rest
  | _ => []

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 23 then true else
  let v := (f.take 24).map (fun s => s.toInt!)
  let h : Exr.HeaderView :=
    { numChannels := v.getD 0 0 |>.toNat
      channelsPresent := v.getD 1 0 == 1
      partType := v.getD 2 0
      compression := v.getD 3 0
      lineOrder := v.getD 4 0
      minX := v.getD 5 0
      maxX := v.getD 6 0
      minY := v.getD 7 0
      maxY := v.getD 8 0
      displayMinX := v.getD 9 0
      displayMaxX := v.getD 10 0
      displayMinY := v.getD 11 0
      displayMaxY := v.getD 12 0
      pixelAspectRatio := if v.getD 14 0 == 1 then 1 else 0
      screenWidth := if v.getD 15 0 == 1 then 1 else -1
      finiteFloats := v.getD 13 0 == 1
      tiled := v.getD 17 0 == 1
      tileX := (v.getD 18 0).toNat
      tileY := (v.getD 19 0).toNat
      levelMode := v.getD 20 0
      roundingMode := v.getD 21 0
      nameLen := (v.getD 22 0).toNat
      channels := chans (f.drop 24) }
  Exr.headerValid h == (v.getD 23 0 == 1)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/header_validate_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 8 then IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} header-validation vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "header validation differential mismatch")
