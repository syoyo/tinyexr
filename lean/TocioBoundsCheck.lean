/-
  TinyEXR - tocio loader-bounds differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.LoaderBoundsCsp
import Tocio.YamlFuelExact

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def checkLine (line : String) : Bool :=
  let f := fields line
  if f.length < 3 then true else
  let count := (f.getD 0 "0").toNat!
  let avail := (f.getD 1 "0").toNat!
  let want := (f.getD 2 "0") == "1"
  Tocio.spiValuesFit count avail == want

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tocio_bounds_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 5 then IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} tocio loader-bound vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "loader bounds differential mismatch")
