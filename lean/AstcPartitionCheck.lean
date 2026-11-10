/-
  TinyEXR - ASTC partition-cache differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/astc_partition_vectors.c`
  (`S` per-seed digests, `P`/`E` cache entries) and compares
  `Texcomp.astcPartitionDigest` / `astcBuildPartitionCache` with the C
  `tc_astc_select_partition` / `tc_astc_build_partition_cache`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcPartition

open Texcomp

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")

/-- Decode a hex string of single-digit bytes. -/
def parseHexBytes (s : String) : List Nat :=
  (List.range (s.length / 2)).map (fun i => hexNat (((s.drop (i * 2)).take 2).toString))

def emptyEntry : AstcPartitionEntry := (0, ([] : List Nat), ([] : List Nat), ([] : List Nat))

structure CacheAcc where
  bx : Nat := 0
  bh : Nat := 0
  pc : Nat := 0
  want : List AstcPartitionEntry := []
  started : Bool := false
  bad : Nat := 0
  entries : Nat := 0
  note : String := ""

/-- Run the cache build for the group collected so far; returns the number of
  differing entries (and resets the group). -/
def flushCache (a : CacheAcc) : CacheAcc × Nat :=
  if !a.started then (a, 0)
  else
    let got := astcBuildPartitionCache a.bx a.bh a.pc
    -- C only writes `partition_texel_count[p]` for `p < pc` and never reads
    -- the rest, so compare just those entries.
    let entryEq : AstcPartitionEntry → AstcPartitionEntry → Bool := fun g w =>
      g.1 == w.1 && g.2.1 == w.2.1 && g.2.2.2 == w.2.2.2 &&
        (g.2.2.1.take a.pc) == w.2.2.1
    let mism :=
      (List.range (max got.length a.want.length)).foldl (fun acc i =>
        if entryEq (List.getD got i emptyEntry) (List.getD a.want i emptyEntry) then acc
        else acc + 1) 0
    let dbg := if mism != 0 then
        let g0 := List.getD got 0 emptyEntry
        let w0 := List.getD a.want 0 emptyEntry
        s!" first: lean {repr g0} c {repr w0}"
      else ""
    ({ a with want := [], started := false, bad := a.bad + mism,
              entries := a.entries + a.want.length, note := dbg }, mism)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_partition_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut seeds := 0
  let mut cache : CacheAcc := {}
  let seedLines := lines.filter (fun l => l.startsWith "S")
  let cacheLines := lines.filter (fun l => !l.startsWith "S")
  for (idx, line) in List.zip (List.range seedLines.length) seedLines do
    let f := fields line
    let bx := natAt f 1
    let bh := natAt f 2
    let pc := natAt f 3
    let seed := natAt f 4
    let want := natAt f 5
    let got := astcPartitionDigest bx bh pc seed
    if got != want then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} S {bx}x{bh} pc {pc} seed {seed}: got {got}, want {want}"
    seeds := seeds + 1
  for line in cacheLines do
    let sections := line.splitOn "|"
    let f := fields (sections.getD 0 "")
    if f.getD 0 "" == "P" then
      let (c1, m1) := flushCache cache
      if m1 != 0 then
        IO.eprintln s!"cache {cache.bx}x{cache.bh} pc {cache.pc}: {m1} entries differ{c1.note}"
      cache := { c1 with bx := natAt f 1, bh := natAt f 2, pc := natAt f 3,
                         started := true }
    else if f.getD 0 "" == "E" then
      let seed := natAt f 1
      let map := parseHexBytes (f.getD 2 "")
      let counts := (List.range cache.pc).map (fun i => natAt (fields (sections.getD 1 "")) i)
      let bits := (List.range 3).map (fun i => natAt (fields (sections.getD 2 "")) i)
      cache := { cache with want := cache.want ++ [(seed, map, counts, bits)] }
  let (c2, m2) := flushCache cache
  if m2 != 0 then
    IO.eprintln s!"cache {cache.bx}x{cache.bh} pc {cache.pc}: {m2} entries differ"
  let totalBad := bad + c2.bad
  IO.println s!"{seeds} seed digests + {c2.entries} cache entries checked, {totalBad} mismatches"
  if totalBad != 0 then
    throw (IO.userError "astc partition mismatch")
