/-
  TinyEXR - Lean 4 formalization of the ASTC encoder's partition cache.

  Ports `tc_astc_hash52`, `tc_astc_select_partition`,
  `tc_astc_canonical_partition_map` and `tc_astc_build_partition_cache`
  from `tools/texcomp/src/texcomp_astc.c`: the 1024 candidate seeds per
  partition count are turned into texel maps, seeds that leave a partition
  empty are dropped, and seeds whose canonical (first-appearance-relabelled)
  map duplicates an earlier seed are dropped too.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcBlockMode

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_hash52` in 32-bit wrapping arithmetic. -/
def astcHash52 (inp0 : Nat) : Nat :=
  let inp := (inp0 ^^^ (inp0 >>> 15)) &&& 0xFFFFFFFF
  let inp := (inp * 0xEEDE0891) &&& 0xFFFFFFFF
  let inp := (inp ^^^ (inp >>> 5)) &&& 0xFFFFFFFF
  let inp := (inp + (inp <<< 16)) &&& 0xFFFFFFFF
  let inp := (inp ^^^ (inp >>> 7)) &&& 0xFFFFFFFF
  let inp := (inp ^^^ (inp >>> 3)) &&& 0xFFFFFFFF
  let inp := (inp ^^^ (inp <<< 6)) &&& 0xFFFFFFFF
  (inp ^^^ (inp >>> 17)) &&& 0xFFFFFFFF

/-- `tc_astc_select_partition`: partition index for one texel. -/
def astcSelectPartition (seed0 x0 y0 pc : Nat) (small : Bool) : Nat :=
  let x := if small then x0 * 2 else x0
  let y := if small then y0 * 2 else y0
  let seed := (seed0 + (pc - 1) * 1024) &&& 0xFFFFFFFF
  let rnum := astcHash52 seed
  let nib := fun (k : Nat) => (rnum >>> k) &&& 15
  let seed1 := nib 0 * nib 0
  let seed2 := nib 4 * nib 4
  let seed3 := nib 8 * nib 8
  let seed4 := nib 12 * nib 12
  let seed5 := nib 16 * nib 16
  let seed6 := nib 20 * nib 20
  let seed7 := nib 24 * nib 24
  let seed8 := nib 28 * nib 28
  let seed9 := nib 18 * nib 18
  let seed10 := nib 22 * nib 22
  let seed11 := nib 26 * nib 26
  let seed12 := ((rnum >>> 30) ||| (rnum <<< 2)) &&& 15
  let seed12 := seed12 * seed12
  let (sh1, sh2) :=
    if seed &&& 1 != 0 then
      ((if seed &&& 2 != 0 then 4 else 5), (if pc == 3 then 6 else 5))
    else
      ((if pc == 3 then 6 else 5), (if seed &&& 2 != 0 then 4 else 5))
  let sh3 := if seed &&& 0x10 != 0 then sh1 else sh2
  let a := ((seed1 >>> sh1) * x + (seed2 >>> sh2) * y + (rnum >>> 14)) &&& 63
  let b := ((seed3 >>> sh1) * x + (seed4 >>> sh2) * y + (rnum >>> 10)) &&& 63
  let c := ((seed5 >>> sh1) * x + (seed6 >>> sh2) * y + (rnum >>> 6)) &&&
    (if pc > 2 then 63 else 0)
  let d := ((seed7 >>> sh1) * x + (seed8 >>> sh2) * y + (rnum >>> 2)) &&&
    (if pc > 3 then 63 else 0)
  let _ := (seed9 >>> sh3, seed10 >>> sh3, seed11 >>> sh3, seed12 >>> sh3)
  if a ≥ b && a ≥ c && a ≥ d then 0
  else if b ≥ c && b ≥ d then 1
  else if c ≥ d then 2
  else 3

/-- `tc_astc_canonical_partition_map`: first-appearance relabelling plus the
  FNV-style digest C uses for the duplicate pre-check. -/
def astcCanonicalMap (map : List Nat) : List Nat × Nat :=
  let step (st : List Nat × Nat × List Nat × Nat) (p : Nat) :=
    let (remap, next, canon, h) := st
    let cur := remap.getD p 0xFF
    let (remap, next, p') :=
      if cur == 0xFF then (remap.set p next, next + 1, next) else (remap, next, cur)
    let h := ((h ^^^ p') * 16777619) &&& 0xFFFFFFFF
    (remap, next, canon ++ [p'], h)
  let (_, _, canon, h) := map.foldl step ([0xFF, 0xFF, 0xFF, 0xFF], 0, [], 2166136261)
  (canon, h)

/-- Partition-of-texel map for one seed, with the cache's clamp of
  out-of-range partition indices. -/
def astcPartitionMap (blockX blockY pc seed : Nat) : List Nat :=
  let texelCount := blockX * blockY
  let small := texelCount < 32
  (List.range texelCount).map (fun i =>
    let part := astcSelectPartition seed (i % blockX) (i / blockX) pc small
    if part ≥ pc then pc - 1 else part)

/-- FNV digest of a seed's partition map (the gate's compact primitive check). -/
def astcPartitionDigest (blockX blockY pc seed : Nat) : Nat :=
  (astcPartitionMap blockX blockY pc seed).foldl (fun h p =>
    ((h ^^^ p) * 16777619) &&& 0xFFFFFFFF) 2166136261

/-- One kept cache entry: `(seed, map, counts, bitmap)`. -/
abbrev AstcPartitionEntry := Nat × List Nat × List Nat × List Nat

/-- `tc_astc_build_partition_cache`: the deduplicated seed list for one
  footprint and partition count. The canonical maps and their digests are
  kept alongside the entries while building so the duplicate test is the
  same `memcmp`-style comparison the C uses. -/
def astcBuildPartitionCache (blockX blockY pc : Nat) : List AstcPartitionEntry :=
  let texelCount := blockX * blockY
  let seedStep (st : List AstcPartitionEntry × List Nat × List (List Nat)) (seed : Nat) :=
    let (entries, hashes, canons) := st
    let map := astcPartitionMap blockX blockY pc seed
    let counts := (List.range 4).map (fun p => (map.filter (fun q => q == p)).length)
    if !(List.range pc).all (fun p => counts.getD p 0 != 0) then st
    else
      let (canon, hash) := astcCanonicalMap map
      let dup := (List.range entries.length).any (fun i =>
        hashes.getD i 0 == hash && canons.getD i [] == canon)
      if dup then st
      else
        let bits :=
          if pc == 2 then
            (List.range texelCount).foldl (fun (acc : List Nat) i =>
              if map.getD i 0 != 0 then
                acc.set (i / 64) (acc.getD (i / 64) 0 ||| (1 <<< (i % 64)))
              else acc) [0, 0, 0]
          else [0, 0, 0]
        (entries ++ [(seed, map, counts, bits)], hashes ++ [hash], canons ++ [canon])
  ((List.range 1024).foldl seedStep ([], [], [])).1

end Texcomp
