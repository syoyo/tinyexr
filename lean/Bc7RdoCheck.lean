/-
  TinyEXR - BC7 RDO pass differential checker (C vs Lean).

  Reads vectors emitted by `test/v3/bc7_rdo_vectors.c`
  (`G <rdo> <nblocks>` groups of `B <src> <pre> <post>`) and compares
  `Texcomp.bc7RdoPass` with the C `tc_bc7_rdo_pass`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Bc7Rdo

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexVal c) 0

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

def parseHexBytes (s : String) : List Nat :=
  (List.range (s.length / 2)).map (fun i =>
    hexNat (((s.drop (i * 2)).take 2).toString))

structure RdoAcc where
  rdo : Nat := 0
  started : Bool := false
  srcs : List (List Nat) := []
  encs : List (List Nat) := []
  wants : List (List Nat) := []
  bad : Nat := 0
  blocks : Nat := 0

/-- Run the pass for the group collected so far and count mismatching blocks. -/
def flush (a : RdoAcc) : RdoAcc :=
  if !a.started then a
  else
    let got := bc7RdoPass a.srcs a.encs a.rdo
    let mism := (List.range a.srcs.length).foldl (fun acc i =>
      if got.getD i [] == a.wants.getD i [] then acc else acc + 1) 0
    { a with srcs := [], encs := [], wants := [], bad := a.bad + mism }

def step (a : RdoAcc) (line : String) : RdoAcc :=
  if line.startsWith "G" then
    let a := flush a
    let f := fields line
    { a with rdo := decNat (f.getD 1 "0"), started := true }
  else if line.startsWith "B" then
    let f := fields line
    { a with srcs := a.srcs ++ [parseHexBytes (f.getD 1 "")],
             encs := a.encs ++ [parseHexBytes (f.getD 2 "")],
             wants := a.wants ++ [parseHexBytes (f.getD 3 "")],
             blocks := a.blocks + 1 }
  else a

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/bc7_rdo_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let final := flush (lines.foldl step {})
  IO.println s!"{final.blocks} blocks checked in RDO groups, {final.bad} mismatches"
  if final.bad != 0 then
    throw (IO.userError "bc7 rdo mismatch")
