/-
  TinyEXR - tir streaming trace differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tir.Streaming

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def rcOf (n : Int) : Tir.StreamRc :=
  if n == 0 then .ok else if n == 1 then .wouldBlock else .error

structure CheckAcc where
  cap : Nat := 0
  height : Nat := 0
  starts : List (Nat × Nat) := []
  st : Tir.StreamState := Tir.newStream 0 0
  bad : Nat := 0
  parity : Bool := false

def parseStarts (fs : List String) : List (Nat × Nat) :=
  match fs with
  | "start" :: a :: b :: rest => (a.toNat!, b.toNat!) :: parseStarts rest
  | _ => []

def neededRows (starts : List (Nat × Nat)) (d : Nat) : List Nat :=
  match starts.getD d (0, 0) with
  | (s, n) => (List.range n).map (fun k => s + k)

def stepTrace (acc : CheckAcc) (line : String) : CheckAcc :=
  let f := fields line
  match f with
  | "cfg" :: sh :: _dh :: cap :: _ :: _ :: _ =>
      let c := cap.toNat!
      let h := sh.toNat!
      { cap := c, height := h, starts := [], st := Tir.newStream c h,
        bad := acc.bad, parity := acc.parity }
  | "start" :: _ :: _ :: _rest =>
      { acc with starts := acc.starts ++ parseStarts f }
  | "trace" :: op :: arg :: rc :: rest =>
      let wantRing := (rest.take acc.cap).map (fun s => s.toInt!)
      let wantCur := (rest.getD acc.cap "0").toNat!
      let (modelRc, st') :=
        if op == "P" then
          let y := arg.toNat!
          let guard := (acc.starts.getD acc.st.curDst (0, 0)).1
          Tir.pushRow acc.st y y guard
        else
          Tir.pullRow acc.st (neededRows acc.starts acc.st.curDst)
      let ok := modelRc == rcOf rc.toInt! &&
        st'.ringSrcY == wantRing && st'.curDst == wantCur &&
        (Tir.resident st').length ≤ st'.ringCap
      { acc with st := st', bad := acc.bad + (if ok then 0 else 1) }
      -- diagnostics are emitted in main via a separate pass
  | "parity" :: v :: _ :: _ =>
      { acc with parity := acc.parity || v == "1" }
  | _ => acc

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/tir_streaming_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let acc := ls.foldl stepTrace {}
  IO.println s!"{ls.length} streaming trace lines checked, {acc.bad} mismatches, parity={acc.parity}"
  if acc.bad != 0 || !acc.parity then
    throw (IO.userError "tir streaming differential mismatch")
