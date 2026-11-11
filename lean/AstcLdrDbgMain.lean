/-
  TinyEXR - ASTC LDR debug driver: replays one vector line and prints the
  Lean decision trace. Debug tool; not part of the gate.
-/
import Texcomp.AstcLdrDbg

open Texcomp

set_option linter.unusedVariables false

def decNat (s : String) : Nat := s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")
def natAt (xs : List String) (i : Nat) : Nat := decNat (xs.getD i "0")
def valsFrom (xs : List String) (start n : Nat) : List Nat := (List.range n).map (fun i => natAt xs (start + i))
def blockFrom (xs : List String) (start count : Nat) : List (List Nat) := (List.range count).map (fun i => valsFrom xs (start + i * 4) 4)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/astc_ldr_vectors.txt"
  let wantLine := args.getD 1 "5"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  for (idx, line) in List.zip (List.range lines.length) lines do
    if toString (idx + 1) != wantLine then continue
    let sections := line.splitOn "|"
    let head := fields (sections.getD 0 "")
    let bx := natAt head 1
    let by_ := natAt head 2
    let quality := natAt head 3
    let count := bx * by_
    let block := blockFrom head 4 count
    let (got, log) := astcEncodeLdrBlockDbg block count quality bx by_
    log.forM IO.println
    IO.println s!"DBG out {got}"
