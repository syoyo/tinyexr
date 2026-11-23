/-
  TinyEXR - image-budget differential checker (C vs Lean).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.ImageBudget

def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def chans : List Int → List Exr.BudgetChan
  | a :: b :: c :: rest =>
      { xSampling := a.toNat, ySampling := b.toNat, pixelType := c.toNat } :: chans rest
  | _ => []

def checkLine (line : String) : Bool :=
  let v := (fields line).map (fun s => s.toInt!)
  if v.length < 4 then true else
  let w := v.getD 0 0 |>.toNat
  let h := v.getD 1 0 |>.toNat
  let nc := v.getD 2 0 |>.toNat
  let cs := chans (v.drop 3)
  let want := v.getD (3 + nc * 3) 0 |>.toNat
  let size := Exr.flatPlanesSize cs w h
  size == want &&
  Exr.budgetReject (want - 1) size == true &&
  Exr.budgetReject want size == false &&
  (if want == 0 then true else Exr.budgetReject 0 size == false)

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/image_budget_vectors.txt"
  let content ← IO.FS.readFile path
  let ls := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range ls.length) ls do
    if !checkLine line then
      bad := bad + 1
      if bad <= 5 then IO.println s!"mismatch at line {idx + 1}: {line}"
  IO.println s!"{ls.length} image-budget vectors checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "image budget differential mismatch")
