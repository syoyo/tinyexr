/-
  TinyEXR - ETC2 RGB / EAC alpha block-encoder differential checker.

  Compares each candidate encoder's bits AND error (the errors drive the C's
  mode selection) plus the final selected block and the EAC alpha block.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Etc2Encode

open Texcomp

def hexVal (c : Char) : Nat := if c >= '0' && c <= '9' then c.toNat - '0'.toNat else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10 else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10 else 0
def hexNat (s : String) : Nat := s.foldl (fun acc c => acc * 16 + hexVal c) 0
def fields (s : String) : List String := (s.splitOn " ").filter (fun f => f != "")

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "build/lean-gen/etc2_enc_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  let mut diffFail := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sec := line.splitOn "|"
    let px := ((fields (sec.getD 0 "")).filter (fun f => f != "E")).map hexNat
    let blk : List (List Nat) := (List.range 16).map (fun i =>
      (List.range 4).map (fun c => px.getD (i * 4 + c) 0))
    let v (k : Nat) := (fields (sec.getD k "")).map hexNat
    let flat := (v 1).getD 0 0
    let ind := v 2
    let dif := v 3
    let pla := v 4
    let rgb := (v 5).getD 0 0
    let eac := (v 6).getD 0 0
    let i := etc1Individual blk
    let d := etc1Differential blk
    let p := etc2RgbPlanar blk
    if d.2 == u64Max then diffFail := diffFail + 1
    let alpha := blk.map (fun q => q.getD 3 0)
    let ok := etc2RgbFlat blk == flat &&
      [i.1, i.2] == ind && [d.1, d.2] == dif && [p.1, p.2] == pla &&
      etc2RgbEncode blk == rgb && eacAlphaEncode alpha == eac
    if !ok then
      bad := bad + 1
      if bad <= 4 then
        IO.eprintln s!"line {idx + 1}: flat {etc2RgbFlat blk == flat} ind {[i.1, i.2] == ind} diff {[d.1, d.2] == dif} planar {[p.1, p.2] == pla} rgb {etc2RgbEncode blk == rgb} eac {eacAlphaEncode alpha == eac}"
  IO.println s!"{lines.length} ETC2/EAC blocks checked ({diffFail} with unusable differential), {bad} mismatches"
  if bad != 0 then throw (IO.userError "etc2 enc mismatch")
