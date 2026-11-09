/-
  TinyEXR - ASTC debug dump (Lean side).
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.AstcDecode

open Texcomp

def hexVal (c : Char) : Nat :=
  if c >= '0' && c <= '9' then c.toNat - '0'.toNat
  else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseBlock (s : String) : List Nat :=
  (List.range 16).map (fun i =>
    let h := ((s.drop (i * 2) |>.take 2).toString).foldl (fun acc c => acc * 16 + hexVal c) 0
    h)

def main (args : List String) : IO Unit := do
  let hex := args.getD 0 "42085738e21eca9e49569e1a9465ad45"
  let block := parseBlock hex
  let mode := rdBits block 0 11
  IO.println s!"mode={mode}"
  match decodeBlockMode mode with
  | none => IO.println "bad mode"
  | some bm =>
    IO.println s!"wx={bm.wx} wy={bm.wy} wquant={bm.quant} dual={bm.dual}"
    let pc := rdBits block 11 2 + 1
    let wc := bm.wx * bm.wy * (if bm.dual != 0 then 2 else 1)
    let wb := iseBitcount wc bm.quant
    IO.println s!"part={pc} weight_count={wc} weight_bits={wb}"
    let rev := (List.range 16).map (fun i => bitrev8 (block.getD (15 - i) 0))
    match iseDecode bm.quant wc rev 0 with
    | none => IO.println "ise fail"
    | some ws =>
      IO.println s!"wsyms={ws}"
      let uq := weightUnquant.getD bm.quant []
      let grid := (List.range (bm.wx * bm.wy)).map (fun i =>
        uq.getD (ws.getD (if bm.dual != 0 then i * 2 else i) 0) 0)
      IO.println s!"wgrid={grid}"
      let pindex := rdBits block 13 10
      let cf := rdBits block 23 6
      IO.println s!"pindex={pindex} cf={cf}"
      let cems := if pc == 1 then [rdBits block 13 4]
        else if (cf &&& 3) == 0 then (List.range pc).map (fun _ => cf >>> 2)
        else
          let baseClass := (cf &&& 3) - 1
          let extra := 3 * pc - 4
          let extPos := 128 - wb - extra
          let code := cf + (rdBits block extPos extra <<< 6)
          (List.range pc).map (fun i =>
            (((baseClass + ((code >>> (2 + i)) &&& 1)) <<< 2) +
             ((code >>> (2 + pc + 2 * i)) &&& 3)))
      let colorStart := if pc == 1 then 17 else 29
      IO.println s!"cems={cems} color_start={colorStart}"
      let vcount := (List.range pc).foldl (fun acc i =>
        acc + (((cems.getD i 0 >>> 2) + 1) * 2)) 0
      IO.println s!"vcount={vcount}"
      let avail := 128 - (colorStart + wb + (if bm.dual != 0 then 2 else 0))
      let cq := (List.range 21).reverse.find? (fun i =>
        (not (i < 4)) && (iseBitcount vcount i <= avail))
      IO.println s!"cq={cq}"
      match cq with
      | none => pure ()
      | some cq =>
        match iseDecode cq vcount block colorStart with
        | none => IO.println "color ise fail"
        | some cs =>
          IO.println s!"csyms={cs}"
          let cu := colorUnquant.getD (cq - 4) []
          let vals := (List.range vcount).map (fun i =>
            if cq == 20 then cs.getD i 0 else cu.getD (cs.getD i 0) 0)
          IO.println s!"vals={vals}"
