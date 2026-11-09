/-
  TinyEXR - Lean 4 formalization of the Sony .spi1d/.spi3d loaders.

  Total text parsers mirroring `load_spi1d` / `load_spi3d` in
  `sandbox/tocio/src/toc_lutfile.c`, with a libm-free decimal float /
  int parser reproducing `toc_parse_float` / `toc_parse_int` in
  `sandbox/tocio/src/toc_math.c` (double accumulation, sequential
  10^exp scaling, saturating exponents and ints) and the
  `toc_values_fit` allocation guard (`count ≤ avail/2 + 1`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.LutFile

namespace Tocio

set_option linter.unusedVariables false

/-- 1D LUT content. -/
structure Lut1dContent where
  length : Nat
  channels : Nat
  (domainMin domainMax : Float32)
  data : List Float32
  deriving Repr

/-- 3D LUT content (domain [0,1]³). -/
structure Lut3dContent where
  size : Nat
  data : List Float32
  deriving Repr

/-- Whitespace-commute test for the lutfile cursor. -/
def isSp (c : Char) : Bool := c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Fuel-bounded skip of whitespace and `#` comments (mirrors C's
  `skip_ws`): strips whitespace, then one comment to end-of-line, then
  repeats. Fuel bounds the loop; passing `cs.length + 1` is enough
  because each comment strip consumes its `#`. -/
def skipWsAux : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    let stripped := cs.dropWhile (fun c => isSp c)
    match stripped with
    | '#' :: _ =>
      let rest := stripped.dropWhile (fun c => c != '\n')
      skipWsAux fuel rest
    | _ => stripped

/-- Skip whitespace/comments. -/
def skipWs (cs : List Char) : List Char := skipWsAux (cs.length + 1) cs

/-- Alphabetic test for `peek_word`. -/
def isAlpha (c : Char) : Bool := (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')

/-- True iff the next significant token is a bare word. -/
def peekWord (cs : List Char) : Bool :=
  match skipWs cs with
  | c :: _ => isAlpha c
  | _ => false

/-- Read the next bare word (mirrors `read_word`, 31-char cap, stops at
  whitespace or `#`). -/
def readWord (cs : List Char) : String × List Char :=
  let cs := skipWs cs
  let w := cs.takeWhile (fun c => !(isSp c) && c != '#')
  (String.ofList (w.take 31), cs.drop w.length)

/-- Sequential power of ten (matches C's `for (i=0;i<exp;i++) m*=10`). -/
def pow10Acc : Nat → Float → Float
  | 0, m => m
  | n + 1, m => pow10Acc n (m * 10.0)

/-- Decimal float parser (C double-then-cast rounding). Faithful to
  `toc_parse_float`: leading whitespace *and commas* are skipped, then
  an optional sign, integer and fraction parts in `Float64`, then an
  optional exponent saturated so `exp` stays ≤ ~100009, scaled by the
  sequential `pow10Acc`, finally converted `Float.toFloat32`. Returns
  `none` when no digit is present (C returns 0 without advancing).
  The remainder is the unconsumed suffix. -/
def readF32 (cs0 : List Char) : Option (Float32 × List Char) :=
  let cs := (cs0.dropWhile (fun c => isSp c || c == ','))
  let (sign, cs) := match cs with
    | '-' :: t => ((-1 : Int), t)
    | '+' :: t => ((1 : Int), t)
    | _ => ((1 : Int), cs)
  let (intPart, cs2) := (cs.takeWhile Char.isDigit, cs.dropWhile Char.isDigit)
  let (fracPart, cs3) := match cs2 with
    | '.' :: t =>
      let fr := t.takeWhile Char.isDigit
      (fr, t.drop fr.length)
    | _ => ([], cs2)
  if intPart.isEmpty && fracPart.isEmpty then none
  else
    let dv : Char → Float := fun c => c.val.toFloat - 48.0
    let v0 := intPart.foldl (fun acc c => acc * 10 + dv c) 0
    let (fracV, _) := fracPart.foldl (fun (acc : Float × Float) c =>
      (acc.1 + dv c / acc.2, acc.2 * 10)) (0.0, 10.0)
    let base := v0 + fracV
    let v1 := if sign < 0 then -base else base
    let (withExp, cs4) := match cs3 with
      | 'e' :: t | 'E' :: t =>
        let (esign, tt) := match t with
          | '-' :: tt => ((-1 : Int), tt)
          | '+' :: tt => ((1 : Int), tt)
          | _ => (1, t)
        let expDigits := tt.takeWhile Char.isDigit
        let rest := tt.drop expDigits.length
        let expV := expDigits.foldl (fun (acc : Nat) c =>
          if acc < 10000 then acc * 10 + (c.val.toNat - '0'.toNat) else acc) 0
        let m := pow10Acc expV 1.0
        (v1 * (if esign < 0 then 1.0 / m else m), rest)
      | _ => (v1, cs3)
    some (Float.toFloat32 withExp, cs4)

/-- Int parser (C `toc_parse_int`: saturates at 1e14, sign-aware). -/
def readInt (cs0 : List Char) : Option (Int × List Char) :=
  let cs := cs0.dropWhile isSp
  let (sign, cs) := match cs with
    | '-' :: t => ((-1 : Int), t)
    | '+' :: t => ((1 : Int), t)
    | _ => ((1 : Int), cs)
  let digs := cs.takeWhile Char.isDigit
  if digs.isEmpty then none
  else
    let v := digs.foldl (fun (acc : Int) c =>
      if acc < 100000000000000 then acc * 10 + (Int.ofNat c.val.toNat - 48) else acc) 0
    some (v * sign, cs.drop digs.length)

/-- `toc_values_fit`: `count ≤ avail/2 + 1` where `avail` is the byte
  count remaining. -/
def spiValuesFit (count avail : Nat) : Bool := count ≤ avail / 2 + 1

/-- Header state for spi1d (C's header locals). -/
structure Spi1dHdr where
  (from0 from1 : Float32)
  (length comps : Nat)
  deriving Repr

/-- Header scan loop (fuel-bounded; each iteration consumes a word).
  Returns the state and the remaining chars at the first non-header
  token, mirroring C's `while (peek_word(c))`. -/
def spi1dHdrLoop : Nat → List Char → Spi1dHdr → Option (Spi1dHdr × List Char)
  | 0, cs, h => some (h, cs)
  | fuel + 1, cs, h =>
    if !peekWord cs then some (h, cs)
    else
      let (w, cs2) := readWord cs
      match w with
      | "Version" =>
        match readInt cs2 with
        | none => spi1dHdrLoop fuel cs2 h
        | some (_, cs3) => spi1dHdrLoop fuel cs3 h
      | "From" =>
        match readF32 cs2 with
        | none => spi1dHdrLoop fuel cs2 h
        | some (a, cs3) =>
          match readF32 cs3 with
          | none => spi1dHdrLoop fuel cs3 { h with from0 := a }
          | some (b, cs4) => spi1dHdrLoop fuel cs4 { h with from0 := a, from1 := b }
      | "Length" =>
        match readInt cs2 with
        | some (v, cs3) =>
          if v ≥ 0 then spi1dHdrLoop fuel cs3 { h with length := v.toNat }
          else spi1dHdrLoop fuel cs3 h
        | none => spi1dHdrLoop fuel cs2 h
      | "Components" =>
        match readInt cs2 with
        | some (v, cs3) =>
          if v ≥ 0 then spi1dHdrLoop fuel cs3 { h with comps := v.toNat }
          else spi1dHdrLoop fuel cs3 h
        | none => spi1dHdrLoop fuel cs2 h
      | _ => some (h, cs2)

/-- spi1d value reader: skip one `{` if present, then read exactly
  `want` floats, stopping early at `}` or EOF (C's `got != want` check
  then fails the load). Fuel = `want`. -/
def spi1dVals (fuel want : Nat) (cs0 : List Char) (acc : List Float32) :
    Option (List Float32 × List Char) :=
  if acc.length = want then some (acc, cs0)
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let cs := skipWs cs0
      match cs with
      | '}' :: _ => none
      | _ =>
        match readF32 cs with
        | none => none
        | some (v, rest) => spi1dVals fuel want rest (acc ++ [v])

/-- Full spi1d load: header, range checks (`2 ≤ length ≤ 2^18`,
  `comps ∈ {1,3}`), `valuesFit`, then the body. Some/None mirrors
  `TOC_SUCCESS` vs `TOC_ERROR_PARSE`. -/
def loadSpi1d (src : String) : Option Lut1dContent :=
  let cs := src.toList
  match spi1dHdrLoop (cs.length + 1) cs ⟨0.0, 1.0, 0, 1⟩ with
  | none => none
  | some (h, cs2) =>
    if h.length < 2 || h.length > (1 <<< 18) || (h.comps != 1 && h.comps != 3) then none
    else
      let cs3 := skipWs cs2
      let cs4 := match cs3 with | '{' :: t => t | _ => cs3
      let want := h.length * h.comps
      if !spiValuesFit want cs4.length then none
      else
        match spi1dVals (want + 1) want cs4 [] with
        | none => none
        | some (vals, _) =>
          if vals.length = want then
            some ⟨h.length, h.comps, h.from0, h.from1, vals⟩
          else none

/-- One spi3d row: three indices and three floats, bounds-checked. -/
def spi3dRow (N : Nat) (cs : List Char) :
    Option (Nat × Nat × Nat × Float32 × Float32 × Float32 × List Char) :=
  match readInt cs with
  | none => none
  | some (ir, cs1) =>
    match readInt cs1 with
    | none => none
    | some (ig, cs2) =>
      match readInt cs2 with
      | none => none
      | some (ib, cs3) =>
        if ir < 0 || ir >= N || ig < 0 || ig >= N || ib < 0 || ib >= N then none
        else
          match readF32 cs3 with
          | none => none
          | some (r, cs4) =>
            match readF32 cs4 with
            | none => none
            | some (g, cs5) =>
              match readF32 cs5 with
              | none => none
              | some (b, cs6) =>
                some (ir.toNat, ig.toNat, ib.toNat, r, g, b, cs6)

/-- Full spi3d load: `SPILUT ver nin nout n1 n2 n3` header (the `ver`
  float and the `SPILUT` token are consumed unconditionally, as in C),
  then `N³` rows written into `N³·3` zero-initialised data at
  `((ib*N + ig)*N + ir)*3` (R-fastest). Returns the 3D content. -/
def loadSpi3d (src : String) : Option Lut3dContent := do
  let cs := src.toList
  let cs := if peekWord cs then (readWord cs).2 else cs
  let (_, cs2) ← readF32 cs
  let (_, cs3) ← readInt cs2
  let (_, cs4) ← readInt cs3
  let (n1, cs5) ← readInt cs4
  let (n2, cs6) ← readInt cs5
  let (n3, cs7) ← readInt cs6
  if decide (n1 != n2 || n2 != n3 || n1 < 2 || n1 > 256) then none
  else
    let N := n1.toNat
    let want := N * N * N * 3
    if !spiValuesFit (want * 2) cs7.length then none
    else
      let zeros : List Float32 := List.replicate want 0.0
      let rec fill (fuel : Nat) (cs : List Char) (acc : List Float32)
          (filled : Nat) : Option (List Float32) :=
        if filled = N * N * N then some acc
        else
          match fuel with
          | 0 => none
          | fuel + 1 =>
            match spi3dRow N cs with
            | none => none
            | some (ir, ig, ib, r, g, b, rest) =>
              let idx := ((ib * N + ig) * N + ir) * 3
              let acc' := acc.set idx r |>.set (idx + 1) g |>.set (idx + 2) b
              fill fuel rest acc' (filled + 1)
      fill (N * N * N + 1) cs7 zeros 0 |>.map (fun data => (⟨N, data⟩ : Lut3dContent))
/-- Allocation bound: spi1d `2^18 * 3`, spi3d `256³·3`. -/
theorem spi1dWant_bound : (1 <<< 18) * 3 ≤ 786432 * 3 := by decide
/-- .spi3d N³·3 row count at the 256 cap. -/
theorem spi3dWant_max : 256 * 256 * 256 * 3 = 50331648 := by decide

end Tocio
