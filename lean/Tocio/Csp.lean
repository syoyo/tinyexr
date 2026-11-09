/-
  TinyEXR - Lean 4 formalization of the Cinespace CSP loader (.csp).

  Ports `sandbox/tocio/src/toc_csp.c`: line-based reading with
  case-insensitive prefix matching, per-channel preluts with the
  Rising-Sun cubic spline resample (65536 samples), the `CSPLUTV100`
  structure with `1D`/`3D` LUTs and `BEGIN/END METADATA` blocks.
  The spline reproduces OCIO's `rsr_Interpolator1D` exactly in
  `Float32` arithmetic (build, binary search, cubic evaluation).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Clf
import Tocio.SpiFile

namespace Tocio

set_option linter.unusedVariables false

/-- CSP line whitespace: space, tab, CR, VT, FF (`csp_ws` + 11, 12). -/
def cspWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == Char.ofNat 11 || c == Char.ofNat 12

/-- Fuel-bounded line reader (mirrors `csp_line`; blank lines are
  skipped entirely). -/
def cspLineFuel : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    let (line, rest) := cs.span (· != '\n')
    let rest := match rest with | '\n' :: t => t | _ => []
    let trimmed := (line.reverse.dropWhile cspWs |>.reverse).dropWhile cspWs
    if trimmed.isEmpty then cspLineFuel fuel rest else some (trimmed, rest)

/-- Read the next non-blank line (trimmed on both ends). -/
def cspLine (cs : List Char) : Option (List Char × List Char) :=
  cspLineFuel (cs.length + 1) cs

/-- Case-insensitive prefix test on a trimmed line (mirrors
  `csp_starts`, uppercase-folding ASCII lowercase bytes). -/
def cspStarts (line : List Char) (pre : String) : Bool :=
  let up : Char → Char := fun c => if c >= 'a' && c <= 'z' then
    Char.ofNat (c.val.toNat - 32) else c
  line.zip pre.toList |>.all (fun (a, b) => up a == b) && pre.length ≤ line.length

/-- Exactly `want` floats from a line, with only ' \\t\\r' allowed
  after them (mirrors `csp_floats`' strict whole-line parse). -/
def cspFloats (line : List Char) (want : Nat) : Option (List Float32) :=
  let rec go (fuel : Nat) (cs : List Char) (acc : List Float32) : Option (List Float32) :=
    if acc.length = want then
      let rem := cs.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')
      if rem.isEmpty then some acc else none
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match readF32 cs with
        | none => none
        | some (v, rest) => go fuel rest (acc ++ [v])
  go (line.length + 1) line []

/-- Exactly `want` ints with the same whole-line discipline. -/
def cspInts (line : List Char) (want : Nat) : Option (List Int) :=
  let rec go (fuel : Nat) (cs : List Char) (acc : List Int) : Option (List Int) :=
    if acc.length = want then
      let rem := cs.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')
      if rem.isEmpty then some acc else none
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match readInt cs with
        | none => none
        | some (v, rest) => go fuel rest (acc ++ [v])
  go (line.length + 1) line []

/-- Rising-Sun spline parameters: per segment `[1/delta, a, b, c, d]`. -/
def splineBuild (st va : List Float32) : List (List Float32) :=
  let n := st.length
  if n < 2 then []
  else if n == 2 then
    [[1.0 / (st.getD 1 0.0 - st.getD 0 0.0), va.getD 0 0.0,
      va.getD 1 0.0 - va.getD 0 0.0, 0.0, 0.0]]
  else
    (List.range (n - 1)).map (fun i =>
      let f0 := va.getD i 0.0
      let f1 := va.getD (i + 1) 0.0
      let delta : Float32 := st.getD (i + 1) 0.0 - st.getD i 0.0
      let p0 : Float32 := 1.0 / delta
      if i == 0 then
        let delta2 : Float32 := (st.getD (i + 2) 0.0 - st.getD (i + 1) 0.0) / delta
        let dfdx1 : Float32 := (va.getD (i + 2) 0.0 - f0) / (1.0 + delta2)
        [p0, f0, -2.0 * f0 + 2.0 * f1 - dfdx1, f0 - f1 + dfdx1, 0.0]
      else if i == n - 2 then
        let delta1 : Float32 := (st.getD i 0.0 - st.getD (i - 1) 0.0) / delta
        let dfdx0 : Float32 := (f1 - va.getD (i - 1) 0.0) / (1.0 + delta1)
        [p0, f0, dfdx0, -f0 + f1 - dfdx0, 0.0]
      else
        let delta1 : Float32 := (st.getD i 0.0 - st.getD (i - 1) 0.0) / delta
        let delta2 : Float32 := (st.getD (i + 2) 0.0 - st.getD (i + 1) 0.0) / delta
        let dfdx0 : Float32 := (f1 - va.getD (i - 1) 0.0) / (1.0 + delta1)
        let dfdx1 : Float32 := (va.getD (i + 2) 0.0 - f0) / (1.0 + delta2)
        [p0, f0, -3.0 * f0 - 2.0 * dfdx0 + 3.0 * f1 - dfdx1,
         2.0 * f0 + dfdx0 - 2.0 * f1 + dfdx1, 0.0])

/-- `csp_spline_build` validity: inputs strictly increase. -/
def splineOk (st : List Float32) : Bool :=
  (List.zip st (st.drop 1)).all (fun (a, b) => a < b)

/-- `csp_spline_eval`: binary search + cubic evaluation. -/
def splineEval (params : List (List Float32)) (st va : List Float32) (x : Float32) :
    Float32 :=
  let n := st.length
  if x != x then x
  else if x < st.getD 0 0.0 then va.getD 0 0.0
  else if x > st.getD (n - 1) 0.0 then va.getD (n - 1) 0.0
  else
    let rec seg : Nat → Nat → Nat → Nat
      | 0, lo, _ => lo
      | fuel + 1, lo, hi =>
        if hi - lo > 1 then
          let mid := (lo + hi) / 2
          if x < st.getD mid 0.0 then seg fuel lo mid else seg fuel mid hi
        else lo
    let lo := seg n 0 (n - 1)
    let p := params.getD lo []
    let z : Float32 := (x - st.getD lo 0.0) * p.getD 0 0.0
    p.getD 1 0.0 + z * (p.getD 2 0.0 + z * (p.getD 3 0.0 + p.getD 4 0.0 * z))

/-- `csp_identity`: whole-prelut relative-identity check. -/
def cspIdentity (pin pout : List Float32) : Bool :=
  (List.zip pin pout).all (fun (a, b) =>
    let d := if a > b then a - b else b - a
    let m := if a > 0.0 then a else -a
    d ≤ 1e-6 * m)

/-- Counts constraint helpers (shortcuts to SpiFile primitives). -/
def valuesFitC (count avail : Nat) : Bool := spiValuesFit count avail

/-! ## Loader (`toc_load_csp`) -/

/-- One prelut channel: `cnt` input then output floats from the two
  lines following the count line (`csAfter` is the text after the count
  line). Returns `(pin, pout, identity, rest)`. -/
def preChannel (csAfter : List Char) (cnt : Nat) :
    Except ClfError (List Float32 × List Float32 × Bool × List Char) :=
  if cnt < 2 then Except.ok ([], [], true, csAfter)
  else if !spiValuesFit (cnt * 2) csAfter.length then Except.error .parse
  else
    match cspLine csAfter with
    | none => Except.error .parse
    | some (l1, cs1) =>
      match cspFloats l1 cnt with
      | none => Except.error .parse
      | some pin =>
        match cspLine cs1 with
        | none => Except.error .parse
        | some (l2, cs2) =>
          match cspFloats l2 cnt with
          | none => Except.error .parse
          | some pout => Except.ok (pin, pout, cspIdentity pin pout, cs2)

/-- Fuel-bounded loop over the three prelude channels. The count line
  for channel 0 is supplied; channels 1 and 2 read theirs on entry. -/
def preludeLoop (fuel : Nat) (cs : List Char)
    (countLine : Option (List Char)) (pin pout : List (List Float32))
    (usePre : Bool) :
    Except ClfError (List (List Float32) × List (List Float32) × Bool × List Char) :=
  match fuel, countLine with
  | 0, _ => Except.ok (pin, pout, usePre, cs)
  | fuel + 1, none =>
    match cspLine cs with
    | none => Except.error .parse
    | some (l, cs2) =>
      -- resolve the count line, then continue with the same fuel budget
      match cspInts l 1 with
      | some [c] =>
        if c < 0 || c > 65536 then Except.error .parse
        else
          match preChannel cs2 (c.toNat) with
          | Except.error e => Except.error e
          | Except.ok (pinI, poutI, ident, cs3) =>
            let usePre' := if c < 2 then usePre else usePre || !ident
            if fuel < 1 then Except.ok (pin ++ [pinI], pout ++ [poutI], usePre', cs3)
            else
              match cspLine cs3 with
              | none => Except.error .parse
              | some (l2, cs4) =>
                preludeLoop fuel cs4 (some l2) (pin ++ [pinI]) (pout ++ [poutI]) usePre'
      | _ => Except.error .parse
  | fuel + 1, some countLine =>
    match cspInts countLine 1 with
    | some [c] =>
      if c < 0 || c > 65536 then Except.error .parse
      else
        match preChannel cs (c.toNat) with
        | Except.error e => Except.error e
        | Except.ok (pinI, poutI, ident, cs1) =>
          let usePre' := if c < 2 then usePre else usePre || !ident
          let pin' := pin ++ [pinI]
          let pout' := pout ++ [poutI]
          match fuel with
          | 0 => Except.ok (pin', pout', usePre', cs1)
          | _ =>
            match cspLine cs1 with
            | none => Except.error .parse
            | some (l, cs2) => preludeLoop fuel cs2 (some l) pin' pout' usePre'
    | _ => Except.error .parse

/-- Read `rows` lines of exactly `per` floats each (C's LUT body loop). -/
def readLutLines (rows per : Nat) (cs0 : List Char) :
    Except ClfError (List (List Float32)) :=
  let rec go : Nat → List Char → List (List Float32) → Except ClfError (List (List Float32))
    | 0, _, acc => Except.error .parse
    | fuel + 1, cs, acc =>
      if acc.length = rows then Except.ok acc
      else
        match cspLine cs with
        | none => Except.error .parse
        | some (l, cs2) =>
          match cspFloats l per with
          | none => Except.error .parse
          | some row => go fuel cs2 (acc ++ [row])
  go (rows + 1) cs0 []

/-- Assemble the op list, inserting the prelude resample if needed: a
  65536×3 resampled LUT1D preceded by the diagonal scale matrix
  (offsets s.t. `[lo,hi]` maps to `[0,1]`). -/
def buildCspOps (pin pout : List (List Float32)) (usePre : Bool) (lut : ClfOp) :
    Except ClfError (List ClfOp) :=
  if !usePre then Except.ok [lut]
  else if !((List.range 3).all (fun ch => splineOk (if (pin.getD ch []).isEmpty then [0.0, 1.0] else pin.getD ch []))) then
    Except.error .parse
  else
    let st : Nat → List Float32 := fun ch =>
      if (pin.getD ch []).isEmpty then [0.0, 1.0] else pin.getD ch []
    let va : Nat → List Float32 := fun ch =>
      if (pout.getD ch []).isEmpty then [0.0, 1.0] else pout.getD ch []
    let lo : Nat → Float32 := fun ch => (st ch).headD 0.0
    let hi : Nat → Float32 := fun ch => (st ch).getLastD 1.0
    let m : List Float32 := (List.range 16).map (fun idx =>
      let i := idx % 4
      let j := idx / 4
      if i < 3 && i == j then 1.0 / (hi i - lo i)
      else if idx == 15 then 1.0 else 0.0)
    let off : List Float32 := (List.range 4).map (fun i =>
      let sc : Float32 := 1.0 / (hi i - lo i)
      if i < 3 then -lo i * sc else 0.0)
    let pre : List Float32 := (List.range 65536).flatMap (fun i =>
      (List.range 3).map (fun ch =>
        let params := splineBuild (st ch) (va ch)
        let t : Float32 := Float32.ofNat i / Float32.ofNat 65535
        splineEval params (st ch) (va ch) (lo ch + (hi ch - lo ch) * t)))
    Except.ok [.matrix m off, .lut1d 65536 pre, lut]

/-- The LUT-body part of the loader (after the preludes). -/
def loadCspBody (is3d : Bool) (pin pout : List (List Float32)) (usePre : Bool)
    (cs : List Char) : Except ClfError (List ClfOp) :=
  match cspLine cs with
  | none => Except.error .parse
  | some (hdr, cs1) =>
    if is3d then
      match cspInts hdr 3 with
      | some [n1, n2, n3] =>
        if n1 != n2 || n1 != n3 || n1 < 2 || n1 > 129 then
          Except.error .parse
        else if !spiValuesFit (n1.toNat * n1.toNat * n1.toNat * 3) cs1.length then
          Except.error .parse
        else
          (readLutLines (n1.toNat * n1.toNat * n1.toNat) 3 cs1).bind (fun rows =>
            buildCspOps pin pout usePre (.lut3d (n1.toNat) rows.flatten false))
      | _ => Except.error .parse
    else
      match cspInts hdr 1 with
      | some [n1] =>
        if n1 < 2 || n1 > (1 <<< 20) then Except.error .parse
        else if !spiValuesFit (n1.toNat * 3) cs1.length then Except.error .parse
        else
          (readLutLines (n1.toNat) 3 cs1).bind (fun rows =>
            buildCspOps pin pout usePre (.lut1d (n1.toNat) rows.flatten))
      | _ => Except.error .parse

/-- The top-level CSP loader. -/
def loadCsp (src : String) : Except ClfError (List ClfOp) :=
  let cs := src.toList
  match cspLine cs with
  | none => Except.error .parse
  | some (h0, cs1) =>
    if !cspStarts h0 "CSPLUTV100" then Except.error .parse
    else
      match cspLine cs1 with
      | none => Except.error .parse
      | some (h1, cs2) =>
        if !(cspStarts h1 "3D") && !(cspStarts h1 "1D") then Except.error .unsupported
        else
          let is3d := cspStarts h1 "3D"
          let body : Option (List Char × List Char) := match cspLine cs2 with
            | none => none
            | some (h2, cs3) =>
              if cspStarts h2 "BEGIN METADATA" then
                let rec skipMeta : Nat → List Char → Option (List Char × List Char)
                  | 0, _ => none
                  | fuel + 1, cs4 =>
                    match cspLine cs4 with
                    | none => none
                    | some (l, cs5) =>
                      if cspStarts l "END METADATA" then
                        match cspLine cs5 with
                        | none => none
                        | some (l2, cs6) => some (l2, cs6)
                      else skipMeta fuel cs5
                skipMeta (cs3.length + 1) cs3
              else some (h2, cs3)
          match body with
          | none => Except.error .parse
          | some (countLine0, cs3) =>
            match preludeLoop 3 cs3 (some countLine0) [] [] false with
            | Except.error e => Except.error e
            | Except.ok (pin, pout, usePre, cs4) =>
              loadCspBody is3d pin pout usePre cs4

end Tocio
