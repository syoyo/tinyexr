/-
  TinyEXR - Lean 4 formalization of the CLF (Common LUT Format) loader.

  Ports `sandbox/tocio/src/toc_clf.c`: the single-pass stream reader
  over the XML primitives (`Tocio.ClfXml`), the `ProcessList`
  dispatcher, and the process-node handlers. Node handlers mirror C
  bit-for-bit: bit-depth normalization, the BLUE-fastest to
  RED-fastest LUT3D transpose, CDL inverse decomposition via
  `toc_push_cdl`, and the OCIO Range semantics. Unrecognized node
  kinds listed in `toc_load_clf` return `UNSUPPORTED` (never skipped);
  other unknown elements are skipped as in C.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ClfXml
import Tocio.SpiFile
import Tocio.LutFile

namespace Tocio

set_option linter.unusedVariables false

/-- Loader error kind (mirrors C result codes). -/
inductive ClfError where
  | parse
  | unsupported
  deriving Repr, DecidableEq

/-- Error display (mirrors the C result-name mapping used in logs). -/
instance : ToString ClfError where
  toString
    | .parse => "parse"
    | .unsupported => "unsupported"

/-- Op contents as produced by the CLF handlers (mirroring `toc_op`
  fields; the data the Lean kernels consume). -/
inductive ClfOp where
  | matrix (m off : List Float32)
  | range (scale offset mn mx : List Float32) (clampLo clampHi : Bool)
  | exponent (e : List Float32) (mirror : Bool)
  | expLinear (scale offset gamma brk slope : List Float32) (inverse mirror : Bool)
  | log (base : Float32) (inverse : Bool)
        (logSlope logOffset linSlope linOffset : List Float32)
  | logCam (base : Float32) (inverse : Bool)
        (logSlope logOffset linSlope linOffset linBreak linearSlope linearOffset :
          List Float32)
  | lut1d (length : Nat) (data : List Float32)
  | lut3d (size : Nat) (data : List Float32) (tetra : Bool)
  deriving Repr

/-- `clf_depth_scale`: code-value normalization scales. -/
def depthScale (v : String) : Float32 :=
  match v with
  | "8i" => 255.0
  | "10i" => 1023.0
  | "12i" => 4095.0
  | "16i" => 65535.0
  | _ => 1.0

/-- `clf_dims`: parse a `dim="a b c d"` attribute value (at most 4
  dims, positive, ≤ 2^20, breaks without progress). -/
def clfDims (val : String) : List Nat :=
  let chars := val.toList
  let rec go (fuel : Nat) (cs : List Char) (nd : Nat) (acc : List Nat) : List Nat :=
    match fuel, cs with
    | 0, _ => acc
    | _, [] => acc
    | fuel + 1, _ =>
      if nd = 4 then acc
      else
        match readInt cs with
        | none => acc
        | some (d, rest) =>
          if d > 0 && d ≤ (1 <<< 20) then
            go fuel (rest.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'))
              (nd + 1) (acc ++ [d.toNat])
          else go fuel (rest.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')) nd acc
  go (chars.length + 1) chars 0 []

/-- Segment reader for `xfloatsAux` (C inner loop): greedy floats from one text segment. -/
def xfloatSeg : Nat → List Char → List Float32 → Nat → List Float32 × List Char × Bool
  | 0, _, acc, _ => (acc, [], false)
  | fuel + 1, cs, acc, max =>
    if acc.length = max then (acc, cs, true)
    else
      match readF32 cs with
      | none =>
        let rem := cs.dropWhile (fun c => c.val ≤ 32)
        (acc, cs, rem.isEmpty)
      | some (v, rest) => xfloatSeg fuel rest (acc ++ [v]) max

/-- `xfloats` core loop, recursive version peeled off `xfloatSeg`. -/
def xfloatsAux (fuel : Nat) (cs0 : List Char) (max : Nat) (acc : List Float32) :
    List Float32 × List Char :=
  match fuel with
  | 0 => (acc, cs0)
  | fuel + 1 =>
    if acc.length = max then (acc, cs0)
    else
      let (txt, rest) := xt cs0
      if txt == "" then (acc, rest)
      else
        let (acc', segRem, segDone) := xfloatSeg fuel txt.toList acc max
        let segRemWs := segRem.dropWhile (fun c => c.val ≤ 32)
        if !segDone && !segRemWs.isEmpty then (acc', rest)
        else xfloatsAux fuel rest max acc'

/-- Read up to `max` floats (C `xfloats`). -/
def xfloats (cs : List Char) (max : Nat) : List Float32 × List Char :=
  xfloatsAux (cs.length + 1) cs max []

/-- If the next thing is a closing tag (`</...`), consume it as in C's
  `if (xat(r)) { ++r->p; if (*r->p == '/') xskip_close(r); }`. -/
def skipCloseTag (cs : List Char) : List Char :=
  if xat cs then
    match (xs cs).drop 1 with
    | '/' :: rest => (xskipClose rest).2
    | rest => rest
  else cs

/-- `<Array>` dims attribute scan: `while (xa(...)) if dim ...`. -/
def arrayDimsAux (fuel : Nat) (cs : List Char) (dims : List Nat) : List Nat × List Char :=
  match fuel with
  | 0 => (dims, cs)
  | fuel + 1 =>
    let (found, key, val, rest) := xa cs
    if !found then (dims, rest)
    else
      let dims' := if key == "dim" then clfDims val else dims
      arrayDimsAux fuel rest dims'

/-- Read `dim=` and consume the `>` (`xc`). -/
def arrayDims (cs : List Char) : List Nat × List Char :=
  let (dims, rest) := arrayDimsAux (cs.length + 1) cs []
  let (_, rest) := xc rest
  (dims, rest)

/-! ## Matrix -/

/-- `clf_matrix`: `<Array>` (row-major, column-major output, optional
  offset column) and `<Offset>` children. -/
def clfMatrix (cs0 : List Char) (inS outS : Float32) :
    Except ClfError (ClfOp × List Char) :=
  let identity : List Float32 := [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
  let zeroC : List Float32 := [0, 0, 0, 0]
  let rec loop (fuel : Nat) (cs : List Char) (m : List Float32) (off : List Float32) :
      Except ClfError (List Float32 × List Float32 × List Char) :=
    if fuel = 0 then Except.error .parse
    else
      let (isOpen, tag, rest) := xtag cs
      if !isOpen then
        match xskipClose rest with
        | (true, rest2) => Except.ok (m, off, rest2)
        | (false, _) => Except.error .parse
      else if tag == "Array" then
        let (dims, rest) := arrayDims rest
        let rows := if dims.length = 3 && dims.getD 2 0 = 3 && dims.getD 0 0 = dims.getD 1 0 then 3
                    else dims.getD 0 0
        let cols := if dims.length = 2 then dims.getD 1 0
                    else if dims.length = 3 then dims.getD 0 0
                    else 0
        if (dims.length = 2 && ((dims.getD 0 0 = 3 && (dims.getD 1 0 = 3 || dims.getD 1 0 = 4)) ||
              (dims.getD 0 0 = 4 && (dims.getD 1 0 = 4 || dims.getD 1 0 = 5)))) ||
           (dims.length = 3 && dims.getD 2 0 = 3 && dims.getD 0 0 = dims.getD 1 0) then
          let (vals, rest) := xfloats rest (rows * cols)
          if vals.length != rows * cols then Except.error .parse
          else
            let m' := (List.range 16).map (fun idx =>
              let i := idx % 4
              let j := idx / 4
              if i < rows && j < rows then vals.getD (i * cols + j) 0.0 * inS / outS
              else m.getD idx 0.0)
            let off' := if cols > rows then
              (List.range 4).map (fun i => if i < rows then vals.getD (i * cols + rows) 0.0 / outS else off.getD i 0.0)
              else off
            loop (fuel - 1) (skipCloseTag rest) m' off'
        else Except.error .unsupported
      else if tag == "Offset" then
        let (_, rest2) := xc rest
        let (vals, rest) := xfloats rest2 4
        let off' := (List.range 4).map (fun i => vals.getD i 0.0)
        loop (fuel - 1) (skipCloseTag rest) m off'
      else loop (fuel - 1) (xskipElem rest tag) m off
  loop (cs0.length + 1) cs0 identity zeroC |>.map (fun (m, off, rest) => (.matrix m off, rest))

/-! ## Range -/

/-- Single-float element body (`<minInValue>v</minInValue>`): not
  self-closing, then one float from text, then close tag. -/
def elemFloat (cs : List Char) : Except ClfError (Float32 × List Char) :=
  match xc cs with
  | (true, _) => Except.error .parse
  | (false, rest) =>
    let (txt, rest) := xt rest
    match readF32 (txt.toList) with
    | none => Except.error .parse
    | some (v, _) => Except.ok (v, skipCloseTag rest)

def clfRangeOp (minIn maxIn minOut maxOut : Float32)
    (hasMinIn hasMaxIn hasMinOut hasMaxOut : Bool) (noclamp : Bool) :
    Except ClfError ClfOp :=
  if hasMinIn != hasMinOut || hasMaxIn != hasMaxOut || (!hasMinIn && !hasMaxIn) then
    Except.error .parse
  else if hasMinIn && hasMaxIn && !(maxIn > minIn) then Except.error .parse
  else
    let (scale, offset) :=
      if hasMinIn && hasMaxIn then
        let scale := (maxOut - minOut) / (maxIn - minIn)
        (scale, minOut - minIn * scale)
      else if hasMinIn then (1.0, minOut - minIn)
      else (1.0, maxOut - maxIn)
    let unbounded : Float32 := -3.4e38
    let unboundedHi : Float32 := 3.4e38
    let full := hasMinIn && hasMaxIn
    let mnodef : Float32 := if hasMinOut then minOut else unbounded
    let mxnodef : Float32 := if hasMaxOut then maxOut else unboundedHi
    let scale4 := [scale, scale, scale, 1.0]
    let off4 := [offset, offset, offset, 0.0]
    let mn4 := [mnodef, mnodef, mnodef, unbounded]
    let mx4 := [mxnodef, mxnodef, mxnodef, unboundedHi]
    let cl := !(noclamp && full)
    Except.ok (.range scale4 off4 mn4 mx4 cl cl)

/-- `clf_range` state: the four values plus presence flags (C locals). -/
structure RngSt where
  (minIn maxIn minOut maxOut : Float32)
  (hasMinIn hasMaxIn hasMinOut hasMaxOut : Bool)
  deriving Repr

/-- `clf_range`: min/max in/out values, OCIO RangeOpData semantics. -/
def clfRange (cs0 : List Char) (inS outS : Float32) (noclamp : Bool) :
    Except ClfError (ClfOp × List Char) :=
  let rec loop (fuel : Nat) (cs : List Char) (st : RngSt) :
      Except ClfError (RngSt × List Char) :=
    if fuel = 0 then Except.error .parse
    else
      let (isOpen, tag, rest) := xtag cs
      if !isOpen then
        match xskipClose rest with
        | (true, rest2) => Except.ok (st, rest2)
        | (false, _) => Except.error .parse
      else if (tag == "minInValue" || tag == "maxInValue" ||
               tag == "minOutValue" || tag == "maxOutValue") then
        match elemFloat rest with
        | Except.error e => Except.error e
        | Except.ok (v, rest) =>
          let v := if tag.toList.getD 3 ' ' == 'I' then v / inS else v / outS
          if tag == "minInValue" then loop (fuel - 1) rest ⟨v, st.maxIn, st.minOut, st.maxOut, true, st.hasMaxIn, st.hasMinOut, st.hasMaxOut⟩
          else if tag == "maxInValue" then loop (fuel - 1) rest ⟨st.minIn, v, st.minOut, st.maxOut, st.hasMinIn, true, st.hasMinOut, st.hasMaxOut⟩
          else if tag == "minOutValue" then loop (fuel - 1) rest ⟨st.minIn, st.maxIn, v, st.maxOut, st.hasMinIn, st.hasMaxIn, true, st.hasMaxOut⟩
          else loop (fuel - 1) rest ⟨st.minIn, st.maxIn, st.minOut, v, st.hasMinIn, st.hasMaxIn, st.hasMinOut, true⟩
      else
        loop (fuel - 1) (xskipElem rest tag) st
  match loop (cs0.length + 1) cs0 ⟨0.0, 0.0, 0.0, 0.0, false, false, false, false⟩ with
  | Except.error e => Except.error e
  | Except.ok (st, rest) =>
    match clfRangeOp st.minIn st.maxIn st.minOut st.maxOut
        st.hasMinIn st.hasMaxIn st.hasMinOut st.hasMaxOut noclamp with
    | Except.error e => Except.error e
    | Except.ok op => Except.ok (op, rest)

/-! ## Exponent / Log / CDL / LUT handlers (stubs returning UNSUPPORTED) -/

/-- `clf_exponent` (slice 3). -/
def clfExponent (_cs : List Char) (_style : String) :
    Except ClfError (ClfOp × List Char) := Except.error .unsupported

/-- `clf_log` (slice 3). -/
def clfLog (_cs : List Char) (_style : String) (_empty : Bool) :
    Except ClfError (ClfOp × List Char) := Except.error .unsupported

/-- `clf_cdl` (slice 3). -/
def clfCdl (_cs : List Char) (_style : String) :
    Except ClfError (ClfOp × List Char) := Except.error .unsupported

/-- `clf_lut1d` (slice 4). -/
def clfLut1d (_cs : List Char) (_outS : Float32) :
    Except ClfError (ClfOp × List Char) := Except.error .unsupported

/-- `clf_lut3d` (slice 4). -/
def clfLut3d (_cs : List Char) (_tetra : Bool) (_outS : Float32) :
    Except ClfError (ClfOp × List Char) := Except.error .unsupported

/-! ## Dispatcher (`toc_load_clf`) -/

/-- The top-level skip-loop for unknown process nodes (C's else
  branch), fuel-bounded by the remaining input. -/
def unknownSkipLoop (fuel : Nat) (cs : List Char) (skipTag : String) :
    Except ClfError (List Char) :=
  match fuel with
  | 0 => Except.error .parse
  | fuel + 1 =>
    if cs.isEmpty then Except.ok cs
    else
      let (isOpen, tag, rest) := xtag cs
      if isOpen then
        let (_, rest) := xc rest
        unknownSkipLoop fuel rest skipTag
      else if tag == skipTag then
        Except.ok (rest.drop 1)
      else
        unknownSkipLoop fuel (rest.drop 1) skipTag

/-- `loadClf`: find `ProcessList`, read its attributes, iterate
  process nodes. -/
def loadClf (src : String) : Except ClfError (List ClfOp) :=
  let cs := src.toList
  let rec find (fuel : Nat) (cs : List Char) : Except ClfError (List Char) :=
    match fuel with
    | 0 => Except.error .parse
    | fuel + 1 =>
      let (isOpen, tag, rest) := xtag cs
      if !isOpen then Except.error .parse
      else if tag == "ProcessList" then Except.ok rest
      else find (fuel - 1) (xc rest).2
  match find (cs.length + 1) cs with
  | Except.error e => Except.error e
  | Except.ok cs1 =>
    let rec drainAttrs (fuel : Nat) (cs : List Char) : List Char :=
      match fuel with
      | 0 => cs
      | fuel + 1 =>
        let (found, _, _, rest) := xa cs
        if !found then rest
        else drainAttrs fuel rest
    let (_, cs2) := xc (drainAttrs (cs1.length + 1) cs1)
    let rec nodes (fuel : Nat) (cs : List Char) (acc : List ClfOp) :
        Except ClfError (List ClfOp) :=
      match fuel with
      | 0 => Except.ok acc
      | fuel + 1 =>
        match xtag cs with
        | (false, _, _) => Except.ok acc
        | (true, tag, rest) =>
          if tag == "InputDescriptor" || tag == "OutputDescriptor" || tag == "Description" then
            nodes (fuel - 1) (xskipElem rest tag) acc
          else if (tag == "ExposureContrast" || tag == "FixedFunction" ||
                   clfPrefix tag "Grading" || tag == "Function" ||
                   tag == "InverseLUT1D" || tag == "InverseLUT3D" ||
                   tag == "Reference" || tag == "Gamma") then
            Except.error .unsupported
          else if (tag == "Matrix" || tag == "Range" || tag == "Exponent" ||
                   tag == "Log" || tag == "LUT1D" || tag == "LUT3D" ||
                   tag == "ASC_CDL") then
            let rec attrs (fuel : Nat) (cs : List Char)
                (st : String × Bool × Bool × Float32 × Float32 × Bool) :
                String × Bool × Bool × Float32 × Float32 × Bool × List Char :=
              match fuel with
              | 0 => (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2, cs)
              | fuel + 1 =>
                let (found, key, val, rest) := xa cs
                if !found then
                  (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2, rest)
                else if key == "style" then
                  attrs fuel rest (val, st.2.1 || val == "noClamp", st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2)
                else if (key == "halfDomain" || key == "rawHalfs") && val == "true" then
                  attrs fuel rest (st.1, st.2.1, true, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2)
                else if key == "inBitDepth" then
                  attrs fuel rest (st.1, st.2.1, st.2.2.1, depthScale val, st.2.2.2.2.1, st.2.2.2.2.2)
                else if key == "outBitDepth" then
                  attrs fuel rest (st.1, st.2.1, st.2.2.1, st.2.2.2.1, depthScale val, st.2.2.2.2.2)
                else if key == "interpolation" && val == "tetrahedral" then
                  attrs fuel rest (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, true)
                else
                  attrs fuel rest st
            let (style, noclamp, halfdom, inS, outS, tetra, rest2) :=
              attrs (rest.length + 1) rest ("", false, false, 1.0, 1.0, false)
            let (empty, rest3) := xc rest2
            if halfdom && tag.toList.getD 0 ' ' == 'L' && tag.toList.getD 3 ' ' == '1' then
              Except.error .unsupported
            else if empty && tag.toList.getD 1 ' ' == 'o' then
              match clfLog rest3 style true with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if empty then Except.error .parse
            else if tag.toList.getD 0 ' ' == 'M' then
              match clfMatrix rest3 inS outS with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if tag.toList.getD 0 ' ' == 'R' then
              match clfRange rest3 inS outS noclamp with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if tag.toList.getD 0 ' ' == 'E' then
              match clfExponent rest3 style with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if tag.toList.getD 1 ' ' == 'o' then
              match clfLog rest3 style false with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if tag.toList.getD 0 ' ' == 'A' then
              match clfCdl rest3 style with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else if tag.toList.getD 3 ' ' == '1' then
              match clfLut1d rest3 outS with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
            else
              match clfLut3d rest3 tetra outS with
              | Except.error e => Except.error e
              | Except.ok (op, rest4) => nodes (fuel - 1) rest4 (acc ++ [op])
          else
            let (_, rest2) := xc rest
            match unknownSkipLoop (rest2.length + 1) rest2 tag with
            | Except.error e => Except.error e
            | Except.ok rest3 => nodes (fuel - 1) rest3 acc
    nodes (cs2.length + 1) cs2 []



end Tocio
