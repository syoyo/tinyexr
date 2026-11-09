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
  | cdl (slope offset power : List Float32) (sat : Float32) (clampVal : Bool)
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
    Except ClfError (List ClfOp × List Char) :=
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
  loop (cs0.length + 1) cs0 identity zeroC |>.map (fun (m, off, rest) => ([.matrix m off], rest))

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
    Except ClfError (List ClfOp × List Char) :=
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
    | Except.ok op => Except.ok ([op], rest)

/-! ## Exponent / Log / CDL / LUT handlers -/

/-- `clf_param`: one named per-channel parameter with defaults. -/
structure ClfParam where
  name : String
  (v0 v1 v2 : Float32)
  set : Bool
  deriving Repr

/-- `clf_read_params`: read the attributes of a parameter element
  (`name="value"`, optional `channel="R|G|B"`), then skip the
  element. Returns the updated parameter list (each entry's `set`
  flag records whether any of its values was supplied). -/
def clfReadParams (cs0 : List Char) (tag : String) (params : List ClfParam) :
    List ClfParam × List Char :=
  let n := params.length
  let rec attrs (fuel : Nat) (cs : List Char)
      (ch : Int) (tmp : List (Float32 × Bool)) :
      List (Float32 × Bool) × Int × List Char :=
    match fuel with
    | 0 => (tmp, ch, cs)
    | fuel + 1 =>
      let (found, key, val, rest) := xa cs
      if !found then (tmp, ch, rest)
      else if key == "channel" then
        let ch' := match val.toList.getD 0 ' ' with
          | 'R' => (0 : Int)
          | 'G' => (1 : Int)
          | 'B' => (2 : Int)
          | _ => (-2 : Int)
        attrs fuel rest ch' tmp
      else
        match (params.map (·.name)).findIdx? (fun nm => nm == key) with
        | none => attrs fuel rest ch tmp
        | some i =>
          if i ≥ n then attrs fuel rest ch tmp
          else
            match readF32 val.toList with
            | none => attrs fuel rest ch tmp
            | some (v, _) => attrs fuel rest ch (tmp.set i (v, true))
  let (tmp, ch, cs) := attrs (cs0.length + 1) cs0 (-1) (params.map (fun _ => (0.0, false)))
  let cs' := xskipElem cs tag
  if ch = -2 then (params, cs')
  else
    let updated := (List.range n).map (fun i =>
      let (v, has) := tmp.getD i (0.0, false)
      let p := params.getD i ⟨"", 0.0, 0.0, 0.0, false⟩
      if has then
        let setChan := fun (c : Nat) (x : Float32) =>
          if ch < 0 || ch = (c : Int) then v else x
        ⟨p.name, setChan 0 p.v0, setChan 1 p.v1, setChan 2 p.v2, true⟩
      else p)
    (updated, cs')

/-- `moncurve_params` (C, `toc_processor.c`): `Float64` intermediates,
  `Float32` outputs, with `powf` via `Tocio.Math.powf`. -/
def moncurveParams (gamma offset : Float32) :
    Float32 × Float32 × Float32 × Float32 × Float32 :=
  let G : Float := max (Float32.toFloat gamma) 1.000001
  let O : Float := max (Float32.toFloat offset) 1e-6
  let a : Float := (G - 1.0) / O
  let b : Float := O * G / ((G - 1.0) * (1.0 + O))
  let scale : Float32 := Float.toFloat32 (1.0 / (1.0 + O))
  let off : Float32 := Float.toFloat32 (O / (1.0 + O))
  let brk : Float32 := Float.toFloat32 (O / (G - 1.0))
  let pwr : Float32 := powf (Float.toFloat32 b) (Float.toFloat32 G)
  let slope : Float32 := Float.toFloat32 (a * Float32.toFloat pwr)
  let g2 : Float32 := Float.toFloat32 G
  (scale, off, g2, brk, slope)

/-- `toc_push_exp_linear`: MonCurve params for all four channels. -/
def pushExpLinear (gamma offset : List Float32) (inverse mirror : Bool) :
    ClfOp :=
  let ch := fun (i : Nat) =>
    moncurveParams (gamma.getD i 1.0) (offset.getD i 0.0)
  .expLinear
    (List.range 4 |>.map (fun i => (ch i).1))
    (List.range 4 |>.map (fun i => (ch i).2.1))
    (List.range 4 |>.map (fun i => (ch i).2.2.1))
    (List.range 4 |>.map (fun i => (ch i).2.2.2.1))
    (List.range 4 |>.map (fun i => (ch i).2.2.2.2))
    inverse mirror

/-- `clf_exponent`: Exponent styles (basic/monCurve, Mirror, Fwd/Rev). -/
def clfExponent (cs0 : List Char) (style0 : String) :
    Except ClfError (List ClfOp × List Char) :=
  let (mon, rest0) :=
    if clfPrefix style0 "monCurve" then (true, String.ofList (style0.toList.drop 8))
    else if clfPrefix style0 "basic" then (false, String.ofList (style0.toList.drop 5))
    else (false, style0)
  if !(clfPrefix style0 "monCurve") && !(clfPrefix style0 "basic") then
    Except.error .unsupported
  else
    let (mirror, rest1) :=
      if clfPrefix rest0 "Mirror" then (true, String.ofList (rest0.toList.drop 6))
      else (false, rest0)
    let rev := rest1 == "Rev"
    if rest1 != "Fwd" && !rev then Except.error .unsupported
    else
      let defaults : List ClfParam :=
        [⟨"exponent", 1.0, 1.0, 1.0, false⟩, ⟨"offset", 0.0, 0.0, 0.0, false⟩]
      let rec loop (fuel : Nat) (cs : List Char) (p : List ClfParam) :
          Except ClfError (List ClfParam × List Char) :=
        if fuel = 0 then Except.error .parse
        else
          let (isOpen, tag, rest) := xtag cs
          if !isOpen then
            match xskipClose rest with
            | (true, rest2) => Except.ok (p, rest2)
            | (false, _) => Except.error .parse
          else if tag == "ExponentParams" then
            let (p2, rest) := clfReadParams rest tag p
            loop (fuel - 1) rest p2
          else loop (fuel - 1) (xskipElem rest tag) p
      match loop (cs0.length + 1) cs0 defaults with
      | Except.error e => Except.error e
      | Except.ok (p, rest) =>
        let e0 := p.getD 0 ⟨"", 1.0, 1.0, 1.0, false⟩
        if !e0.set then Except.error .parse
        else if mon then
          let o1 := p.getD 1 ⟨"", 0.0, 0.0, 0.0, false⟩
          if !o1.set then Except.error .parse
          else
            Except.ok ([pushExpLinear [e0.v0, e0.v1, e0.v2, 1.0] [o1.v0, o1.v1, o1.v2, 0.0]
              rev mirror], rest)
        else
          let e := [e0.v0, e0.v1, e0.v2, 1.0].map (fun v =>
            if rev then (if v != 0.0 then 1.0 / v else 1.0) else v)
          Except.ok ([.exponent e mirror], rest)

/-- `toc_push_logcam` per-channel linear-segment computation:
  returns `(linear_slope, linear_offset)` — with an explicit
  `linearSlope` when given, else the C1-continuity derivation. -/
def logcamLin (base ls lo ns no brk : Float32) (lslope : Option Float32) :
    Float32 × Float32 :=
  let lnb : Float32 := log2f base * 0.6931471805599453
  let xb : Float32 := ns * brk + no
  let xbPos : Float32 := if xb > 0.0 then xb else 1e-30
  let yb : Float32 := ls * (log2f xbPos / log2f base) + lo
  let lsl : Float32 := lslope.getD (ls * ns / ((if xb != 0.0 then xb else 1e-30) * lnb))
  (lsl, yb - lsl * brk)

/-- `clf_log`: Log styles (log10/log2/antiLog*, linToLog/logToLin,
  cameraLinToLog/cameraLogToLin). -/
def clfLog (cs0 : List Char) (style : String) (empty : Bool) :
    Except ClfError (List ClfOp × List Char) :=
  let (simple, base0, inverse0, camera0) :=
    if style == "log10" then (true, (10.0 : Float32), false, false)
    else if style == "log2" then (true, (2.0 : Float32), false, false)
    else if style == "antiLog10" then (true, (10.0 : Float32), true, false)
    else if style == "antiLog2" then (true, (2.0 : Float32), true, false)
    else if style == "linToLog" then (false, (2.0 : Float32), false, false)
    else if style == "logToLin" then (false, (2.0 : Float32), true, false)
    else if style == "cameraLinToLog" then (false, (2.0 : Float32), false, true)
    else if style == "cameraLogToLin" then (false, (2.0 : Float32), true, true)
    else (false, (2.0 : Float32), false, false)
  if !(style == "log10" || style == "log2" || style == "antiLog10" ||
      style == "antiLog2" || style == "linToLog" || style == "logToLin" ||
      style == "cameraLinToLog" || style == "cameraLogToLin") then
    Except.error .unsupported
  else
    let defaults : List ClfParam :=
      [⟨"base", 2.0, 2.0, 2.0, false⟩,
       ⟨"logSideSlope", 1.0, 1.0, 1.0, false⟩,
       ⟨"logSideOffset", 0.0, 0.0, 0.0, false⟩,
       ⟨"linSideSlope", 1.0, 1.0, 1.0, false⟩,
       ⟨"linSideOffset", 0.0, 0.0, 0.0, false⟩,
       ⟨"linSideBreak", 0.0, 0.0, 0.0, false⟩,
       ⟨"linearSlope", 0.0, 0.0, 0.0, false⟩]
    let finish (p : List ClfParam) (rest : List Char) :
        Except ClfError (List ClfOp × List Char) :=
      if !simple then
        let base := (p.getD 0 ⟨"", 2.0, 2.0, 2.0, false⟩).v0
        if !(base > 0.0) || base == 1.0 then Except.error .parse
        else if camera0 then
          let brk := p.getD 5 ⟨"", 0.0, 0.0, 0.0, false⟩
          if !brk.set then Except.error .parse
          else
            let ls := p.getD 1 ⟨"", 1.0, 1.0, 1.0, false⟩
            let lo := p.getD 2 ⟨"", 0.0, 0.0, 0.0, false⟩
            let ns := p.getD 3 ⟨"", 1.0, 1.0, 1.0, false⟩
            let no := p.getD 4 ⟨"", 0.0, 0.0, 0.0, false⟩
            let lv := p.getD 6 ⟨"", 0.0, 0.0, 0.0, false⟩
            let chSel := fun (i : Nat) (x : List Float32) (d : Float32) =>
              match i with | 0 => x.getD 0 d | 1 => x.getD 1 d | _ => x.getD 2 d
            let logSl := List.range 3 |>.map (fun i => chSel i [ls.v0, ls.v1, ls.v2] 1.0)
            let logOf := List.range 3 |>.map (fun i => chSel i [lo.v0, lo.v1, lo.v2] 0.0)
            let linSl := List.range 3 |>.map (fun i => chSel i [ns.v0, ns.v1, ns.v2] 1.0)
            let linOf := List.range 3 |>.map (fun i => chSel i [no.v0, no.v1, no.v2] 0.0)
            let linBr := List.range 3 |>.map (fun i => chSel i [brk.v0, brk.v1, brk.v2] 0.0)
            let linPer := List.range 3 |>.map (fun i =>
              logcamLin base (logSl.getD i 1.0) (logOf.getD i 0.0)
                (linSl.getD i 1.0) (linOf.getD i 0.0) (linBr.getD i 0.0)
                (if lv.set then some (chSel i [lv.v0, lv.v1, lv.v2] 0.0) else none))
            let linSlo := linPer.map (·.1)
            let linOff' := linPer.map (·.2)
            Except.ok ([.logCam base inverse0 logSl logOf linSl linOf linBr linSlo linOff'], rest)
        else
          let ls := p.getD 1 ⟨"", 1.0, 1.0, 1.0, false⟩
          let lo := p.getD 2 ⟨"", 0.0, 0.0, 0.0, false⟩
          let ns := p.getD 3 ⟨"", 1.0, 1.0, 1.0, false⟩
          let no := p.getD 4 ⟨"", 0.0, 0.0, 0.0, false⟩
          Except.ok ([.log base inverse0 [ls.v0, ls.v1, ls.v2] [lo.v0, lo.v1, lo.v2]
            [ns.v0, ns.v1, ns.v2] [no.v0, no.v1, no.v2]], rest)
      else
        Except.ok ([.log base0 inverse0 [1.0, 1.0, 1.0] [0.0, 0.0, 0.0]
          [1.0, 1.0, 1.0] [0.0, 0.0, 0.0]], rest)
    if empty then finish defaults cs0
    else
      let rec loop (fuel : Nat) (cs : List Char) (p : List ClfParam) :
          Except ClfError (List ClfParam × List Char) :=
        if fuel = 0 then Except.error .parse
        else
          let (isOpen, tag, rest) := xtag cs
          if !isOpen then
            match xskipClose rest with
            | (true, rest2) => Except.ok (p, rest2)
            | (false, _) => Except.error .parse
          else if tag == "LogParams" then
            let (p2, rest) := clfReadParams rest tag p
            loop (fuel - 1) rest p2
          else loop (fuel - 1) (xskipElem rest tag) p
      match loop (cs0.length + 1) cs0 defaults with
      | Except.error e => Except.error e
      | Except.ok (p, rest) => finish p rest

/-- `toc_push_cdl`: forward is one CDL op; the inverse is three
  basic ops (inverse saturation matrix, inverse power, inverse
  slope/offset). -/
def pushCdl (sl of pw : List Float32) (sat : Float32) (clampVal inverse : Bool) :
    List ClfOp :=
  if inverse then
    let ny : Float32 := if sat != 0.0 then 1.0 / sat else 1.0
    let luma : List Float32 := [0.2126, 0.7152, 0.0722]
    let m : List Float32 := (List.range 16).map (fun idx =>
      let i := idx % 4
      let j := idx / 4
      if i < 3 && j < 3 then (if i == j then ny else 0.0) + (1.0 - ny) * luma.getD j 0.0
      else if idx == 15 then 1.0 else 0.0)
    let e : List Float32 := (List.range 4).map (fun i =>
      if i < 3 then (let v := pw.getD i 1.0; if v != 0.0 then 1.0 / v else 1.0) else 1.0)
    let scale : List Float32 := (List.range 4).map (fun i =>
      if i < 3 && sl.getD i 0.0 != 0.0 then 1.0 / sl.getD i 0.0 else 1.0)
    let offset : List Float32 := (List.range 4).map (fun i =>
      if i < 3 then -of.getD i 0.0 * scale.getD i 1.0 else 0.0)
    [.matrix m [0.0, 0.0, 0.0, 0.0], .exponent e false,
     .range scale offset [0.0, 0.0, 0.0, 0.0] [1.0, 1.0, 1.0, 1.0] clampVal clampVal]
  else [.cdl sl of pw sat clampVal]

/-- `clf_cdl`: ASC_CDL styles and SOP/SatNode children. -/
def clfCdl (cs0 : List Char) (style : String) :
    Except ClfError (List ClfOp × List Char) :=
  let (inverse, clampVal) :=
    if style == "" || style == "Fwd" then (false, true)
    else if style == "Rev" then (true, true)
    else if style == "FwdNoClamp" then (false, false)
    else if style == "RevNoClamp" then (true, false)
    else (false, true)
  if !(style == "" || style == "Fwd" || style == "Rev" ||
      style == "FwdNoClamp" || style == "RevNoClamp") then
    Except.error .unsupported
  else
    let rec inner (fuel : Nat) (cs : List Char)
        (st : List Float32 × List Float32 × List Float32 × Float32) :
        Except ClfError (List Float32 × List Float32 × List Float32 × Float32 × List Char) :=
      if fuel = 0 then Except.error .parse
      else
        let (isOpen, tag, rest) := xtag cs
        if !isOpen then
          match xskipClose rest with
          | (true, rest2) => Except.ok (st.1, st.2.1, st.2.2.1, st.2.2.2, rest2)
          | (false, _) => Except.error .parse
        else if (tag == "Slope" || tag == "Offset" || tag == "Power" || tag == "Saturation") then
          let want := if tag == "Saturation" then 1 else 3
          match xc rest with
          | (true, _) => Except.error .parse
          | (false, rest) =>
            let (vals, rest) := xfloats rest want
            if vals.length != want then Except.error .parse
            else
              let st' := if tag == "Slope" then (vals, st.2.1, st.2.2.1, st.2.2.2)
                        else if tag == "Offset" then (st.1, vals, st.2.2.1, st.2.2.2)
                        else if tag == "Power" then (st.1, st.2.1, vals, st.2.2.2)
                        else (st.1, st.2.1, st.2.2.1, vals.getD 0 1.0)
              inner (fuel - 1) (skipCloseTag rest) st'
        else inner (fuel - 1) (xskipElem rest tag) st
    let rec loop (fuel : Nat) (cs : List Char)
        (st : List Float32 × List Float32 × List Float32 × Float32) :
        Except ClfError (List Float32 × List Float32 × List Float32 × Float32 × List Char) :=
      if fuel = 0 then Except.error .parse
      else
        let (isOpen, tag, rest) := xtag cs
        if !isOpen then
          match xskipClose rest with
          | (true, rest2) => Except.ok (st.1, st.2.1, st.2.2.1, st.2.2.2, rest2)
          | (false, _) => Except.error .parse
        else if tag == "SOPNode" || tag == "SatNode" then
          match xc rest with
          | (true, rest) => loop (fuel - 1) rest st
          | (false, rest) =>
            match inner (fuel - 1) rest st with
            | Except.error e => Except.error e
            | Except.ok (sl, of, pw, sat, rest) => loop (fuel - 1) rest (sl, of, pw, sat)
        else loop (fuel - 1) (xskipElem rest tag) st
    match loop (cs0.length + 1) cs0 ([1, 1, 1], [0, 0, 0], [1, 1, 1], 1.0) with
    | Except.error e => Except.error e
    | Except.ok (sl, of, pw, sat, rest) =>
      Except.ok (pushCdl sl of pw sat clampVal inverse, rest)

/-- `clf_lut1d`: `<Array dim="length channels">` with 1- or
  3-component entries (replicated to 3 channels), divided by the out
  bit-depth scale. -/
def clfLut1d (cs0 : List Char) (outS : Float32) :
    Except ClfError (List ClfOp × List Char) :=
  let rec loop (fuel : Nat) (cs : List Char)
      (data : Option (Nat × Nat × List Float32)) :
      Except ClfError (Nat × Nat × List Float32 × List Char) :=
    if fuel = 0 then Except.error .parse
    else
      let (isOpen, tag, rest) := xtag cs
      if !isOpen then
        match xskipClose rest, data with
        | (true, rest2), some (ln, ch, d) => Except.ok (ln, ch, d, rest2)
        | (false, _), _ => Except.error .parse
        | (_, _), none => Except.error .parse
      else if tag == "Array" then
        let (dims, rest) := arrayDims rest
        if data.isSome then Except.error .parse
        else if dims.length != 2 then Except.error .unsupported
        else
          let length := dims.getD 0 0
          let channels := dims.getD 1 0
          if (channels != 1 && channels != 3) || length < 2 || length > (1 <<< 20) then
            Except.error .parse
          else if !spiValuesFit (length * channels) rest.length then
            Except.error .parse
          else
            let (tmp, rest) := xfloats rest (length * channels)
            if tmp.length != length * channels then Except.error .parse
            else
              let data := (List.range (length * 3)).map (fun i =>
                let row := i / 3
                let c := i % 3
                (if c < channels then tmp.getD (row * channels + c) 0.0
                 else tmp.getD (row * channels + channels - 1) 0.0) / outS)
              loop (fuel - 1) (skipCloseTag rest) (some (length, channels, data))
      else loop (fuel - 1) (xskipElem rest tag) data
  loop (cs0.length + 1) cs0 none |>.map (fun (ln, _, d, rest) => ([.lut1d ln d], rest))

/-- `clf_lut3d`: `<Array dim="N N N 3">` entries stored blue-fastest
  in the file; transposed to the RED-fastest layout (as C does) and
  divided by the out bit-depth scale. -/
def clfLut3d (cs0 : List Char) (tetra : Bool) (outS : Float32) :
    Except ClfError (List ClfOp × List Char) :=
  let rec loop (fuel : Nat) (cs : List Char)
      (data : Option (Nat × List Float32)) :
      Except ClfError (Nat × List Float32 × List Char) :=
    if fuel = 0 then Except.error .parse
    else
      let (isOpen, tag, rest) := xtag cs
      if !isOpen then
        match xskipClose rest, data with
        | (true, rest2), some (sz, d) => Except.ok (sz, d, rest2)
        | (false, _), _ => Except.error .parse
        | (_, _), none => Except.error .parse
      else if tag == "Array" then
        let (dims, rest) := arrayDims rest
        if data.isSome then Except.error .parse
        else if dims.length != 4 || dims.getD 3 0 != 3 then Except.error .unsupported
        else
          let size := dims.getD 0 0
          if dims.getD 1 0 != size || dims.getD 2 0 != size || size < 2 || size > 256 then
            Except.error .parse
          else if !spiValuesFit (size * size * size * 3) rest.length then
            Except.error .parse
          else
            let need := size * size * size * 3
            let (file, rest) := xfloats rest need
            if file.length != need then Except.error .parse
            else
              let data := (List.range (size * size * size)).map (fun pos =>
                let ir := pos % size
                let ig := (pos / size) % size
                let ib := pos / (size * size)
                let src := ((ir * size + ig) * size + ib) * 3
                [file.getD (src + 0) 0.0 / outS,
                 file.getD (src + 1) 0.0 / outS,
                 file.getD (src + 2) 0.0 / outS])
                |>.flatten
              loop (fuel - 1) (skipCloseTag rest) (some (size, data))
      else loop (fuel - 1) (xskipElem rest tag) data
  loop (cs0.length + 1) cs0 none |>.map (fun (sz, d, rest) => ([.lut3d sz d tetra], rest))

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
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if empty then Except.error .parse
            else if tag.toList.getD 0 ' ' == 'M' then
              match clfMatrix rest3 inS outS with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if tag.toList.getD 0 ' ' == 'R' then
              match clfRange rest3 inS outS noclamp with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if tag.toList.getD 0 ' ' == 'E' then
              match clfExponent rest3 style with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if tag.toList.getD 1 ' ' == 'o' then
              match clfLog rest3 style false with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if tag.toList.getD 0 ' ' == 'A' then
              match clfCdl rest3 style with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else if tag.toList.getD 3 ' ' == '1' then
              match clfLut1d rest3 outS with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
            else
              match clfLut3d rest3 tetra outS with
              | Except.error e => Except.error e
              | Except.ok (ops, rest4) => nodes (fuel - 1) rest4 (acc ++ ops)
          else
            let (_, rest2) := xc rest
            match unknownSkipLoop (rest2.length + 1) rest2 tag with
            | Except.error e => Except.error e
            | Except.ok rest3 => nodes (fuel - 1) rest3 acc
    nodes (cs2.length + 1) cs2 []



end Tocio
