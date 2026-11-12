/-
  TinyEXR - Lean 4 formalization of the tocio processor build
  (`toc_processor.c`): config + endpoints -> flat op list.

  The model pins the *pipeline construction*: which ops appear and in
  which order for a colorspace->colorspace conversion and for a
  display/view view build. It covers the transform walk (groups,
  directions, colorspace references, fixed-function styles), the
  reference-space bridging through the default view transform, view
  looks with their process space, shared views, and `<USE_DISPLAY_NAME>`.
  Numeric op parameters are covered by the kernel gates
  (`tocio-diff`, `tocio-lut-diff`, `tocio-clf-diff`, ...); this model
  tracks op kinds and the fixed-function style ids.

  FileTransform and BuiltinTransform payloads are outside the model
  (they need the file reader / the builtin table): the model reports
  UNSUPPORTED for them, and the differential vectors do not use them.

  Termination: every recursive call consumes one unit of a work fuel
  (the vectors are tiny; the depth counter `TOC_MAX_WALK_DEPTH` = 64 is
  threaded separately and is exact).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ConfigQuery

namespace Tocio

set_option linter.unusedVariables false

/-- Lowered op kinds (kind-level model). `fixed` carries the
fixed-function style id, whose inverse is the even/odd partner. -/
inductive POp where
  | matrix
  | range
  | exponent
  | expLinear
  | log
  | logCamera
  | cdl
  | lut1d
  | lut3d
  | fixed (style : Nat)
  | acesOutput
  deriving Repr, DecidableEq

def pOpName : POp → String
  | .matrix => "MATRIX"
  | .range => "RANGE"
  | .exponent => "EXPONENT"
  | .expLinear => "EXP_LINEAR"
  | .log => "LOG"
  | .logCamera => "LOG_CAMERA"
  | .cdl => "CDL"
  | .lut1d => "LUT1D"
  | .lut3d => "LUT3D"
  | .fixed s => "FIXEDFUNC(" ++ toString s ++ ")"
  | .acesOutput => "ACES_OUTPUT"

/-- The node's `!<Tag>`. -/
def tagOf : YTree → Option String
  | .scalar t _ => t
  | .seq t _ => t
  | .map t _ => t

/-! ## Parameter-presence helpers (mirroring `read_vec` / `read_scalar`) -/

/-- `read_vec` returns a positive count for a scalar or a non-empty
sequence, zero otherwise. -/
def vecPresent (o : Option YTree) : Bool :=
  match o with
  | some (.seq _ xs) => !xs.isEmpty
  | some (.scalar _ _) => true
  | _ => false

def isDigit (c : Char) : Bool := c ≥ '0' && c ≤ '9'

def digitVal (c : Char) : Float := (c.toNat - '0'.toNat).toFloat

/-- The fractional part of `toc_parse_float`: digits after the point,
each divided by the running power of ten. -/
def parseFrac : List Char → Float → Float
  | [], _ => 0.0
  | c :: rest, sc => digitVal c / sc + parseFrac rest (sc * 10.0)

/-- `toc_parse_float`'s grammar (leading spaces/commas, optional sign,
digits with an optional fraction, optional exponent). Values, not just
acceptance, are needed for the Range bound checks. -/
def parseCfgFloat (s : String) : Option Float :=
  let cs := s.toList.dropWhile
    (fun c => c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == ',')
  let (neg, cs) :=
    match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let intPart := cs.takeWhile isDigit
  let cs1 := cs.drop intPart.length
  let (fracPart, cs2) :=
    match cs1 with
    | '.' :: r => (r.takeWhile isDigit, r.drop (r.takeWhile isDigit).length)
    | _ => ([], cs1)
  if intPart.isEmpty && fracPart.isEmpty then none
  else
    let v := intPart.foldl (fun a c => a * 10.0 + digitVal c) 0.0
    let frac := parseFrac fracPart 10.0
    let base := (v + frac) * (if neg then -1.0 else 1.0)
    match cs2 with
    | 'e' :: r => applyExp base r
    | 'E' :: r => applyExp base r
    | _ => some base
where
  applyExp (base : Float) (r : List Char) : Option Float :=
    let (esign, r) :=
      match r with
      | '-' :: r' => (true, r')
      | '+' :: r' => (false, r')
      | r' => (false, r')
    let ds := r.takeWhile isDigit
    if ds.isEmpty then some base
    else
      let exp := ds.foldl (fun a c => if a < 10000 then a * 10 + (c.toNat - '0'.toNat) else a) 0
      let m := (List.range (min exp 400)).foldl (fun a _ => a * 10.0) 1.0
      some (if esign then base / m else base * m)

/-- `read_scalar` succeeds only for a scalar that parses as a float. -/
def scalarNumeric (o : Option YTree) : Bool :=
  match o with
  | some (.scalar _ s) => (parseCfgFloat s).isSome
  | _ => false

/-- A float parameter (`0.0` when missing or unparsable, as the C). -/
def scalarFloat (o : Option YTree) : Float :=
  match o with
  | some (.scalar _ s) => (parseCfgFloat s).getD 0.0
  | _ => 0.0

/-! ## Fixed-function styles (`toc_lower_fixedfunc`) -/

/-- Forward style id per OCIO style name; inverses are the odd partners,
as the C's `toc_invert_op` toggles the low bit. -/
def ffStyleId : String → Option Nat
  | "REC2100_SURROUND" => some 6
  | "Rec2100Surround" => some 6
  | "ACES_Glow_03" => some 8
  | "ACES_Glow_10" => some 0
  | "ACES_Dark_To_Dim_10" => some 2
  | "ACES_Gamut_Comp_13" => some 4
  | "ACES_Red_Mod_03" => some 10
  | "ACES_Red_Mod_10" => some 12
  | "RGB_TO_HSV" => some 14
  | "HSV_TO_RGB" => some 15
  | "XYZ_TO_xyY" => some 16
  | "xyY_TO_XYZ" => some 17
  | "XYZ_TO_uvY" => some 18
  | "uvY_TO_XYZ" => some 19
  | "XYZ_TO_LUV" => some 20
  | "LUV_TO_XYZ" => some 21
  | _ => none

def ffInvert (id : Nat) : Nat := if id % 2 == 0 then id + 1 else id - 1

/-! ## Color-space hooks -/

/-- `cs_is_data`: the (role-resolved) colorspace is flagged `isdata`. -/
def isDataCs (root : YTree) (name : String) : Bool :=
  match findColorspace root (resolveRole root name) with
  | some cs => isData cs
  | none => false

/-- `cs_ref_domain`: `true` for display-referred. Explicit display
attributes win, then explicit scene/v1 attributes, then the section the
colorspace was declared in. -/
def refDomain (root : YTree) (name : String) : Bool :=
  let rn := resolveRole root name
  match findColorspace root rn with
  | none => false
  | some cs =>
    if (cs.mapGet "to_display_reference").isSome ||
       (cs.mapGet "from_display_reference").isSome then true
    else if (cs.mapGet "to_scene_reference").isSome ||
            (cs.mapGet "from_scene_reference").isSome ||
            (cs.mapGet "to_reference").isSome ||
            (cs.mapGet "from_reference").isSome then false
    else inDisplaySection root rn

/-- `toc_cfg_cs_transform` as a node plus its invert flag. -/
def csTransformNode (cs : YTree) (wantToRef : Bool) : Option (YTree × Bool) :=
  let toAttr := firstPresent cs
    ["to_reference", "to_scene_reference", "to_display_reference"]
  let fromAttr := firstPresent cs
    ["from_reference", "from_scene_reference", "from_display_reference"]
  let pick (a : String) (inv : Bool) : Option (YTree × Bool) :=
    (cs.mapGet a).map (fun n => (n, inv))
  if wantToRef then
    match toAttr with
    | some a => pick a false
    | none => match fromAttr with
              | some a => pick a true
              | none => none
  else
    match fromAttr with
    | some a => pick a false
    | none => match toAttr with
              | some a => pick a true
              | none => none

/-! ## Pipeline construction -/

def walkMaxDepth : Nat := 64

/-- Work-fuel entry (every recursive call consumes one unit). -/
def procFuel : Nat := 100000

mutual
/-- `walk` with its depth cap and one fuel unit. -/
def pWalk (root : YTree) (depth fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    if depth ≥ walkMaxDepth then .error "PARSE"
    else pWalkNode root (depth + 1) f node invert

/-- `walk_node`. -/
def pWalkNode (root : YTree) (depth fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    let dirInv :=
      match getScalar node "direction" with
      | some "inverse" => !invert
      | _ => invert
    match tagOf node with
    | none => .ok []
    | some tag =>
      if tag = "GroupTransform" then
        match node.mapGet "children" with
        | some (.seq _ xs) =>
          if !dirInv then pWalkAll root depth f xs false
          else pWalkAllRev root depth f xs true
        | _ => .ok []
      else if tag = "ColorSpaceTransform" then
        match getScalar node "src", getScalar node "dst" with
        | some src, some dst =>
          let (s, d) := if dirInv then (dst, src) else (src, dst)
          (pEmitToRef root depth f s false).bind (fun a =>
            (pEmitFromRef root depth f d false).map (fun b => a ++ b))
        | _, _ => .error "PARSE"
      else if tag = "FileTransform" then
        if (getScalar node "src").isNone then .error "PARSE"
        else .error "UNSUPPORTED"
      else if tag = "BuiltinTransform" then
        if (getScalar node "style").isNone then .error "PARSE"
        else .error "UNSUPPORTED"
      else if tag = "FixedFunctionTransform" then pLowerFixed f node dirInv
      else pLowerTransform f node dirInv

/-- Walk a child list forward. -/
def pWalkAll (root : YTree) (depth fuel : Nat) (xs : List YTree) (invert : Bool) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    match xs with
    | [] => .ok []
    | x :: rest =>
      (pWalk root depth f x invert).bind (fun a =>
        (pWalkAll root depth f rest invert).map (fun b => a ++ b))

/-- Walk a child list in reverse (inverted group). -/
def pWalkAllRev (root : YTree) (depth fuel : Nat) (xs : List YTree)
    (invert : Bool) : Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    match xs.reverse with
    | [] => .ok []
    | x :: rest =>
      (pWalk root depth f x invert).bind (fun a =>
        (pWalkAllRev root depth f rest.reverse invert).map (fun b => a ++ b))

/-- `emit_to_ref`. -/
def pEmitToRef (root : YTree) (depth fuel : Nat) (csName : String)
    (invert : Bool) : Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    match findColorspace root (resolveRole root csName) with
    | none => .error "NOT_FOUND"
    | some cs =>
      if isData cs then .ok []
      else
        match csTransformNode cs true with
        | none => .ok []
        | some (t, needinv) => pWalk root depth f t (invert != needinv)

/-- `emit_from_ref`. -/
def pEmitFromRef (root : YTree) (depth fuel : Nat) (csName : String)
    (invert : Bool) : Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    match findColorspace root (resolveRole root csName) with
    | none => .error "NOT_FOUND"
    | some cs =>
      if isData cs then .ok []
      else
        match csTransformNode cs false with
        | none => .ok []
        | some (t, needinv) => pWalk root depth f t (invert != needinv)

/-- `toc_lower_transform`. -/
def pLowerTransform (fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | _ + 1 =>
    match tagOf node with
    | none => .ok []
    | some tag =>
      if tag = "MatrixTransform" then .ok [.matrix]
      else if tag = "ExponentTransform" then .ok [.exponent]
      else if tag = "ExponentWithLinearTransform" then .ok [.expLinear]
      else if tag = "LogTransform" || tag = "LogAffineTransform" then .ok [.log]
      else if tag = "LogCameraTransform" then
        if vecPresent (node.mapGet "lin_side_break") ||
           vecPresent (node.mapGet "linSideBreak") then .ok [.logCamera]
        else .error "PARSE"
      else if tag = "CDLTransform" then
        if invert then .ok [.matrix, .exponent, .range] else .ok [.cdl]
      else if tag = "RangeTransform" then
        let hasMinIn := scalarNumeric (node.mapGet "minInValue")
        let hasMaxIn := scalarNumeric (node.mapGet "maxInValue")
        let hasMinOut := scalarNumeric (node.mapGet "minOutValue")
        let hasMaxOut := scalarNumeric (node.mapGet "maxOutValue")
        if hasMinIn != hasMinOut || hasMaxIn != hasMaxOut then .error "PARSE"
        else if !hasMinIn && !hasMaxIn then .error "PARSE"
        else if hasMinIn && hasMaxIn then
          if !(scalarFloat (node.mapGet "maxInValue") >
               scalarFloat (node.mapGet "minInValue")) then .error "PARSE"
          else .ok [.range]
        else .ok [.range]
      else .error "UNSUPPORTED"

/-- `toc_lower_fixedfunc` (style id only). -/
def pLowerFixed (fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | _ + 1 =>
    match getScalar node "style" with
    | none => .error "PARSE"
    | some style =>
      match ffStyleId style with
      | some id => .ok [.fixed (if invert then ffInvert id else id)]
      | none => .error "UNSUPPORTED"

/-- Apply a view's looks in order (each look through its process space
when present); the look list is capped at 8 by the caller. -/
def pApplyLooks (root : YTree) (fuel : Nat) (looks : List String) :
    Except String (List POp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    match looks with
    | [] => .ok []
    | lkName :: rest =>
      match findLook root lkName with
      | none => .error "NOT_FOUND"
      | some lk =>
        match getScalar lk "process_space" with
        | some ps =>
          (pEmitFromRef root 0 f ps false).bind (fun a =>
            (match lk.mapGet "transform" with
             | some tf => pWalk root 0 f tf false
             | none => .ok []).bind (fun b =>
              (pEmitToRef root 0 f ps false).bind (fun c =>
                (pApplyLooks root f rest).map (fun d => a ++ b ++ c ++ d))))
        | none =>
          (match lk.mapGet "transform" with
           | some tf => pWalk root 0 f tf false
           | none => .ok []).bind (fun a =>
            (pApplyLooks root f rest).map (fun b => a ++ b))
end

/-! ## Public builders -/

/-- `toc_processor_from_colorspaces`. -/
def pFromColorspaces (root : YTree) (src dst : String) :
    Except String (List POp) :=
  if isDataCs root src || isDataCs root dst then .ok []
  else
    (pEmitToRef root 0 procFuel src false).bind (fun a =>
      let bridge : Except String (List POp) :=
        if refDomain root src != refDomain root dst then
          let vt := defaultViewTransform root
          let baseInv := refDomain root src
          let chosen : Option (YTree × Bool) :=
            match vt with
            | none => none
            | some v =>
              match v.mapGet "from_scene_reference" with
              | some tf => some (tf, baseInv)
              | none =>
                match v.mapGet "from_reference" with
                | some tf => some (tf, baseInv)
                | none =>
                  match v.mapGet "to_scene_reference" with
                  | some tf => some (tf, !baseInv)
                  | none => (v.mapGet "to_reference").map (fun tf => (tf, !baseInv))
          match chosen with
          | none => .error "UNSUPPORTED"
          | some (tf, inv) => pWalk root 0 procFuel tf inv
        else .ok []
      bridge.bind (fun b =>
        (pEmitFromRef root 0 procFuel dst false).map (fun c => a ++ b ++ c)))

/-- The views of a display, or `none` when the mapping/sequence is absent. -/
def displayViews (root : YTree) (display : String) : Option (List YTree) :=
  match (root.mapGet "displays").bind (fun d => d.mapGet display) with
  | some (.seq _ xs) => some xs
  | _ => none

/-- A view defined in `shared_views`. -/
def findSharedView (root : YTree) (view : String) : Option YTree :=
  match root.mapGet "shared_views" with
  | some (.seq _ xs) => xs.find? (fun it => getScalar it "name" == some view)
  | _ => none

/-- Resolve a view name in a display's view list (`!<Views>` entries
reference `shared_views`). -/
def findView (root : YTree) : List YTree → String → Option YTree
  | [], _ => none
  | it :: rest, view =>
    match it with
    | .seq _ names =>
      if names.any (fun x => x.scalarVal == some view) then
        findSharedView root view
      else findView root rest view
    | _ =>
      if getScalar it "name" == some view then some it
      else findView root rest view

/-- `toc_processor_from_display_view`. -/
def pFromDisplayView (root : YTree) (srcCs display view : String) :
    Except String (List POp) :=
  match displayViews root display with
  | none => .error "NOT_FOUND"
  | some views =>
    match findView root views view with
    | none => .error "NOT_FOUND"
    | some vnode =>
      let viewCs := getScalar vnode "colorspace"
      let viewVt := getScalar vnode "view_transform"
      if viewCs.isNone && viewVt.isNone then .error "UNSUPPORTED"
      else if isDataCs root srcCs ||
              (match viewCs with
               | some c => isDataCs root c
               | none => false) then .ok []
      else
        (pEmitToRef root 0 procFuel srcCs false).bind (fun ops0 =>
          (pApplyLooks root procFuel ((viewLooks vnode).take 8)).bind (fun ops1 =>
            let vtOps : Except String (List POp) :=
              match viewVt with
              | none => .ok []
              | some vtName =>
                match findViewTransform root vtName with
                | none => .error "NOT_FOUND"
                | some vt =>
                  match vt.mapGet "from_scene_reference" with
                  | some tf => pWalk root 0 procFuel tf false
                  | none =>
                    match vt.mapGet "from_reference" with
                    | some tf => pWalk root 0 procFuel tf false
                    | none =>
                      match vt.mapGet "to_scene_reference" with
                      | some tf => pWalk root 0 procFuel tf true
                      | none =>
                        match vt.mapGet "to_reference" with
                        | some tf => pWalk root 0 procFuel tf true
                        | none =>
                          match vt.mapGet "from_display_reference" with
                          | none => .error "UNSUPPORTED"
                          | some dtf =>
                            match defaultViewTransform root with
                            | none => .error "UNSUPPORTED"
                            | some dvt =>
                              let btf :=
                                match dvt.mapGet "from_scene_reference" with
                                | some b => some b
                                | none => dvt.mapGet "from_reference"
                              match btf with
                              | none => .error "UNSUPPORTED"
                              | some b =>
                                (pWalk root 0 procFuel b false).bind (fun x =>
                                  (pWalk root 0 procFuel dtf false).map
                                    (fun y => x ++ y))
            vtOps.bind (fun ops2 =>
              let viewDc : Option String :=
                match viewCs with
                | some c => some c
                | none => getScalar vnode "display_colorspace"
              let dc :=
                match viewDc with
                | some c => if c = "<USE_DISPLAY_NAME>" then some display else some c
                | none => none
              match dc with
              | none => .ok (ops0 ++ ops1 ++ ops2)
              | some c => (pEmitFromRef root 0 procFuel c false).map
                  (fun ops3 => ops0 ++ ops1 ++ ops2 ++ ops3))))

/-! ## Result rendering (mirrors `test/v3/config_vectors.c`'s `pq` records) -/

/-- `ok:K1,K2,...` or `err:CODE`. -/
def renderProcResult (r : Except String (List POp)) : String :=
  match r with
  | .error e => "err:" ++ e
  | .ok ops => "ok:" ++ String.intercalate "," (ops.map pOpName)

end Tocio
