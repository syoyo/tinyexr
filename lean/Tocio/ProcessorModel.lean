/-
  TinyEXR - Lean 4 formalization of the tocio processor build
  (`toc_processor.c`): config + endpoints -> flat op list.

  The model pins the pipeline *construction*: which ops appear and in
  which order for a colorspace->colorspace conversion and for a
  display/view view build (transform walk with groups/directions,
  colorspace references, fixed-function styles, reference-space bridging
  through the default view transform, view looks with their process
  space, shared views, `<USE_DISPLAY_NAME>`), together with the numeric
  parameters each lowering produces (see `Tocio/ProcessorParams.lean`).

  Numeric parameters are covered bit-for-bit by
  `make tocio-proc-params-diff`; the kernel gates cover op semantics.
  FileTransform and BuiltinTransform payloads are outside the model
  (UNSUPPORTED, never vectorized).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ProcessorParams

namespace Tocio

set_option linter.unusedVariables false

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

/-! ## Numeric lowering (`toc_lower_transform`, `toc_lower_fixedfunc`) -/

/-- `read_scalar`-based Range parameter. -/
def scalarNumeric (o : Option YTree) : Bool :=
  match o with
  | some (.scalar _ s) => (parseCfgFloat s).isSome
  | _ => false

def scalarFloat (o : Option YTree) : Float :=
  match o with
  | some (.scalar _ s) => (parseCfgFloat s).getD 0.0
  | _ => 0.0

def zeros (n : Nat) : List FB := List.replicate n 0

/-- `MonCurve` parameters from (gamma, offset): scale, offset, gamma,
breakpoint, slope (C `moncurve_params`, double intermediates). -/
def moncurve (gamma offset : FB) : List FB :=
  let G : Float := if (f32of gamma).toFloat < 1.000001 then 1.000001 else (f32of gamma).toFloat
  let O : Float := if (f32of offset).toFloat < 1e-6 then 1e-6 else (f32of offset).toFloat
  let a := (G - 1.0) / O
  let b := O * G / ((G - 1.0) * (1.0 + O))
  let f (x : Float) : FB := fbits (Float.toFloat32 x)
  let slope := a * (powf (Float.toFloat32 b) (Float.toFloat32 G)).toFloat
  [f (1.0 / (1.0 + O)), f (O / (1.0 + O)), f G, f (O / (G - 1.0)), f slope]

def lowerMatrix (node : YTree) (invert : Bool) : Except String (List COp) :=
  let ident : List FB := [fconst 1, 0, 0, 0, 0, fconst 1, 0, 0, 0, 0, fconst 1, 0,
    0, 0, 0, fconst 1]
  let (rm0, cnt) := readVec node "matrix" 16 ident
  let rm := if cnt == 16 then rm0 else ident
  let (off, _) := readVec node "offset" 4 (zeros 4)
  if !invert then .ok [.matrix (transpose4 rm) off]
  else
    match inv4x4 rm with
    | none => .error "NONINVERTIBLE"
    | some inv =>
      let tmp := matvec4 inv off
      .ok [.matrix (transpose4 inv) (tmp.map fneg)]

def lowerExponent (node : YTree) (invert : Bool) : Except String (List COp) :=
  let (e, _) := readVec node "value" 4 [fconst 1, fconst 1, fconst 1, fconst 1]
  let e' := if invert then e.map finv else e
  .ok [.exponent e' false]

def lowerExpLinear (node : YTree) (invert : Bool) : Except String (List COp) :=
  let (gamma, _) := readVec node "gamma" 4 [fconst 1, fconst 1, fconst 1, fconst 1]
  let (offset, _) := readVec node "offset" 4 (zeros 4)
  let mc := (List.range 4).map (fun i => moncurve (fuget gamma i) (fuget offset i))
  let col (j : Nat) : List FB := mc.map (fun l => fuget l j)
  .ok [.expLinear (col 0) (col 1) (col 2) (col 3) (col 4) invert false]

def lowerLog (node : YTree) (invert : Bool) : Except String (List COp) :=
  let base := readScalarD node "base" (fconst 2)
  let (ls, _) := readVec2 node "log_side_slope" "logSideSlope" 3 [fconst 1, fconst 1, fconst 1]
  let (lo, _) := readVec2 node "log_side_offset" "logSideOffset" 3 (zeros 3)
  let (ns, _) := readVec2 node "lin_side_slope" "linSideSlope" 3 [fconst 1, fconst 1, fconst 1]
  let (no, _) := readVec2 node "lin_side_offset" "linSideOffset" 3 (zeros 3)
  .ok [.log ls lo ns no base invert]

def lowerLogCamera (node : YTree) (invert : Bool) : Except String (List COp) :=
  let base := readScalarD node "base" (fconst 2)
  let (ls, _) := readVec2 node "log_side_slope" "logSideSlope" 3 [fconst 1, fconst 1, fconst 1]
  let (lo, _) := readVec2 node "log_side_offset" "logSideOffset" 3 (zeros 3)
  let (ns, _) := readVec2 node "lin_side_slope" "linSideSlope" 3 [fconst 1, fconst 1, fconst 1]
  let (no, _) := readVec2 node "lin_side_offset" "linSideOffset" 3 (zeros 3)
  let (brk, bn) := readVec2 node "lin_side_break" "linSideBreak" 3 (zeros 3)
  if bn == 0 then .error "PARSE"
  else
    let (lslRaw, ln) := readVec2 node "linear_slope" "linearSlope" 3 (zeros 3)
    let lnb := fmul (fbits (log2f (f32of base))) (fconst 0.6931471805599453)
    let chan (i : Nat) : FB × FB :=
      let xb := fadd (fmul (fuget ns i) (fuget brk i)) (fuget no i)
      let xbsafe := if f32of xb > 0.0 then xb else fconst 1e-30
      let yb := fadd (fmul (fuget ls i)
        (fdiv (fbits (log2f (f32of xbsafe))) (fbits (log2f (f32of base))))) (fuget lo i)
      let lsl := if ln != 0 then fuget lslRaw i
                 else fdiv (fmul (fuget ls i) (fuget ns i))
                        (fmul (if f32of xb != 0.0 then xb else fconst 1e-30) lnb)
      (lsl, fsub yb (fmul lsl (fuget brk i)))
    let pairs := (List.range 3).map chan
    let lsl := pairs.map (·.1)
    let loff := pairs.map (·.2)
    .ok [.logCamera ls lo ns no brk lsl loff base invert]

def lowerCdl (node : YTree) (invert : Bool) : Except String (List COp) :=
  let (sl, _) := readVec node "slope" 3 [fconst 1, fconst 1, fconst 1]
  let (of, _) := readVec node "offset" 3 (zeros 3)
  let (pw, _) := readVec node "power" 3 [fconst 1, fconst 1, fconst 1]
  let sat := readScalarD node "sat" (fconst 1)
  let clampv := match getScalar node "style" with
    | some s => s != "noclamp"
    | none => true
  if !invert then .ok [.cdl sl of pw sat (zeros 3) clampv false]
  else
    let ny := finv sat
    let luma : List FB := [fconst 0.2126, fconst 0.7152, fconst 0.0722]
    let m := (List.range 16).map (fun idx =>
      let i := idx % 4
      let j := idx / 4
      if i < 3 && j < 3 then
        fadd (if i == j then ny else 0) (fmul (fsub (fconst 1) ny) (fuget luma j))
      else if idx == 15 then fconst 1 else 0)
    let e := (List.range 4).map (fun i => if i < 3 then finv (fuget pw i) else fconst 1)
    let rscale := (List.range 4).map (fun i => if i < 3 then finv (fuget sl i) else fconst 1)
    let roff := (List.range 4).map (fun i =>
      if i < 3 then fmul (fneg (fuget of i)) (fuget rscale i) else 0)
    .ok [.matrix m (zeros 4), .exponent e false,
      .range rscale roff (zeros 4) [fconst 1, fconst 1, fconst 1, fconst 1] clampv clampv]

/-- `toc_push_range` plus the in-place inverse (`toc_invert_op`). -/
def lowerRange (node : YTree) (invert : Bool) : Except String (List COp) :=
  let hasMinIn := scalarNumeric (node.mapGet "minInValue")
  let hasMaxIn := scalarNumeric (node.mapGet "maxInValue")
  let hasMinOut := scalarNumeric (node.mapGet "minOutValue")
  let hasMaxOut := scalarNumeric (node.mapGet "maxOutValue")
  if hasMinIn != hasMinOut || hasMaxIn != hasMaxOut then .error "PARSE"
  else if !hasMinIn && !hasMaxIn then .error "PARSE"
  else if hasMinIn && hasMaxIn &&
          !(scalarFloat (node.mapGet "maxInValue") >
            scalarFloat (node.mapGet "minInValue")) then .error "PARSE"
  else
    let minIn := nodeFloat (node.mapGet "minInValue")
    let maxIn := nodeFloat (node.mapGet "maxInValue")
    let minOut := nodeFloat (node.mapGet "minOutValue")
    let maxOut := nodeFloat (node.mapGet "maxOutValue")
    let full := hasMinIn && hasMaxIn
    let scale : FB :=
      if full then fdiv (fsub maxOut minOut) (fsub maxIn minIn) else fconst 1
    let offset : FB :=
      if full then fsub minOut (fmul minIn scale)
      else if hasMinIn then fsub minOut minIn else fsub maxOut maxIn
    let unb : FB := fconst 3.4e38
    let negUnb : FB := fconst (-3.4e38)
    let mkScale := (List.range 4).map (fun i => if i < 3 then scale else fconst 1)
    let mkOff := (List.range 4).map (fun i => if i < 3 then offset else 0)
    let mkMin := (List.range 4).map (fun i => if i < 3 && hasMinIn then minOut else negUnb)
    let mkMax := (List.range 4).map (fun i => if i < 3 && hasMaxIn then maxOut else unb)
    let style := getScalar node "style"
    let noclamp := match style with
      | some s => s == "noClamp"
      | none => false
    let clampv := !(noclamp && full)
    if !invert then
      .ok [.range mkScale mkOff mkMin mkMax clampv clampv]
    else
      -- toc_invert_op on the Range op: map the forward output bounds back
      -- through the inverse (the C compares against +-3.0e38, not the
      -- 3.4e38 unbounded marker).
      let ns := mkScale.map finv
      let no := (List.zip mkOff ns).map (fun (o, s) => fmul (fneg o) s)
      let thrHi : FB := fconst 3.0e38
      let thrLo : FB := fconst (-3.0e38)
      let aOf (i : Nat) : FB :=
        let lo := fuget mkMin i
        if f32of lo <= f32of thrLo then lo
        else fadd (fmul lo (fuget ns i)) (fuget no i)
      let bOf (i : Nat) : FB :=
        let hi := fuget mkMax i
        if f32of hi >= f32of thrHi then hi
        else fadd (fmul hi (fuget ns i)) (fuget no i)
      let newMin := (List.range 4).map (fun i =>
        if f32of (aOf i) < f32of (bOf i) then aOf i else bOf i)
      let newMax := (List.range 4).map (fun i =>
        if f32of (aOf i) < f32of (bOf i) then bOf i else aOf i)
      .ok [.range ns no newMin newMax clampv clampv]

/-- `parse_param`: the `params` sequence entry at `idx`, or the default. -/
def paramAt (params : Option YTree) (idx : Nat) (dflt : Float32) : FB :=
  match params with
  | some (.seq _ xs) =>
    if xs.length > idx then
      match (xs[idx]?).bind (·.scalarVal) with
      | some s => (parseCfgFloat s).map (fun d => fbits (Float.toFloat32 d)) |>.getD (fconst dflt)
      | none => fconst dflt
    else fconst dflt
  | _ => fconst dflt

def lowerFixed (node : YTree) (invert : Bool) : Except String (List COp) :=
  match getScalar node "style" with
  | none => .error "PARSE"
  | some style =>
    match ffStyleId style with
    | none => .error "UNSUPPORTED"
    | some id =>
      let st := if invert then ffInvert id else id
      let params := node.mapGet "params"
      let p (i : Nat) (d : Float32) : FB := paramAt params i d
      if st == 6 || st == 7 then
        .ok [.fixed st 1 ([p 0 0.78] ++ zeros 7)]
      else if st == 8 || st == 9 then
        .ok [.fixed st 2 ([fconst 0.075, fconst 0.1] ++ zeros 6)]
      else if st == 0 || st == 1 then
        .ok [.fixed st 2 ([fconst 0.05, fconst 0.08] ++ zeros 6)]
      else if st == 2 || st == 3 then
        .ok [.fixed st 1 ((if st == 3 then fconst 1.0192640913260627
                           else fconst 0.9811) :: zeros 7)]
      else if st == 4 || st == 5 then
        .ok [.fixed st 7 ([p 0 0, p 1 0, p 2 0, p 3 0, p 4 0, p 5 0, p 6 1, 0])]
      else
        .ok [.fixed st 0 (zeros 8)]

/-- `toc_lower_transform`. -/
def pLowerTransform (node : YTree) (invert : Bool) : Except String (List COp) :=
  match tagOf node with
  | none => .ok []
  | some tag =>
    if tag = "MatrixTransform" then lowerMatrix node invert
    else if tag = "ExponentTransform" then lowerExponent node invert
    else if tag = "ExponentWithLinearTransform" then lowerExpLinear node invert
    else if tag = "LogTransform" || tag == "LogAffineTransform" then lowerLog node invert
    else if tag = "LogCameraTransform" then lowerLogCamera node invert
    else if tag = "CDLTransform" then lowerCdl node invert
    else if tag = "RangeTransform" then lowerRange node invert
    else .error "UNSUPPORTED"

/-! ## Pipeline construction -/

def walkMaxDepth : Nat := 64

def procFuel : Nat := 100000

mutual
/-- `walk` with its depth cap and one fuel unit. -/
def pWalk (root : YTree) (depth fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List COp) :=
  match fuel with
  | 0 => .error "PARSE"
  | f + 1 =>
    if depth ≥ walkMaxDepth then .error "PARSE"
    else pWalkNode root (depth + 1) f node invert

/-- `walk_node`. -/
def pWalkNode (root : YTree) (depth fuel : Nat) (node : YTree) (invert : Bool) :
    Except String (List COp) :=
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
      else if tag = "FixedFunctionTransform" then lowerFixed node dirInv
      else pLowerTransform node dirInv

/-- Walk a child list forward. -/
def pWalkAll (root : YTree) (depth fuel : Nat) (xs : List YTree) (invert : Bool) :
    Except String (List COp) :=
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
    (invert : Bool) : Except String (List COp) :=
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
    (invert : Bool) : Except String (List COp) :=
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
    (invert : Bool) : Except String (List COp) :=
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

/-- Apply a view's looks in order (capped at 8 by the caller). -/
def pApplyLooks (root : YTree) (fuel : Nat) (looks : List String) :
    Except String (List COp) :=
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
    Except String (List COp) :=
  if isDataCs root src || isDataCs root dst then .ok []
  else
    (pEmitToRef root 0 procFuel src false).bind (fun a =>
      let bridge : Except String (List COp) :=
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
    Except String (List COp) :=
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
            let vtOps : Except String (List COp) :=
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

/-! ## Rendering -/

/-- Kind names (`err:` payloads use the same spelling as the C). -/
def copKindName : COp → String
  | .matrix .. => "MATRIX"
  | .range .. => "RANGE"
  | .exponent .. => "EXPONENT"
  | .expLinear .. => "EXP_LINEAR"
  | .log .. => "LOG"
  | .logCamera .. => "LOG_CAMERA"
  | .cdl .. => "CDL"
  | .lut1d .. => "LUT1D"
  | .lut3d .. => "LUT3D"
  | .fixed s .. => "FIXEDFUNC(" ++ toString s ++ ")"

/-- `ok:K1,K2,...` or `err:CODE`. -/
def renderProcResult (r : Except String (List COp)) : String :=
  match r with
  | .error e => "err:" ++ e
  | .ok ops => "ok:" ++ String.intercalate "," (ops.map copKindName)

/-- 8 lowercase hex digits of a float bit pattern. -/
def bitsHex (b : UInt32) : String :=
  String.ofList ((List.range 8).map (fun i =>
    hexDigChar ((b >>> UInt32.ofNat (28 - 4 * i)).toNat % 16)))

def fmtBits (l : List FB) : String := String.join (l.map (fun b => " " ++ bitsHex b))

def flag (b : Bool) : String := if b then "1" else "0"

/-- The parameter recipe for one op (the C generator's `emit_recipe` format). -/
def copRecipe : COp → String
  | .matrix m off => "matrix" ++ fmtBits (m ++ off)
  | .range scale offset lo hi cl hi' =>
    "range" ++ fmtBits (scale ++ offset ++ lo ++ hi) ++ " " ++ flag cl ++ " " ++ flag hi'
  | .exponent e mir => "exponent" ++ fmtBits e ++ " " ++ flag mir
  | .expLinear sc of gm bk sl inv mir =>
    "explinear" ++ fmtBits (sc ++ of ++ gm ++ bk ++ sl) ++ " " ++ bitStr inv ++ " " ++ flag mir
  | .log ls lo ns no base inv =>
    "log" ++ fmtBits (ls ++ lo ++ ns ++ no ++ [base]) ++ " " ++ flag inv
  | .logCamera ls lo ns no brk sl so base inv =>
    "logcam" ++ fmtBits (ls ++ lo ++ ns ++ no ++ brk ++ sl ++ so ++ [base]) ++ " " ++ bitStr inv
  | .cdl sl of pw sat luma cl inv =>
    "cdl" ++ fmtBits (sl ++ of ++ pw ++ [sat] ++ luma) ++ " " ++ flag cl ++ " " ++ flag inv
  | .lut1d len ch dmin dmax data =>
    "lut1d " ++ toString len ++ " " ++ toString ch ++ fmtBits ([dmin, dmax] ++ data)
  | .lut3d size dmin dmax tet data =>
    "lut3d " ++ toString size ++ " " ++ flag tet ++ fmtBits (dmin ++ dmax ++ data)
  | .fixed style nparams params =>
    "fixed " ++ toString style ++ " " ++ toString nparams ++ fmtBits params

end Tocio
