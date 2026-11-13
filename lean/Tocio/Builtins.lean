/-
  TinyEXR - Lean 4 formalization of the tocio builtin transform expansion
  (`toc_builtins.c`: `toc_builtin_expand`).

  `BuiltinTransform {style: ...}` expands a style name into a flat op list:
  the ACES AP0/AP1 matrices, the ACEScc/ACEScct log curves, the derived
  colorimetry (linear-RGB <-> CIE-XYZ matrices from primaries + white point
  with Bradford/von-Kries adaptation), the composed display output
  transforms (primaries matrix + MonCurve / pure gamma / PQ / HLG encode),
  the camera-log builtins (LogCamera decode + camera gamut -> AP0) and the
  ACES 2.0 output transforms. Inversion reverses the list and inverts each
  op (`toc_invert_op`), exactly like the C.

  The ACES 2.0 op's *init scalars* are modelled here (`aces2Scalars`):
  the tonescale, chroma-compression coefficients, both CAM16 JMh matrices
  and the derived compression bounds. The hue-indexed tables the kernel
  indexes at runtime (`reach_m`, `hue_table`, `cusp_*`, built by the
  corner/hull search in `toc_aces2.c`) are outside the model — the op is
  pinned by every scalar `toc_aces2_init` derives, not by those tables.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.ProcessorParams
import Tocio.Math

namespace Tocio

set_option linter.unusedVariables false

/-! ## 3x3 float helpers (row-major, `M * v` like the C's `mat3_*`) -/

def m3get (m : List FB) (i : Nat) : FB := fuget m i

/-- `mat3_mul`: `o[r*3+c] = ((0 + a[r,0]b[0,c]) + a[r,1]b[1,c]) + a[r,2]b[2,c]`. -/
def m3mul (a b : List FB) : List FB :=
  (List.range 9).map (fun i =>
    let r := i / 3
    let c := i % 3
    fadd (fadd (fadd 0 (fmul (m3get a (r * 3)) (m3get b c)))
                (fmul (m3get a (r * 3 + 1)) (m3get b (3 + c))))
         (fmul (m3get a (r * 3 + 2)) (m3get b (6 + c))))

/-- `mat3_vec`: `o[r] = (a[r,0]v0 + a[r,1]v1) + a[r,2]v2`. -/
def m3vec (m v : List FB) : List FB :=
  (List.range 3).map (fun r =>
    fadd (fadd (fmul (m3get m (r * 3)) (fuget v 0))
               (fmul (m3get m (r * 3 + 1)) (fuget v 1)))
         (fmul (m3get m (r * 3 + 2)) (fuget v 2)))

/-- `mat3_inv` (cofactor / determinant, the C's evaluation order). -/
def m3inv (m : List FB) : Option (List FB) :=
  let c00 := fsub (fmul (m3get m 4) (m3get m 8)) (fmul (m3get m 5) (m3get m 7))
  let c01 := fsub (fmul (m3get m 5) (m3get m 6)) (fmul (m3get m 3) (m3get m 8))
  let c02 := fsub (fmul (m3get m 3) (m3get m 7)) (fmul (m3get m 4) (m3get m 6))
  let det0 := fadd (fadd (fmul (m3get m 0) c00) (fmul (m3get m 1) c01))
                   (fmul (m3get m 2) c02)
  if fzero det0 then none
  else
    let d := fdiv (fconst 1) det0
    some [fmul c00 d,
          fmul (fsub (fmul (m3get m 2) (m3get m 7)) (fmul (m3get m 1) (m3get m 8))) d,
          fmul (fsub (fmul (m3get m 1) (m3get m 5)) (fmul (m3get m 2) (m3get m 4))) d,
          fmul c01 d,
          fmul (fsub (fmul (m3get m 0) (m3get m 8)) (fmul (m3get m 2) (m3get m 6))) d,
          fmul (fsub (fmul (m3get m 2) (m3get m 3)) (fmul (m3get m 0) (m3get m 5))) d,
          fmul c02 d,
          fmul (fsub (fmul (m3get m 1) (m3get m 6)) (fmul (m3get m 0) (m3get m 7))) d,
          fmul (fsub (fmul (m3get m 0) (m3get m 4)) (fmul (m3get m 1) (m3get m 3))) d]

/-- `xy -> XYZ` at unit luminance. -/
def xyToXyz (x y : FB) : List FB :=
  [fdiv x y, fconst 1, fdiv (fsub (fsub (fconst 1) x) y) y]

/-! ## Linear color spaces (the C's `TOC_CSPACES` table) -/

structure CSpace where
  rx : FB
  ry : FB
  gx : FB
  gy : FB
  bx : FB
  byy : FB
  wx : FB
  wy : FB
  isXyz : Bool

def wpD65x : FB := fconst 0.3127
def wpD65y : FB := fconst 0.3290
def wpD60x : FB := fconst 0.32168
def wpD60y : FB := fconst 0.33767
def wpDCIx : FB := fconst 0.314
def wpDCIy : FB := fconst 0.351

def cspaces : List (String × CSpace) :=
  [ ("Linear-sRGB", ⟨fconst 0.640, fconst 0.330, fconst 0.300, fconst 0.600,
      fconst 0.150, fconst 0.060, wpD65x, wpD65y, false⟩),
    ("Linear-Rec709", ⟨fconst 0.640, fconst 0.330, fconst 0.300, fconst 0.600,
      fconst 0.150, fconst 0.060, wpD65x, wpD65y, false⟩),
    ("Linear-P3-D65", ⟨fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
      fconst 0.150, fconst 0.060, wpD65x, wpD65y, false⟩),
    ("Linear-Display-P3", ⟨fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
      fconst 0.150, fconst 0.060, wpD65x, wpD65y, false⟩),
    ("Linear-P3-DCI", ⟨fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
      fconst 0.150, fconst 0.060, wpDCIx, wpDCIy, false⟩),
    ("Linear-DCI-P3", ⟨fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
      fconst 0.150, fconst 0.060, wpDCIx, wpDCIy, false⟩),
    ("Linear-Rec2020", ⟨fconst 0.708, fconst 0.292, fconst 0.170, fconst 0.797,
      fconst 0.131, fconst 0.046, wpD65x, wpD65y, false⟩),
    ("Linear-Rec2100", ⟨fconst 0.708, fconst 0.292, fconst 0.170, fconst 0.797,
      fconst 0.131, fconst 0.046, wpD65x, wpD65y, false⟩),
    ("Linear-AdobeRGB", ⟨fconst 0.640, fconst 0.330, fconst 0.210, fconst 0.710,
      fconst 0.150, fconst 0.060, wpD65x, wpD65y, false⟩),
    ("ACEScg", ⟨fconst 0.713, fconst 0.293, fconst 0.165, fconst 0.830,
      fconst 0.128, fconst 0.044, wpD60x, wpD60y, false⟩),
    ("Linear-AP1", ⟨fconst 0.713, fconst 0.293, fconst 0.165, fconst 0.830,
      fconst 0.128, fconst 0.044, wpD60x, wpD60y, false⟩),
    ("ACES2065-1", ⟨fconst 0.7347, fconst 0.2653, fconst 0.0, fconst 1.0,
      fconst 0.0001, fconst (-0.077), wpD60x, wpD60y, false⟩),
    ("Linear-AP0", ⟨fconst 0.7347, fconst 0.2653, fconst 0.0, fconst 1.0,
      fconst 0.0001, fconst (-0.077), wpD60x, wpD60y, false⟩),
    ("CIE-XYZ-D65", ⟨0, 0, 0, 0, 0, 0, wpD65x, wpD65y, true⟩)]

def cspaceLookup (name : String) : Option CSpace :=
  (cspaces.find? (fun p => p.1 == name)).map (·.2)

/-- `cspace_npm`: RGB -> XYZ normalized primary matrix. -/
def cspaceNpm (cs : CSpace) : Option (List FB) :=
  if cs.isXyz then
    some [fconst 1, 0, 0, 0, fconst 1, 0, 0, 0, fconst 1]
  else
    let pr := xyToXyz cs.rx cs.ry
    let pg := xyToXyz cs.gx cs.gy
    let pb := xyToXyz cs.bx cs.byy
    let C : List FB := [fuget pr 0, fuget pg 0, fuget pb 0,
                        fuget pr 1, fuget pg 1, fuget pb 1,
                        fuget pr 2, fuget pg 2, fuget pb 2]
    let W := xyToXyz cs.wx cs.wy
    match m3inv C with
    | none => none
    | some Cinv =>
      let S := m3vec Cinv W
      some [fmul (m3get C 0) (fuget S 0), fmul (m3get C 1) (fuget S 1),
            fmul (m3get C 2) (fuget S 2),
            fmul (m3get C 3) (fuget S 0), fmul (m3get C 4) (fuget S 1),
            fmul (m3get C 5) (fuget S 2),
            fmul (m3get C 6) (fuget S 0), fmul (m3get C 7) (fuget S 1),
            fmul (m3get C 8) (fuget S 2)]

/-- von Kries chromatic adaptation ws(xy) -> wd(xy) with cone matrix `C`. -/
def vkCat (C : List FB) (wsx wsy wdx wdy : FB) : List FB :=
  let Cinv := (m3inv C).getD (List.replicate 9 0)
  let Ws := xyToXyz wsx wsy
  let Wd := xyToXyz wdx wdy
  let cs := m3vec C Ws
  let cd := m3vec C Wd
  let D : List FB := [fdiv (fuget cd 0) (fuget cs 0), 0, 0,
                      0, fdiv (fuget cd 1) (fuget cs 1), 0,
                      0, 0, fdiv (fuget cd 2) (fuget cs 2)]
  m3mul Cinv (m3mul D C)

def bradfordM : List FB :=
  [fconst 0.8951, fconst 0.2664, fconst (-0.1614),
   fconst (-0.7502), fconst 1.7135, fconst 0.0367,
   fconst 0.0389, fconst (-0.0685), fconst 1.0296]

def bradfordCat (wsx wsy wdx wdy : FB) : List FB :=
  vkCat bradfordM wsx wsy wdx wdy

/-- `cspace_convert`: linear src -> linear dst, Bradford-adapting the white. -/
def cspaceConvert (s d : CSpace) : Option (List FB) :=
  match cspaceNpm s, cspaceNpm d with
  | some Ms, some Md =>
    match m3inv Md with
    | none => none
    | some Mdinv =>
      if s.wx == d.wx && s.wy == d.wy then some (m3mul Mdinv Ms)
      else
        let cat := bradfordCat s.wx s.wy d.wx d.wy
        some (m3mul Mdinv (m3mul cat Ms))
  | _, _ => none

/-! ## Op constructors (the C's `push_*` helpers) -/

/-- `push_mat3`: a 3x3 row-major matrix as a 4x4 column-major op. -/
def pushMat3 (m : List FB) : COp :=
  .matrix ((List.range 16).map (fun i =>
    let c := i / 4
    let r := i % 4
    if r < 3 && c < 3 then m3get m (r * 3 + c)
    else if r == c then fconst 1 else 0)) (List.replicate 4 0)

/-- `push_acescct_log`: ACEScct's log segment as a LogCamera op. -/
def pushAcescctLog (logToLin : Bool) : COp :=
  let ls := fdiv (fconst 1) (fconst 17.52)
  let lo := fdiv (fconst 9.72) (fconst 17.52)
  .logCamera (List.replicate 3 ls) (List.replicate 3 lo)
    (List.replicate 3 (fconst 1)) (List.replicate 3 0)
    (List.replicate 3 (fconst 0.0078125))
    (List.replicate 3 (fconst 10.5402377416545))
    (List.replicate 3 (fconst 0.0729055341958355))
    (fconst 2) logToLin

/-- `push_acescc_log`: ACEScc's pure affine log2 (no linear toe). -/
def pushAcesccLog (logToLin : Bool) : COp :=
  let ls := fdiv (fconst 1) (fconst 17.52)
  let lo := fdiv (fconst 9.72) (fconst 17.52)
  .log (List.replicate 3 ls) (List.replicate 3 lo)
    (List.replicate 3 (fconst 1)) (List.replicate 3 0) (fconst 2) logToLin

/-- `push_range_clamp`. -/
def pushRangeClamp (lo hi : FB) : COp :=
  .range (List.replicate 4 (fconst 1)) (List.replicate 4 0)
    (List.replicate 4 lo) (List.replicate 4 hi) true true

/-- `push_scale3`: an unclamped RGB scale. -/
def pushScale3 (s : FB) : COp :=
  .range ([s, s, s, fconst 1]) (List.replicate 4 0)
    (List.replicate 4 0) (List.replicate 4 (fconst 1)) false false

/-- `push_moncurve`: the OCIO MonCurve EOTF from (gamma, offset). -/
def pushMoncurve (gamma offset : FB) (encode mirror : Bool) : COp :=
  let mc := moncurve gamma offset
  .expLinear (List.replicate 4 (fuget mc 0)) (List.replicate 4 (fuget mc 1))
    (List.replicate 4 (fuget mc 2)) (List.replicate 4 (fuget mc 3))
    (List.replicate 4 (fuget mc 4)) encode mirror

/-- `push_gamma`: a pure-power EOTF. -/
def pushGamma (g : FB) (encode mirror : Bool) : COp :=
  let e := if encode then fdiv (fconst 1) g else g
  .exponent [e, e, e, fconst 1] mirror

/-- `push_ff_style`: a fixed-function op with no params. -/
def pushFfStyle (style : Nat) : COp := .fixed style 0 (List.replicate 8 0)

/-- `push_cspace_named`. -/
def pushCspaceNamed (src dst : String) : Except String (List COp) :=
  match cspaceLookup src, cspaceLookup dst with
  | some s, some d =>
    match cspaceConvert s d with
    | some M => .ok [pushMat3 M]
    | none => .error "UNSUPPORTED"
  | _, _ => .error "UNSUPPORTED"

/-- `find_to`: the index of the first `_to_` (no libc `strstr`). -/
def findToIdx (cs : List Char) : Option Nat :=
  let rec go (i : Nat) (rest : List Char) : Option Nat :=
    match rest with
    | '_' :: 't' :: 'o' :: '_' :: _ => some i
    | _ :: tl => go (i + 1) tl
    | [] => none
  go 0 cs

/-- `push_cspace_convert`: a generic `<A>_to_<B>` linear color-space
conversion. `none` when the style is not of that shape or names an
unknown space. -/
def pushCspaceConvert (style : String) : Option (Except String (List COp)) :=
  match findToIdx style.toList with
  | none => none
  | some i =>
    if i >= 48 then none
    else
      let src := String.ofList (style.toList.take i)
      let dst := String.ofList (style.toList.drop (i + 4))
      match cspaceLookup src, cspaceLookup dst with
      | some _, some _ => some (pushCspaceNamed src dst)
      | _, _ => none

/-! ## Display output transforms (`push_display_xform`) -/

structure DispX where
  name : String
  prim : String
  /-- 0 = MonCurve(gamma, offset), 1 = pure gamma, 2 = PQ, 3 = HLG,
  4 = DCDM (scale 48/52.37 + gamma over XYZ), 5 = PQ over XYZ. -/
  kind : Nat
  g : FB
  off : FB
  /-- OCIO encodes this display with MONCURVE_MIRROR even without the
  `- MIRROR NEGS` suffix. -/
  amir : Bool

def dispXforms : List DispX :=
  [ ⟨"CIE-XYZ-D65_to_sRGB", "Linear-sRGB", 0, fconst 2.4, fconst 0.055, false⟩,
    ⟨"CIE-XYZ-D65_to_DisplayP3", "Linear-Display-P3", 0, fconst 2.4, fconst 0.055, true⟩,
    ⟨"CIE-XYZ-D65_to_Display-P3", "Linear-Display-P3", 0, fconst 2.4, fconst 0.055, true⟩,
    ⟨"CIE-XYZ-D65_to_DisplayP3-HDR", "Linear-Display-P3", 0, fconst 2.4, fconst 0.055, true⟩,
    ⟨"CIE-XYZ-D65_to_G2.2-REC.709", "Linear-Rec709", 1, fconst 2.2, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_G2.6-P3-D65", "Linear-P3-D65", 1, fconst 2.6, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_DCI-P3", "Linear-DCI-P3", 1, fconst 2.6, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_REC.1886-REC.709", "Linear-Rec709", 1, fconst 2.4, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_Rec.1886-Rec.709", "Linear-Rec709", 1, fconst 2.4, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_REC.1886-REC.2020", "Linear-Rec2020", 1, fconst 2.4, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_REC.2100-PQ", "Linear-Rec2020", 2, 0, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_Rec.2100-PQ", "Linear-Rec2020", 2, 0, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_ST2084-P3-D65", "Linear-P3-D65", 2, 0, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_Rec.2100-HLG", "Linear-Rec2020", 3, 0, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_DCDM-D65", "CIE-XYZ-D65", 4, fconst 2.6, 0, false⟩,
    ⟨"CIE-XYZ-D65_to_ST2084-DCDM-D65", "CIE-XYZ-D65", 5, 0, 0, false⟩]

/-- `push_display_xform`: a composed CIE-XYZ-D65 -> display output transform
(primaries matrix then the display transfer function encode). -/
def pushDisplayXform (style : String) : Option (Except String (List COp)) :=
  let inner0 : String :=
    if style.length >= 10 && style.toList.take 10 == "DISPLAY - ".toList then
      String.ofList (style.toList.drop 10)
    else style
  let (mir, inner) : Bool × String :=
    if inner0.length < 128 && endsWithS inner0 " - MIRROR NEGS" then
      (true, String.ofList (inner0.toList.take (inner0.length - 14)))
    else (false, inner0)
  match dispXforms.find? (fun d => d.name == inner) with
  | none => none
  | some d =>
    let m := mir || d.amir
    (pushCspaceNamed "CIE-XYZ-D65" d.prim).bind (fun base =>
      let tail : Except String (List COp) :=
        if d.kind == 0 then .ok [pushMoncurve d.g d.off true m]
        else if d.kind == 1 then .ok [pushGamma d.g true m]
        else if d.kind == 2 then .ok [pushFfStyle 22]
        else if d.kind == 3 then .ok [pushFfStyle 24]
        else if d.kind == 4 then
          .ok [pushScale3 (fdiv (fconst 48) (fconst 52.37)), pushGamma d.g true false]
        else if d.kind == 5 then .ok [pushFfStyle 22]
        else .ok []
      tail.map (fun t => base ++ t))

/-! ## Camera-log builtins (`push_camera`) -/

structure CamEnt where
  name : String
  prim : List FB
  /-- An explicit camera -> AP0 matrix, or `none` to derive it from `prim`. -/
  mat : Option (List FB)
  /-- When deriving: `true` = CAT02, `false` = Bradford. -/
  cat02 : Bool
  base : FB
  ls : FB
  lo : FB
  ns : FB
  no : FB
  brk : FB
  hasLslope : Bool
  lslope : FB

def cat02M : List FB :=
  [fconst 0.7328, fconst 0.4296, fconst (-0.1624),
   fconst (-0.7036), fconst 1.6975, fconst 0.0061,
   fconst 0.0030, fconst 0.0136, fconst 0.9834]

def svenM : List FB :=
  [fconst 0.7933297411, fconst 0.0890786256, fconst 0.1175916333,
   fconst 0.0155810585, fconst 1.0327123069, fconst (-0.0482933654),
   fconst (-0.0188647478), fconst 0.0127694121, fconst 1.0060953358]

def svencM : List FB :=
  [fconst 0.6742570921, fconst 0.2205717359, fconst 0.1051711720,
   fconst (-0.0093136061), fconst 1.1059588614, fconst (-0.0966452553),
   fconst (-0.0382090673), fconst (-0.0179383766), fconst 1.0561474439]

/-- The Sony Venice log curve (shared by both Venice builtins). -/
def veniceBase : FB := fconst 10
def veniceLs : FB := fdiv (fconst 261.5) (fconst 1023)
def veniceLo : FB := fdiv (fconst 420) (fconst 1023)
def veniceNs : FB := fdiv (fconst 1) (fconst 0.19)
def veniceNo : FB := fdiv (fconst 0.01) (fconst 0.19)
def veniceBrk : FB := fconst 0.01125
def veniceLslope : FB := fconst 6.62292117

def cameras : List CamEnt :=
  [ ⟨"ARRI_ALEXA-LOGC-EI800-AWG_to_ACES2065-1",
      [fconst 0.684, fconst 0.313, fconst 0.221, fconst 0.848, fconst 0.0861,
       fconst (-0.102), wpD65x, wpD65y],
      none, true, fconst 10, fconst 0.2471896383, fconst 0.3855369987,
      fdiv (fconst 1) (fconst 0.18), fconst 0.0522722750, fconst 0.0105909905,
      false, 0⟩,
    ⟨"ARRI_LOGC4_to_ACES2065-1",
      [fconst 0.7347, fconst 0.2653, fconst 0.1424, fconst 0.8576, fconst 0.0991,
       fconst (-0.0308), wpD65x, wpD65y],
      none, true, fconst 2, fconst 0.0647954196341293,
      fconst (-0.295908392682586), fconst 2231.82630906769, fconst 64,
      fconst (-0.0180569961199113), false, 0⟩,
    ⟨"SONY_SLOG3-SGAMUT3_to_ACES2065-1",
      [fconst 0.730, fconst 0.280, fconst 0.140, fconst 0.855, fconst 0.100,
       fconst (-0.050), wpD65x, wpD65y],
      none, true, veniceBase, veniceLs, veniceLo, veniceNs, veniceNo, veniceBrk,
      true, veniceLslope⟩,
    ⟨"SONY_SLOG3-SGAMUT3.CINE_to_ACES2065-1",
      [fconst 0.766, fconst 0.275, fconst 0.225, fconst 0.800, fconst 0.089,
       fconst (-0.087), wpD65x, wpD65y],
      none, true, veniceBase, veniceLs, veniceLo, veniceNs, veniceNo, veniceBrk,
      true, veniceLslope⟩,
    ⟨"SONY_SLOG3-SGAMUT3-VENICE_to_ACES2065-1",
      List.replicate 8 0, some svenM, false, veniceBase, veniceLs, veniceLo,
      veniceNs, veniceNo, veniceBrk, true, veniceLslope⟩,
    ⟨"SONY_SLOG3-SGAMUT3.CINE-VENICE_to_ACES2065-1",
      List.replicate 8 0, some svencM, false, veniceBase, veniceLs, veniceLo,
      veniceNs, veniceNo, veniceBrk, true, veniceLslope⟩,
    ⟨"RED_LOG3G10-RWG_to_ACES2065-1",
      [fconst 0.780308, fconst 0.304253, fconst 0.121595, fconst 1.493994,
       fconst 0.095612, fconst (-0.084589), wpD65x, wpD65y],
      none, false, fconst 10, fconst 0.224282, 0, fconst 155.975327,
      fadd (fmul (fconst 0.01) (fconst 155.975327)) (fconst 1),
      fconst (-0.01), false, 0⟩,
    ⟨"PANASONIC_VLOG-VGAMUT_to_ACES2065-1",
      [fconst 0.730, fconst 0.280, fconst 0.165, fconst 0.840, fconst 0.100,
       fconst (-0.030), wpD65x, wpD65y],
      none, false, fconst 10, fconst 0.241514, fconst 0.598206, fconst 1,
      fconst 0.00873, fconst 0.01, false, 0⟩]

/-- `push_camera_logcam`: a camera LogCamera curve as log->lin (decode),
with the linear segment solved for C0 continuity. -/
def pushCameraLogcam (base ls lo ns no brk : FB) (hasLslope : Bool)
    (lslope : FB) : COp :=
  let lnb := fmul (fbits (log2f (f32of base))) (fconst 0.6931471805599453)
  let xb := fadd (fmul ns brk) no
  let xbsafe := if f32of xb > 0.0 then xb else fconst 1e-30
  let yb := fadd (fmul ls (fdiv (fbits (log2f (f32of xbsafe)))
                                  (fbits (log2f (f32of base))))) lo
  let lsl := if hasLslope then lslope
             else fdiv (fmul ls ns)
                    (fmul (if f32of xb != 0.0 then xb else fconst 1e-30) lnb)
  .logCamera (List.replicate 3 ls) (List.replicate 3 lo) (List.replicate 3 ns)
    (List.replicate 3 no) (List.replicate 3 brk) (List.replicate 3 lsl)
    (List.replicate 3 (fsub yb (fmul lsl brk))) base true

/-- `cam_to_ap0`: camera-gamut RGB -> ACES AP0, adapting the camera white to
AP0's D60 with CAT02 or Bradford. -/
def camToAp0 (cam : List FB) (cat02 : Bool) : Option (List FB) :=
  match cspaceLookup "Linear-AP0" with
  | none => none
  | some ap0 =>
    let c : CSpace :=
      ⟨fuget cam 0, fuget cam 1, fuget cam 2, fuget cam 3,
       fuget cam 4, fuget cam 5, fuget cam 6, fuget cam 7, false⟩
    match cspaceNpm c, cspaceNpm ap0 with
    | some Mc, some Map0 =>
      match m3inv Map0 with
      | none => none
      | some Mai =>
        let cat := vkCat (if cat02 then cat02M else bradfordM)
          c.wx c.wy ap0.wx ap0.wy
        some (m3mul Mai (m3mul cat Mc))
    | _, _ => none

/-- `push_camera`: a camera `<X>_to_ACES2065-1` builtin. -/
def pushCamera (style : String) : Option (Except String (List COp)) :=
  match cameras.find? (fun c => c.name == style) with
  | none => none
  | some c =>
    let lc := pushCameraLogcam c.base c.ls c.lo c.ns c.no c.brk c.hasLslope c.lslope
    match c.mat with
    | some m => some (.ok [lc, pushMat3 m])
    | none =>
      match camToAp0 c.prim c.cat02 with
      | some m => some (.ok [lc, pushMat3 m])
      | none => some (.error "UNSUPPORTED")

/-! ## ACES AP0 / AP1 matrices -/

def ap1ToAp0 : List FB :=
  [fconst 0.6954522414, fconst 0.1406786965, fconst 0.1638690622,
   fconst 0.0447945634, fconst 0.8596711185, fconst 0.0955343182,
   fconst (-0.0055258826), fconst 0.0040252103, fconst 1.0015006723]

def ap0ToAp1 : List FB :=
  [fconst 1.4514393161, fconst (-0.2365107469), fconst (-0.2149285693),
   fconst (-0.0765537734), fconst 1.1762296998, fconst (-0.0996759264),
   fconst 0.0083161484, fconst (-0.0060324498), fconst 0.9977163014]

/-! ## ACES 2.0 output transform (`toc_aces2.c` init scalars) -/

def AP0_PRIM : List FB :=
  [fconst 0.7347, fconst 0.2653, fconst 0.0, fconst 1.0,
   fconst 0.0001, fconst (-0.077), fconst 0.32168, fconst 0.33767]

def CAM16_PRIM : List FB :=
  [fconst 0.8336, fconst 0.1735, fconst 2.3854, fconst (-1.4659),
   fconst 0.087, fconst (-0.125), fconst 0.333, fconst 0.333]

def a2Surround : List FB := [fconst 0.9, fconst 0.59, fconst 0.9]

/-- `npm_from_prims`: RGB -> XYZ with the space's own white (row-major). -/
def npmFromPrims (p : List FB) : Option (List FB) :=
  let C : List FB := (List.range 9).map (fun i =>
    let row := i / 3
    let col := i % 3
    let x := fuget p (col * 2)
    let y := fuget p (col * 2 + 1)
    if row == 0 then fdiv x y
    else if row == 1 then fconst 1
    else fdiv (fsub (fsub (fconst 1) x) y) y)
  let W : List FB :=
    [fdiv (fuget p 6) (fuget p 7), fconst 1,
     fdiv (fsub (fsub (fconst 1) (fuget p 6)) (fuget p 7)) (fuget p 7)]
  match m3inv C with
  | none => none
  | some Cinv =>
    let S := m3vec Cinv W
    some ((List.range 9).map (fun i => fmul (m3get C i) (fuget S (i % 3))))

def a2abs (x : FB) : FB := if f32of x < 0.0 then fneg x else x
def a2min (a b : FB) : FB := if f32of a < f32of b then a else b
def a2max (a b : FB) : FB := if f32of a > f32of b then a else b
def a2copysign (x y : FB) : FB := if f32of y < 0.0 then fneg (a2abs x) else a2abs x
def a2ln (x : FB) : FB := fmul (fbits (log2f (f32of x))) (fconst 0.69314718055994531)
def a2log10 (x : FB) : FB := fmul (fbits (log2f (f32of x))) (fconst 0.30102999566398120)

/-- `cone_fwd_abs` (post-adaptation cone response). -/
def coneFwdAbs (rc : FB) : FB :=
  let f := fbits (powf (f32of rc) (f32of (fconst 0.42)))
  fdiv f (fadd (fconst 27.13) f)

def coneFwd (v : FB) : FB := a2copysign (coneFwdAbs (a2abs v)) v

/-- `model_gamma()`. -/
def modelGamma : FB :=
  fmul (fuget a2Surround 1)
    (fadd (fconst 1.48) (fbits (sqrtf (f32of (fdiv (fconst 20) (fconst 100))))))

structure JMH where
  rgbToCam : List FB
  camToRgb : List FB
  coneToAab : List FB
  aabToCone : List FB
  fLn : FB
  cz : FB
  invCz : FB
  aWJ : FB
  invAWJ : FB

def emptyJMH : JMH :=
  { rgbToCam := List.replicate 9 0, camToRgb := List.replicate 9 0
    coneToAab := List.replicate 9 0, aabToCone := List.replicate 9 0
    fLn := 0, cz := 0, invCz := 0, aWJ := 0, invAWJ := 0 }

/-- `init_jmh`: the CAM16 JMh parameters for one RGB primaries set. -/
def initJmh (prims : List FB) : Option JMH :=
  let baseCone : List FB :=
    [fconst 2, fconst 1, fdiv (fconst 1) (fconst 20),
     fconst 1, fdiv (fconst (-12)) (fconst 11), fdiv (fconst 1) (fconst 11),
     fdiv (fconst 1) (fconst 9), fdiv (fconst 1) (fconst 9),
     fdiv (fconst (-2)) (fconst 9)]
  match npmFromPrims CAM16_PRIM, npmFromPrims prims with
  | some npmCam, some npmPrim =>
    match m3inv npmCam with
    | none => none
    | some m16 =>
      let refLum := fconst 100
      let xyzW := m3vec npmPrim [refLum, refLum, refLum]
      let yW := fuget xyzW 1
      let rgbW := m3vec m16 xyzW
      let k := fdiv (fconst 1) (fadd (fmul (fconst 5) (fconst 100)) (fconst 1))
      let k4 := fmul (fmul (fmul k k) k) k
      let fL := fadd (fmul (fmul (fconst 0.2) k4) (fmul (fconst 5) (fconst 100)))
        (fmul (fmul (fmul (fconst 0.1) (fsub (fconst 1) k4)) (fsub (fconst 1) k4))
          (fbits (powf (f32of (fmul (fconst 5) (fconst 100)))
                       (f32of (fdiv (fconst 1) (fconst 3))))))
      let fLn := fdiv fL refLum
      let cz := modelGamma
      let invCz := fdiv (fconst 1) cz
      let dRgb := (List.range 3).map (fun i => fdiv (fmul fLn yW) (fuget rgbW i))
      let rgbWc := (List.range 3).map (fun i => fmul (fuget dRgb i) (fuget rgbW i))
      let rgbAw := rgbWc.map coneFwd
      let crta := baseCone.map (fun v => fmul v (fconst 400))
      let aW := fadd (fadd (fmul (fuget crta 0) (fuget rgbAw 0))
                            (fmul (fuget crta 1) (fuget rgbAw 1)))
                     (fmul (fuget crta 2) (fuget rgbAw 2))
      let aWJ := coneFwdAbs fL
      let invAWJ := fdiv (fconst 1) aWJ
      let r2c := (m3mul m16 npmPrim).map (fun v => fmul v refLum)
      let r2cc := (List.range 9).map (fun i => fmul (fuget r2c i) (fuget dRgb (i / 3)))
      let c2r := (m3inv r2cc).getD (List.replicate 9 0)
      let cta := (List.range 9).map (fun i =>
        if i < 3 then fdiv (fuget crta i) aW
        else fmul (fmul (fuget crta i) (fconst 43)) (fuget a2Surround 2))
      let atc := (m3inv cta).getD (List.replicate 9 0)
      some { rgbToCam := r2cc, camToRgb := c2r, coneToAab := cta, aabToCone := atc
             fLn := fLn, cz := cz, invCz := invCz, aWJ := aWJ, invAWJ := invAWJ }
  | _, _ => none

structure ToneScale where
  n : FB
  nR : FB
  g : FB
  t1 : FB
  cT : FB
  s2 : FB
  u2 : FB
  m2 : FB
  fwdLimit : FB
  invLimit : FB
  logPeak : FB

/-- `init_tonescale`. -/
def initTonescale (peak : FB) : ToneScale :=
  let n := peak
  let nR := fconst 100
  let g := fconst 1.15
  let c := fconst 0.18
  let cD := fconst 10.013
  let wG := fconst 0.14
  let t1 := fconst 0.04
  let rHitMin := fconst 128
  let rHitMax := fconst 896
  let rHit := fadd rHitMin (fmul (fsub rHitMax rHitMin)
    (fdiv (a2ln (fdiv n nR)) (a2ln (fconst 100))))
  let m0 := fdiv n nR
  let m1 := fmul (fconst 0.5)
    (fadd m0 (fbits (sqrtf (f32of (fmul m0 (fadd m0 (fmul (fconst 4) t1)))))))
  let u := fbits (powf (f32of (fdiv (fdiv rHit m1) (fadd (fdiv rHit m1) (fconst 1))))
                        (f32of g))
  let m := fdiv m1 u
  let wI := fdiv (a2ln (fdiv n (fconst 100))) (a2ln (fconst 2))
  let cT := fmul (fdiv cD nR) (fadd (fconst 1) (fmul wI wG))
  let gIp := fmul (fconst 0.5)
    (fadd cT (fbits (sqrtf (f32of (fmul cT (fadd cT (fmul (fconst 4) t1)))))))
  let p := fbits (powf (f32of (fdiv gIp m)) (f32of (fdiv (fconst 1) g)))
  let gIpp2 := fdiv (fneg (fmul m1 p)) (fsub p (fconst 1))
  let w2 := fdiv c gIpp2
  let s2 := fmul (fmul w2 m1) (fconst 100)
  let u2 := fbits (powf (f32of (fdiv (fdiv rHit m1) (fadd (fdiv rHit m1) w2)))
                         (f32of g))
  let m2 := fdiv m1 u2
  { n := n, nR := nR, g := g, t1 := t1, cT := cT, s2 := s2, u2 := u2, m2 := m2
    fwdLimit := fmul (fconst 8) rHit
    invLimit := fdiv n (fmul u2 nR)
    logPeak := a2log10 (fdiv n nR) }

structure ChromaC where
  sat : FB
  satThr : FB
  compr : FB
  scale : FB

/-- `init_chroma`. -/
def initChroma (peak : FB) (t : ToneScale) : ChromaC :=
  { compr := fadd (fconst 2.4) (fmul (fmul (fconst 2.4) (fconst 3.3)) t.logPeak)
    sat := a2max (fconst 0.2)
      (fsub (fconst 1.3) (fmul (fmul (fconst 1.3) (fconst 0.69)) t.logPeak))
    satThr := fdiv (fconst 0.5) peak
    scale := fsub (fbits (powf (f32of (fmul (fconst 0.03379) peak))
                              (f32of (fconst 0.30596)))) (fconst 0.45135) }

/-- `achromatic_n_to_J`. -/
def achromaticNToJ (a cz : FB) : FB := fmul (fconst 100) (fbits (powf (f32of a) (f32of cz)))

/-- `Y_to_J_` (unsigned). -/
def yToJAbs (absY : FB) (p : JMH) : FB :=
  let ra := coneFwdAbs (fmul absY p.fLn)
  achromaticNToJ (fmul ra p.invAWJ) p.cz

/-- `Y_to_J` (sign-preserving). -/
def yToJ (y : FB) (p : JMH) : FB := a2copysign (yToJAbs (a2abs y) p) y

/-- The scalars `toc_aces2_init` derives from (peak luminance, limiting
primaries), in the order the differential gate records them. The
hue-indexed tables are not modelled (see the module header). -/
def aces2Scalars (peak : FB) (lim : List FB) : List FB :=
  let t := initTonescale peak
  let ch := initChroma peak t
  let out := (initJmh lim).getD emptyJMH
  let inp := (initJmh AP0_PRIM).getD emptyJMH
  [t.n, t.nR, t.g, t.t1, t.cT, t.s2, t.u2, t.m2, t.fwdLimit, t.invLimit, t.logPeak,
   ch.sat, ch.satThr, ch.compr, ch.scale,
   yToJ peak inp,
   fdiv (fconst 1) modelGamma,
   yToJ (fmul t.cT (fconst 100)) inp,
   fadd (fconst 1.35) (fmul (fmul (fconst 1.35) (fconst 1.75)) t.logPeak),
   fdiv (fconst 1) (fadd (fconst 1.14) (fmul (fconst 0.07) t.logPeak))]
  ++ out.rgbToCam ++ out.coneToAab

/-! ## ACES 2.0 output styles (`push_aces_output`) -/

def a2Rec709 : List FB :=
  [fconst 0.640, fconst 0.330, fconst 0.300, fconst 0.600,
   fconst 0.150, fconst 0.060, fconst 0.3127, fconst 0.3290]
def a2P3D65 : List FB :=
  [fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
   fconst 0.150, fconst 0.060, fconst 0.3127, fconst 0.3290]
def a2Rec2020 : List FB :=
  [fconst 0.708, fconst 0.292, fconst 0.170, fconst 0.797,
   fconst 0.131, fconst 0.046, fconst 0.3127, fconst 0.3290]
def a2Rec709D60 : List FB :=
  [fconst 0.640, fconst 0.330, fconst 0.300, fconst 0.600,
   fconst 0.150, fconst 0.060, fconst 0.32168, fconst 0.33767]
def a2P3D60 : List FB :=
  [fconst 0.680, fconst 0.320, fconst 0.265, fconst 0.690,
   fconst 0.150, fconst 0.060, fconst 0.32168, fconst 0.33767]
def a2Rec2020D60 : List FB :=
  [fconst 0.708, fconst 0.292, fconst 0.170, fconst 0.797,
   fconst 0.131, fconst 0.046, fconst 0.32168, fconst 0.33767]
def a2XyzE : List FB :=
  [fconst 1.0, fconst 0.0, fconst 0.0, fconst 1.0,
   fconst 0.0, fconst 0.0, fdiv (fconst 1) (fconst 3), fdiv (fconst 1) (fconst 3)]

structure AcesOut where
  name : String
  peak : FB
  /-- Limiting primaries (drive the tonescale/gamut fixed function and the
  final RGB->XYZ matrix). -/
  lim : List FB
  /-- Encoding primaries for the D60 white-point simulation scale. -/
  enc : Option (List FB)
  lscale : FB

def acesOutputs : List AcesOut :=
  [ ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709_2.0",
      fconst 100, a2Rec709, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D65_2.0",
      fconst 100, a2P3D65, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D65_2.0",
      fconst 500, a2P3D65, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D65_2.0",
      fconst 1000, a2P3D65, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-REC2020_2.0",
      fconst 1000, a2Rec2020, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-108nit-P3-D65_2.0",
      fconst 225, a2P3D65, none, fconst 0.48⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-300nit-P3-D65_2.0",
      fconst 625, a2P3D65, none, fconst 0.48⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D65_2.0",
      fconst 2000, a2P3D65, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D65_2.0",
      fconst 4000, a2P3D65, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-REC2020_2.0",
      fconst 500, a2Rec2020, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-REC2020_2.0",
      fconst 2000, a2Rec2020, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-REC2020_2.0",
      fconst 4000, a2Rec2020, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-REC709-D65_2.0",
      fconst 100, a2Rec709D60, some a2Rec709, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-P3-D65_2.0",
      fconst 100, a2Rec709D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-REC709-D60-in-REC2020-D65_2.0",
      fconst 100, a2Rec709D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D60-in-P3-D65_2.0",
      fconst 100, a2P3D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - SDR-100nit-P3-D60-in-XYZ-E_2.0",
      fconst 100, a2P3D60, none, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-108nit-P3-D60-in-P3-D65_2.0",
      fconst 225, a2P3D60, some a2P3D65, fconst 0.48⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-300nit-P3-D60-in-XYZ-E_2.0",
      fconst 625, a2P3D60, some a2XyzE, fconst 0.48⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D60-in-P3-D65_2.0",
      fconst 500, a2P3D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D60-in-P3-D65_2.0",
      fconst 1000, a2P3D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D60-in-P3-D65_2.0",
      fconst 2000, a2P3D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D60-in-P3-D65_2.0",
      fconst 4000, a2P3D60, some a2P3D65, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-P3-D60-in-REC2020-D65_2.0",
      fconst 500, a2P3D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-P3-D60-in-REC2020-D65_2.0",
      fconst 1000, a2P3D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-P3-D60-in-REC2020-D65_2.0",
      fconst 2000, a2P3D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-P3-D60-in-REC2020-D65_2.0",
      fconst 4000, a2P3D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-500nit-REC2020-D60-in-REC2020-D65_2.0",
      fconst 500, a2Rec2020D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-1000nit-REC2020-D60-in-REC2020-D65_2.0",
      fconst 1000, a2Rec2020D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-2000nit-REC2020-D60-in-REC2020-D65_2.0",
      fconst 2000, a2Rec2020D60, some a2Rec2020, fconst 1⟩,
    ⟨"ACES-OUTPUT - ACES2065-1_to_CIE-XYZ-D65 - HDR-4000nit-REC2020-D60-in-REC2020-D65_2.0",
      fconst 4000, a2Rec2020D60, some a2Rec2020, fconst 1⟩]

/-- `aces2_rgb2xyz`: RGB->XYZ for primaries `p`, white = the space's own
(no adaptation), solved from the primaries so it stays well-conditioned. -/
def aces2Rgb2xyz (p : List FB) : Option (List FB) :=
  let C : List FB := (List.range 9).map (fun i =>
    let row := i / 3
    let col := i % 3
    if row == 0 then fuget p (col * 2)
    else if row == 1 then fuget p (col * 2 + 1)
    else fsub (fsub (fconst 1) (fuget p (col * 2))) (fuget p (col * 2 + 1)))
  match m3inv C with
  | none => none
  | some Cinv =>
    let W : List FB :=
      [fdiv (fuget p 6) (fuget p 7), fconst 1,
       fdiv (fsub (fsub (fconst 1) (fuget p 6)) (fuget p 7)) (fuget p 7)]
    let g := (List.range 3).map (fun i =>
      fadd (fadd (fmul (m3get Cinv (i * 3)) (fuget W 0))
                 (fmul (m3get Cinv (i * 3 + 1)) (fuget W 1)))
           (fmul (m3get Cinv (i * 3 + 2)) (fuget W 2)))
    some ((List.range 9).map (fun i => fmul (fuget g (i % 3)) (m3get C i)))

/-- `push_scale_white`: scale the simulated D60 white into the encoding gamut. -/
def pushScaleWhite (lim enc : List FB) : Except String (List COp) :=
  match aces2Rgb2xyz lim, aces2Rgb2xyz enc with
  | some mLim, some mEnc =>
    match m3inv mEnc with
    | none => .error "UNSUPPORTED"
    | some mEncInv =>
      let wXyz := m3vec mLim [fconst 1, fconst 1, fconst 1]
      let wRgb := m3vec mEncInv wXyz
      let mx := a2max (a2max (fuget wRgb 0) (fuget wRgb 1)) (fuget wRgb 2)
      .ok [pushScale3 (fdiv (fconst 1) mx)]
  | _, _ => .error "UNSUPPORTED"

/-- `push_aces_output`: the ACES 2.0 output-transform op chain. -/
def pushAcesOutput (style : String) (invert : Bool) :
    Option (Except String (List COp)) :=
  match acesOutputs.find? (fun v => v.name == style) with
  | none => none
  | some v =>
    if invert then some (.error "UNSUPPORTED")
    else
      -- upperBound = 8*(128 + 768*log2(peak/100)/log2(100))
      let u := fmul (fconst 8)
        (fadd (fconst 128) (fmul (fconst 768)
          (fdiv (fbits (log2f (f32of (fdiv v.peak (fconst 100)))))
                (fbits (log2f (f32of (fconst 100)))))))
      let head := [pushMat3 ap0ToAp1, pushRangeClamp 0 u, pushMat3 ap1ToAp0,
                    .aces2 (aces2Scalars v.peak v.lim) false,
                    pushRangeClamp 0 (fdiv v.peak (fconst 100))]
      (match v.enc with
       | some e => pushScaleWhite v.lim e
       | none => .ok []).bind (fun sw =>
        let ls : List COp := if v.lscale != fconst 1 then [pushScale3 v.lscale] else []
        let mxyz : Except String (List COp) :=
          match aces2Rgb2xyz v.lim with
          | some m => .ok [pushMat3 m]
          | none => .error "UNSUPPORTED"
        mxyz.map (fun t => head ++ sw ++ ls ++ t))

/-! ## Inversion (`toc_invert_op`) and the dispatch -/

/-- Toggle a fixed-function style's forward/inverse partner. -/
def flipStyle (s : Nat) : Nat := if s % 2 == 0 then s + 1 else s - 1

/-- `toc_invert_op` for the op kinds the builtin expansion produces. -/
def invertCOp : COp → Except String COp
  | .matrix m off =>
    match inv4x4 (transpose4 m) with
    | none => .error "NONINVERTIBLE"
    | some inv => .ok (.matrix (transpose4 inv) ((matvec4 inv off).map fneg))
  | .range scale offset lo hi cl hi' =>
    let (ns, no, mn, mx) := invertRange scale offset lo hi
    .ok (.range ns no mn mx cl hi')
  | .exponent e mir => .ok (.exponent (e.map finv) mir)
  | .expLinear sc of gm bk sl inv mir => .ok (.expLinear sc of gm bk sl (!inv) mir)
  | .log ls lo ns no base inv => .ok (.log ls lo ns no base (!inv))
  | .logCamera ls lo ns no brk sl so base inv =>
    .ok (.logCamera ls lo ns no brk sl so base (!inv))
  | .cdl sl of pw sat luma cl inv => .ok (.cdl sl of pw sat luma cl (!inv))
  | .fixed style np p => .ok (.fixed (flipStyle style) np p)
  | .lut1d .. | .lut3d .. | .aces2 .. => .error "NONINVERTIBLE"

/-- Invert every op in order, stopping at the first failure. -/
def invertOps : List COp → Except String (List COp)
  | [] => .ok []
  | op :: rest =>
    (invertCOp op).bind (fun o => (invertOps rest).map (fun r => o :: r))

/-- The explicit style branches of `toc_builtin_expand`. -/
def explicitBuiltin (style : String) : Option (Except String (List COp)) :=
  let ok := fun (l : List COp) => some (.ok l)
  if style == "ACEScg_to_ACES2065-1" then ok [pushMat3 ap1ToAp0]
  else if style == "ACES2065-1_to_ACEScg" then ok [pushMat3 ap0ToAp1]
  else if style == "ACEScct_to_ACES2065-1" then
    ok [pushAcescctLog true, pushMat3 ap1ToAp0]
  else if style == "ACES2065-1_to_ACEScct" then
    ok [pushMat3 ap0ToAp1, pushAcescctLog false]
  else if style == "ACEScc_to_ACES2065-1" then
    -- Clamp the ACEScc input to its minimum ACEScc(0) (a no-op for valid codes).
    ok [pushRangeClamp (fdiv (fadd (fconst (-16)) (fconst 9.72)) (fconst 17.52)) (fconst 1e30),
        pushAcesccLog true, pushMat3 ap1ToAp0]
  else if style == "ACES2065-1_to_ACEScc" then
    ok [pushMat3 ap0ToAp1, pushAcesccLog false,
        pushRangeClamp (fdiv (fadd (fconst (-16)) (fconst 9.72)) (fconst 17.52)) (fconst 1e30)]
  else if style == "UTILITY - ACES-AP0_to_CIE-XYZ-D65_BFD" then
    -- AP0 (D60) -> CIE-XYZ with Bradford adaptation to D65.
    some (pushCspaceNamed "Linear-AP0" "CIE-XYZ-D65")
  else if style == "ACES-LMT - ACES 1.3 Reference Gamut Compression" then
    -- AP0->AP1, ACES 1.3 gamut compress, AP1->AP0.
    ok [pushMat3 ap0ToAp1,
        .fixed 4 7 ([fconst 1.147, fconst 1.264, fconst 1.312,
                     fconst 0.815, fconst 0.803, fconst 0.880, fconst 1.2, 0]),
        pushMat3 ap1ToAp0]
  else none

/-- `toc_builtin_expand`: expand a builtin style into a flat op list. -/
def builtinExpand (style : String) (invert : Bool) : Except String (List COp) :=
  let res : Option (Except String (List COp)) :=
    match pushAcesOutput style invert with
    | some r => some r
    | none =>
      match explicitBuiltin style with
      | some r => some r
      | none =>
        match pushCamera style with
        | some r => some r
        | none =>
          match pushDisplayXform style with
          | some r => some r
          | none => pushCspaceConvert style
  match res with
  | none => .error "UNSUPPORTED"
  | some (.error e) => .error e
  | some (.ok ops) =>
    if invert then invertOps ops.reverse else .ok ops

end Tocio
