/-
  TinyEXR - Lean 4 formalization of the tocio (OpenColorIO) op IR.

  First slice: the op-kind and FixedFunction style enums from tocio.h,
  with the invert-pair convention (_INV = forward + 1) and basic
  decidability. Color-op semantics and lowering come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- Op kinds in the tocio IR (mirrors toc_op_kind in tocio.h). -/
inductive OpKind where
  | matrix
  | range
  | exponent
  | expLinear
  | log
  | logCamera
  | cdl
  | lut1d
  | lut3d
  | fixedfunc
  | acesOutput
  | noop
  deriving Repr, DecidableEq, Inhabited

/-- FixedFunction style ids (mirrors toc_ff_style). _INV variants are forward+1. -/
inductive FfStyle where
  | acesGlow10
  | acesGlow10Inv
  | acesDarkToDim10
  | acesDarkToDim10Inv
  | acesGamutComp13
  | acesGamutComp13Inv
  | rec2100Surround
  | rec2100SurroundInv
  | acesGlow03
  | acesGlow03Inv
  | acesRedMod03
  | acesRedMod03Inv
  | acesRedMod10
  | acesRedMod10Inv
  | rgbToHsv
  | hsvToRgb
  | xyzToXyY
  | xyYToXyz
  | xyzToUvY
  | uvYToXyz
  | xyzToLuv
  | luvToXyz
  | linToPq
  | pqToLin
  | linToHlg
  | hlgToLin
  deriving Repr, DecidableEq, Inhabited

/-- A style is an inverse variant iff its tag is odd (the _INV slots). -/
def FfStyle.isInv (s : FfStyle) : Bool :=
  match s with
  | .acesGlow10Inv | .acesDarkToDim10Inv | .acesGamutComp13Inv
  | .rec2100SurroundInv | .acesGlow03Inv | .acesRedMod03Inv
  | .acesRedMod10Inv | .pqToLin | .hlgToLin | .hsvToRgb
  | .xyYToXyz | .uvYToXyz | .luvToXyz => true
  | _ => false

/-- Forward counterpart of an inverse style is the preceding tag. -/
def FfStyle.forwardOf (s : FfStyle) : FfStyle :=
  if s.isInv then
    match s with
    | .acesGlow10Inv => .acesGlow10
    | .acesDarkToDim10Inv => .acesDarkToDim10
    | .acesGamutComp13Inv => .acesGamutComp13
    | .rec2100SurroundInv => .rec2100Surround
    | .acesGlow03Inv => .acesGlow03
    | .acesRedMod03Inv => .acesRedMod03
    | .acesRedMod10Inv => .acesRedMod10
    | .pqToLin => .linToPq
    | .hlgToLin => .linToHlg
    | .hsvToRgb => .rgbToHsv
    | .xyYToXyz => .xyzToXyY
    | .uvYToXyz => .xyzToUvY
    | .luvToXyz => .xyzToLuv
    | _ => s
  else s

theorem forwardOf_inv (s : FfStyle) (h : s.isInv = true) :
    (s.forwardOf).isInv = false := by
  cases s <;> simp [FfStyle.isInv, FfStyle.forwardOf] at h ⊢

/-- Forward styles are not inverse. -/
theorem forward_not_inv (s : FfStyle) (h : s.isInv = false) :
    s.forwardOf = s := by
  cases s <;> simp [FfStyle.isInv, FfStyle.forwardOf] at h ⊢

/-- For every inverse style, forwardOf yields a non-inverse style. -/
theorem inv_forward_not_inv (s : FfStyle) (h : s.isInv = true) :
    (s.forwardOf).isInv = false := by
  cases s <;> simp [FfStyle.isInv, FfStyle.forwardOf] at h ⊢

end Tocio