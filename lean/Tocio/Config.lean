/-
  TinyEXR - Lean 4 formalization of the tocio OCIO config structure.

  First slice: the config's colorspace/display/view/view-transform/look lists
  as finite sequences of names, with introspection counts. Resolution and
  transform lowering come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- A named colorspace. -/
structure ColorSpace where
  name : String
  deriving Repr, DecidableEq

/-- A display with its views. -/
structure View where
  name : String
  colorspace : String
  deriving Repr, DecidableEq

structure Display where
  name : String
  views : List View
  deriving Repr, DecidableEq

/-- A view transform (name only at this slice). -/
structure ViewTransform where
  name : String
  deriving Repr, DecidableEq

/-- A look (name only at this slice). -/
structure Look where
  name : String
  deriving Repr, DecidableEq

/-- The OCIO config as a collection of named lists. -/
structure Config where
  colorspaces    : List ColorSpace
  displays       : List Display
  viewTransforms : List ViewTransform
  looks          : List Look
  roles          : List (String × String)
  deriving Repr

namespace Config

def numColorSpaces (c : Config) : Nat := c.colorspaces.length
def numDisplays (c : Config) : Nat := c.displays.length
def numViewTransforms (c : Config) : Nat := c.viewTransforms.length
def numLooks (c : Config) : Nat := c.looks.length

def colorSpaceName (c : Config) (i : Nat) : Option String :=
  (c.colorspaces[i]?).map (·.name)

def displayName (c : Config) (i : Nat) : Option String :=
  (c.displays[i]?).map (·.name)

def viewTransformName (c : Config) (i : Nat) : Option String :=
  (c.viewTransforms[i]?).map (·.name)

def lookName (c : Config) (i : Nat) : Option String :=
  (c.looks[i]?).map (·.name)

def resolveRole (c : Config) (role : String) : Option String :=
  (c.roles.find? (fun p => p.1 = role)).map (·.2)

theorem numColorSpaces_nonneg (c : Config) : c.numColorSpaces ≥ 0 := Nat.zero_le _

end Config

end Tocio