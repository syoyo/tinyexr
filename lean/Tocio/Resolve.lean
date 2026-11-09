/-
  TinyEXR - Lean 4 formalization of tocio config resolution.

  First slice: resolve a colorspace by name, and build a transform kind
  from src/dst colorspace names. Full config validation and nested
  transform lowering come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Config
import Tocio.Transform

namespace Tocio

/-- Resolve a colorspace index by name (returns none if not found). -/
def resolveColorSpace (c : Config) (name : String) : Option Nat :=
  (List.range c.colorspaces.length).find? (fun i =>
    match c.colorspaces[i]? with
    | some cs => cs.name = name
    | none => false)

/-- Build a transform kind from src/dst colorspace names. -/
def colorSpaceTransform (c : Config) (src dst : String) : Option TransformKind :=
  match resolveColorSpace c src, resolveColorSpace c dst with
  | some _, some _ => some TransformKind.colorSpace
  | _, _ => none

/-- If both src and dst resolve, the transform is colorSpace. -/
theorem colorSpaceTransform_some (c : Config) (src dst : String)
    (hs : resolveColorSpace c src ≠ none) (hd : resolveColorSpace c dst ≠ none) :
    colorSpaceTransform c src dst = some TransformKind.colorSpace := by
  unfold colorSpaceTransform
  cases h1 : resolveColorSpace c src with
  | none => simp [h1] at hs
  | some _ =>
    cases h2 : resolveColorSpace c dst with
    | none => simp [h2] at hd
    | some _ => rfl

/-- Resolve returns none for empty config. -/
theorem resolve_empty (name : String) :
    resolveColorSpace { colorspaces := [], displays := [], viewTransforms := [], looks := [], roles := [] } name = none := by
  unfold resolveColorSpace
  simp

end Tocio