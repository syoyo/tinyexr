/-
  TinyEXR - Lean 4 formalization of tocio transform lowering with config.

  Lowers a config + src/dst colorspace names into an op list. Uses
  Resolve for colorspace lookup and Transform for op generation.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Config
import Tocio.Transform
import Tocio.Resolve
import Tocio.Processor

namespace Tocio

/-- Lower a colorspace transform if both src and dst resolve. -/
def lowerColorSpace (c : Config) (src dst : String) : Option OpList :=
  match colorSpaceTransform c src dst with
  | some t => some (lowerTransform t)
  | none => none

/-- If both resolve, lowering succeeds. -/
theorem lowerColorSpace_some (c : Config) (src dst : String)
    (hs : resolveColorSpace c src ≠ none) (hd : resolveColorSpace c dst ≠ none) :
    (lowerColorSpace c src dst).isSome = true := by
  unfold lowerColorSpace
  have h := colorSpaceTransform_some c src dst hs hd
  simp [h]

/-- Lowering a noop transform gives empty. -/
theorem lower_noop (t : TransformKind) (h : t = TransformKind.noop) :
    (lowerTransform t).length = 0 := by
  subst h
  unfold lowerTransform OpList.length OpList.empty
  rfl

end Tocio