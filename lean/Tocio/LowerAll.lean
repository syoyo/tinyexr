/-
  TinyEXR - Lean 4 formalization of lowering a list of transforms.

  Lowers a list of TransformKind into a single OpList by appending
  each lowered transform. Includes length theorems.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Transform
import Tocio.Processor

namespace Tocio

/-- Lower a list of transforms into an op list. -/
def lowerAll (ts : List TransformKind) : OpList :=
  ts.foldl (fun acc t => { ops := acc.ops ++ (lowerTransform t).ops }) OpList.empty

/-- Empty list lowers to empty. -/
theorem lowerAll_nil : (lowerAll []).length = 0 := by
  unfold lowerAll OpList.length OpList.empty
  simp

-- Theorems about lowerAll length are deferred to a later slice.

end Tocio