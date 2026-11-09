/-
  TinyEXR - Lean 4 formalization of the tocio processor IR.

  First slice: the op list type and basic operations. Full lowering from
  config + endpoints comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Op

namespace Tocio

/-- An op list is a list of ops, each tagged with its kind. -/
structure OpList where
  ops : List OpKind
  deriving Repr

namespace OpList

def empty : OpList := { ops := [] }

def append (l : OpList) (k : OpKind) : OpList := { ops := l.ops ++ [k] }

def length (l : OpList) : Nat := l.ops.length

theorem empty_length : OpList.empty.length = 0 := by rfl

theorem append_length (l : OpList) (k : OpKind) :
    (l.append k).length = l.length + 1 := by
  unfold append length
  simp

end OpList

end Tocio