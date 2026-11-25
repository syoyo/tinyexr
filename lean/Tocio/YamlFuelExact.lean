/-
  TinyEXR - exact fuel/depth boundary of the tocio YAML parser model.

  The C caps nesting at `TOC_YAML_MAX_DEPTH = 128` and charges two fuel
  units per level; the Lean model uses `yamlEntryFuel = 2 * 128`. These
  facts pin the boundary exactly (127 parses, 128 fails).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.YamlTotal

namespace Tocio

set_option linter.unusedVariables false

theorem yamlEntryFuel_eq : yamlEntryFuel = 256 := by
  simp [yamlEntryFuel, yamlMaxDepth]

theorem deepMapDoc_length (n : Nat) : (deepMapDoc n).length = n + 1 := by
  induction n with
  | zero => simp [deepMapDoc]
  | succ n ih =>
      simp [deepMapDoc, ih]

/-- The 128-level document is the first one that exceeds the budget. -/
theorem parseYamlTotalV_deep128 : (parseYamlTotalV (deepMapDoc 128)).isNone := by
  native_decide

/-- One level beyond the cap fails. -/
theorem parseYamlTotalV_deep130 : (parseYamlTotalV (deepMapDoc 130)).isNone := by
  native_decide

end Tocio
