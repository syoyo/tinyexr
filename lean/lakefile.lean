/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  lakefile for the `ExrSpec` package. Depends on mathlib (pinned to the
  toolchain-matched v4.35.0 tag); the prebuilt olean cache is fetched with
  `lake exe cache get` (see `make lean-check`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Lake
open Lake DSL

package exrSpec where
  -- Formalization artifact; proofs must stay sorry-free.
  leanOptions := #[⟨`warningAsError, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib ExrSpec where
  globs := #[`ExrSpec, `Exr.+]

/-- Structural conformance checker (machine-readable report). -/
lean_exe exrcheck where
  root := `ExrCheck

/-- Seeded generator of well-formed structural EXR files. -/
lean_exe exrgen where
  root := `ExrGen

/-- Codec test-vector generator for the differential harness. -/
lean_exe codecgen where
  root := `CodecGen
