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
  globs := #[`ExrSpec, `Exr.+, `Texcomp.+, `Tocio.+]

/-- Structural conformance checker (machine-readable report). -/
@[default_target]
lean_exe exrcheck where
  root := `ExrCheck

/-- Seeded generator of well-formed structural EXR files. -/
@[default_target]
lean_exe exrgen where
  root := `ExrGen

/-- Codec test-vector generator for the differential harness. -/
@[default_target]
lean_exe codecgen where
  root := `CodecGen

/-- BC6H differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe bc6hcheck where
  root := `Bc6hCheck

/-- BC7 differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe bc7check where
  root := `Bc7Check

/-- BC1/BC3/BC5 differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe bc135check where
  root := `Bc135Check

/-- ETC2/EAC differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe etc2check where
  root := `Etc2Check

/-- ASTC differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe astccheck where
  root := `AstcCheck

/-- ASTC HDR differential checker (C vectors vs Lean decoder). -/
@[default_target]
lean_exe astchdrcheck where
  root := `AstcHdrCheck

/-- ASTC HDR endpoint pack differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcpackcheck where
  root := `AstcPackCheck

/-- DDS/KTX header byte-layout checker (C writers vs Lean model). -/
@[default_target]
lean_exe ddsktxcheck where
  root := `DdsKtxCheck

/-- BC1 encoder differential checker (C vectors vs Lean encoder). -/
@[default_target]
lean_exe bc1enccheck where
  root := `Bc1EncCheck

/-- BC4/BC5 encoder differential checker (C vectors vs Lean encoder). -/
@[default_target]
lean_exe bc4enccheck where
  root := `Bc4EncCheck

/-- ASTC colour-quantizer differential checker (C vectors vs Lean model). -/
@[default_target]
lean_exe astcquantcheck where
  root := `AstcQuantCheck

/-- BC7 pack/palette differential checker (C vectors vs Lean encoder). -/
@[default_target]
lean_exe bc7packcheck where
  root := `Bc7PackCheck

/-- BC7 mode-6 encoder differential checker (C vectors vs Lean encoder). -/
@[default_target]
lean_exe bc7m6check where
  root := `Bc7Mode6Check

/-- BC7 per-mode candidate differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc7seedcheck where
  root := `Bc7SeedCheck

/-- BC7 full block-encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc7enccheck2 where
  root := `Bc7EncCheck

/-- BC6H encoder kernel differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hkerncheck where
  root := `Bc6hKernCheck

/-- Tocio op differential checker (C vectors vs Lean kernels). -/
@[default_target]
lean_exe tociocheck where
  root := `TocioCheck

/-- LUT-file differential checker (C vectors vs Lean kernels). -/
@[default_target]
lean_exe lutcheck where
  root := `LutCheck

/-- SPI file differential checker (C vectors vs Lean parsers). -/
@[default_target]
lean_exe spicheck where
  root := `SpiCheck

/-- CLF differential checker (C vectors vs Lean parser). -/
@[default_target]
lean_exe clfcheck where
  root := `ClfCheck

/-- CSP differential checker (C vectors vs Lean parser). -/
@[default_target]
lean_exe cspcheck where
  root := `CspCheck

/-- ASTC debug dump (Lean side). -/
@[default_target]
lean_exe astcdebug where
  root := `AstcDebug
