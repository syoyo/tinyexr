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

/-- ASTC dual RGBA block encoder differential checker. -/
@[default_target]
lean_exe astcdualcheck where
  root := `AstcDualCheck

/-- ASTC partition RGB block encoder differential checker. -/
@[default_target]
lean_exe astcpartenccheck where
  root := `AstcPartencCheck

/-- ASTC LDR block encoder differential checker. -/
@[default_target]
lean_exe astcldrcheck where
  root := `AstcLdrCheck

/-- ASTC UASTC LDR block encoder differential checker. -/
@[default_target]
lean_exe astcuastccheck where
  root := `AstcUastcCheck

/-- ASTC HDR block encoder differential checker. -/
@[default_target]
lean_exe astchdrenccheck where
  root := `AstcHdrEncCheck

/-- ASTC HDR image-level encoder differential checker. -/
@[default_target]
lean_exe astchdrimgcheck where
  root := `AstcHdrImgCheck

/-- ASTC LDR image-level compress driver checker (C writer vs Lean model). -/
@[default_target]
lean_exe astcldrimgcheck where
  root := `AstcLdrImgCheck

/-- ASTC LDR image-level decoder checker (C writer vs Lean model). -/
@[default_target]
lean_exe astcldrdeccheck where
  root := `AstcLdrDecCheck

/-- texcomp "uni" container checker (C writer vs Lean model). -/
@[default_target]
lean_exe unicheck where
  root := `UniCheck

/-- texcomp "uni" BC1/BC7 transcode checker (C vs Lean model). -/
@[default_target]
lean_exe unitranscodecheck where
  root := `UniTranscodeCheck

/-- ETC2 RGB / EAC alpha block-encoder checker (C vs Lean model). -/
@[default_target]
lean_exe etc2enccheck where
  root := `Etc2EncCheck

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

/-- BC6H mode-0 encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hm0check where
  root := `Bc6hMode0Check

/-- Correctly-rounded sqrtf differential checker (C vs Lean). -/
@[default_target]
lean_exe sqrtcheck where
  root := `SqrtCheck

/-- BC6H mode-12/13 encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hm1213check where
  root := `Bc6hM1213Check

/-- BC6H mode-2/3/4 encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hm234check where
  root := `Bc6hM234Check

/-- BC6H mode-6/7/8 encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hm678check where
  root := `Bc6hM678Check

/-- BC6H mode-1/9 encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hm19check where
  root := `Bc6hM19Check

/-- BC6H signed (`sf16`) encoder differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hsf16check where
  root := `Bc6hSf16Check

/-- BC6H per-block mode-selection differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc6hblockcheck where
  root := `Bc6hBlockCheck

/-- BC7 RDO pass differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe bc7rdocheck where
  root := `Bc7RdoCheck

/-- ASTC weight-decimation differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcdecimcheck where
  root := `AstcDecimCheck

/-- ASTC weight LUT + infill differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcinfillcheck where
  root := `AstcInfillCheck

/-- ASTC encoder block-mode parse differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcblockmodecheck where
  root := `AstcBlockModeCheck


/-- ASTC partition-cache differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcpartitioncheck where
  root := `AstcPartitionCheck

/-- ASTC block-mode candidate list differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astccandidatescheck where
  root := `AstcCandidatesCheck

/-- ASTC endpoint plumbing differential checker (C vectors vs Lean). -/
@[default_target]
lean_exe astcendpointscheck where
  root := `AstcEndpointsCheck

/-- ASTC fit-path (projection / weights / fit / misc) differential checker. -/
@[default_target]
lean_exe astcfitscheck where
  root := `AstcFitsCheck

/-- ASTC ISE encode bits differential checker. -/
@[default_target]
lean_exe astcisecheck where
  root := `AstcIseCheck

/-- ASTC score-from-ideal / score-batch differential checker. -/
@[default_target]
lean_exe astcscorecheck where
  root := `AstcScoreCheck

/-- ASTC least-squares / evaluation differential checker. -/
@[default_target]
lean_exe astclsqcheck where
  root := `AstcLsqCheck

/-- ASTC partition-search / classification differential checker. -/
@[default_target]
lean_exe astcpartselcheck where
  root := `AstcPartselCheck

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

/-- Tocio YAML parser differential checker (C vectors vs Lean model). -/
@[default_target]
lean_exe yamlcheck where
  root := `YamlCheck

/-- Tocio config-query differential checker (C vectors vs Lean model). -/
@[default_target]
lean_exe configcheck where
  root := `ConfigCheck

/-- Tocio processor-build differential checker (C vectors vs Lean model). -/
@[default_target]
lean_exe proccheck where
  root := `ProcessorCheck

/-- ASTC debug dump (Lean side). -/
@[default_target]
lean_exe astcdebug where
  root := `AstcDebug

/-- ASTC LDR block encoder debug driver (decision trace). -/
@[default_target]
lean_exe astcldrdbgmain where
  root := `AstcLdrDbgMain
