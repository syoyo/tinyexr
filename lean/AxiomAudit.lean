/-
  TinyEXR - audit transitive axioms of first-party theorems.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import ExrSpec
import ExrGen
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut bvCount : Nat := 0
  let mut nativeCount : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (name.toString.startsWith "Exr." ||
        name.toString.startsWith "ExrGen." ||
        name.toString.startsWith "ExrMath." ||
        name.toString.startsWith "Texcomp." ||
        name.toString.startsWith "Tocio." ||
        name.toString.startsWith "Tir." ||
        name.toString.startsWith "Math." ||
        name.toString.startsWith "_private.Exr." ||
        name.toString.startsWith "_private.ExrGen." ||
        name.toString.startsWith "_private.ExrMath." ||
        name.toString.startsWith "_private.Texcomp." ||
        name.toString.startsWith "_private.Tocio." ||
        name.toString.startsWith "_private.Tir." ||
        name.toString.startsWith "_private.Math.") then
      count := count + 1
      let axioms ← collectAxioms name
      if axioms.any (fun ax => ax.toString.contains "._native.bv_decide.ax_") then
        bvCount := bvCount + 1
      if axioms.any (fun ax => ax.toString.contains "._native.native_decide.ax_") then
        nativeCount := nativeCount + 1
      for ax in axioms do
        let s := ax.toString
        let standard := ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound
        let certificate := (s.startsWith "Exr." || s.startsWith "_private.Exr." ||
          s.startsWith "ExrGen." || s.startsWith "_private.ExrGen." ||
          s.startsWith "ExrMath." || s.startsWith "_private.ExrMath." ||
          s.startsWith "Texcomp." || s.startsWith "_private.Texcomp." ||
          s.startsWith "Tocio." || s.startsWith "_private.Tocio." ||
          s.startsWith "Tir." || s.startsWith "_private.Tir." ||
          s.startsWith "Math." || s.startsWith "_private.Math.") && s.contains "._native.bv_decide.ax_"
        let approvedFixtures : List String := [
          "ExrGen.generate_scanline_parses", "ExrGen.generate_tiled_parses",
          "ExrGen.generate_mipmap_parses", "ExrGen.generate_ripmap_parses",
          "ExrGen.generate_deepscanline_parses", "ExrGen.generate_multipart_parses",
          "ExrGen.generate_scanline_valid", "ExrGen.generate_tiled_valid",
          "ExrGen.generate_multipart_valid", "ExrGen.generate_multipart_valid_openexr",
          "ExrMath.log2f_pow2_exact", "ExrMath.exp2f_int_exact",
          "ExrMath.powf_pow2_one_exact", "ExrMath.log2f_3ulp_witness",
          "ExrMath.exp2f_1ulp_witness", "ExrMath.powf_one_44ulp_witness",
          "ExrMath.powf_one_uniform_16_ulp_false"]
        -- Tocio/Math concrete checks (Float arithmetic and exhaustive fixture
        -- witnesses) use native_decide locally, same pattern as the ExrGen
        -- fixture checks: the axiom must be owned by the theorem itself. These
        -- are regression checks, not library proofs.
        let fixture := (approvedFixtures.contains name.toString &&
          s.startsWith (name.toString ++ "._native.native_decide.ax_")) ||
          ((name.toString.startsWith "Tocio." ||
        name.toString.startsWith "Tir." || name.toString.startsWith "Texcomp." ||
        name.toString.startsWith "ExrMath." ||
        name.toString.startsWith "Math.") &&
            s.startsWith (name.toString ++ "._native.native_decide.ax_"))
        unless standard || certificate || fixture do
          throwError "unexpected axiom {ax} in {name}"
  if count == 0 then throwError "no first-party theorems audited"
  logInfo m!"axiom audit: {count} first-party theorems; {bvCount} use bv_decide certificates; {nativeCount} use approved native fixture checks; no unexpected axioms"
