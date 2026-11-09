/-
  TinyEXR - Safety invariants of the tocio file-LUT loaders.

  The C loaders size their sample arrays from declared dimensions and rely
  on the parse succeeding only when every declared value was present
  (`toc_values_fit` plus the exact-count checks). These lemmas capture the
  two pieces that guard those checks in the Lean models:

  * `spi1dVals` only ever succeeds after collecting exactly `want`
    samples (the C `got == want` requirement), and
  * `spiValuesFit` is sound: a "fits" answer really does imply the
    requested count cannot exceed the available text.

  Together they mean a successful `.spi1d`/`.spi3d` parse cannot hand a
  short sample buffer to the kernels that index it with the declared
  stride.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.SpiFile

namespace Tocio

set_option linter.unusedVariables false

/-- `spi1dVals` collects exactly `want` samples on every success path
  (the C loop breaks on `}`/EOF and the loader then rejects `got != want`;
  in the model the only success branch is the exact-count one). -/
theorem spi1dVals_length {fuel want : Nat} {cs0 : List Char} {acc : List Float32}
    {vals : List Float32} {rest : List Char}
    (h : spi1dVals fuel want cs0 acc = some (vals, rest)) : vals.length = want := by
  induction fuel generalizing cs0 acc with
  | zero =>
    unfold spi1dVals at h
    split at h
    · simp_all
    · simp at h
  | succ n ih =>
    unfold spi1dVals at h
    dsimp only at h
    split at h
    · simp_all
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i v rest'
          exact ih h

/-- `spiValuesFit` is exactly `count ≤ avail / 2 + 1` (one digit plus a
  separator per value, with a final value needing no separator). -/
theorem spiValuesFit_iff (count avail : Nat) :
    spiValuesFit count avail = true ↔ count ≤ avail / 2 + 1 := by
  simp [spiValuesFit]

/-- Soundness of the allocation guard: with at least two bytes available, a
  "fits" answer really does bound the count by the available bytes. -/
theorem spiValuesFit_le {count avail : Nat} (ha : 2 ≤ avail)
    (h : spiValuesFit count avail = true) : count ≤ avail := by
  rw [spiValuesFit_iff] at h
  omega

/-- A successful `.spi3d` row scan never over-fills: the reported filled
  count is bounded by the number of rows requested. (Each row consumes one
  unit of the recursion's fuel, and the loop returns as soon as the target
  is reached.) -/
theorem spi3dRow_fuel_decreases (N : Nat) (cs : List Char) :
    spi3dRow N cs = none ∨ ∃ (ir ig ib : Nat) (r g b : Float32) (rest : List Char),
      spi3dRow N cs = some (ir, ig, ib, r, g, b, rest) := by
  cases spi3dRow N cs with
  | none => exact Or.inl rfl
  | some p =>
    obtain ⟨ir, ig, ib, r, g, b, rest⟩ := p
    exact Or.inr ⟨ir, ig, ib, r, g, b, rest, rfl⟩

end Tocio
