/-
  TinyEXR - byte budget for whole-image flat allocations (task.md S2).

  Models `exr_flat_planes_size`: the pointer array plus one 8-byte-aligned
  slot per sampled channel plane. `exr_context_set_max_image_bytes` rejects
  an image whose computed size exceeds the configured limit.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Exr

set_option linter.unusedVariables false

structure BudgetChan where
  xSampling : Nat
  ySampling : Nat
  pixelType : Nat
  deriving Repr

/-- `exr_num_samples` on a non-empty integer interval. -/
def numSamples (lo hi step : Int) : Nat :=
  if hi < lo then 0 else ((hi - lo) / step).toNat + 1

/-- `exr_pixel_size`. -/
def budgetPixelSize (t : Nat) : Nat :=
  if t == 1 then 2 else 4  -- HALF = 2, UINT/FLOAT = 4

def align8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- Byte count of one channel plane slot (never zero). -/
def planeSlot (c : BudgetChan) (w h : Nat) : Nat :=
  let nx := numSamples 0 ((w : Int) - 1) (c.xSampling : Int)
  let ny := numSamples 0 ((h : Int) - 1) (c.ySampling : Int)
  align8 (if nx * ny * (budgetPixelSize c.pixelType) == 0 then 1
          else nx * ny * (budgetPixelSize c.pixelType))

/-- Total native bytes reported by `exr_flat_planes_size`. -/
def flatPlanesSize (cs : List BudgetChan) (w h : Nat) : Nat :=
  cs.length * 8 + (cs.map (fun c => planeSlot c w h)).sum

/-- A configured limit rejects exactly when the computed size exceeds it. -/
def budgetReject (limit size : Nat) : Bool := limit != 0 && size > limit

theorem budgetReject_mono {limit size size' : Nat} (hle : size ≤ size')
    (h : budgetReject limit size) : budgetReject limit size' := by
  simp [budgetReject] at h ⊢
  rcases h with ⟨hlim, hsize⟩
  exact ⟨hlim, by omega⟩

end Exr
