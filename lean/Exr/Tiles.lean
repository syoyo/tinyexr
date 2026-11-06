/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Tile and scan-line chunk arithmetic.

  * Scan-line blocks: `linesPerBlock` per compression (see `Exr.Attribute`);
    the chunk count is `ceil(height / linesPerBlock)`.
  * Tiled parts: resolution levels per `ONE_LEVEL` / `MIPMAP_LEVELS` /
    `RIPMAP_LEVELS` and `ROUND_DOWN` / `ROUND_UP`; level dimensions are
    obtained by repeatedly halving with the selected rounding, clamped at 1.
  * Every counted quantity is proven positive when its input dimensions are.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Attribute

namespace Exr

namespace Tiles

/-- Halve a dimension one level: floor for `ROUND_DOWN`, ceil for `ROUND_UP`,
    clamped to 1. -/
def half (up : TypedAttr.RoundingMode) (d : Nat) : Nat :=
  max 1 (match up with
    | .roundUp => (d + 1) / 2
    | .roundDown => d / 2)

theorem half_pos (up : TypedAttr.RoundingMode) (d : Nat) : 0 < half up d := by
  unfold half
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left ..)

theorem half_le_self {up : TypedAttr.RoundingMode} {d : Nat} (hd : 1 ≤ d) : half up d ≤ d := by
  cases up <;> simp [half] <;> omega

theorem half_lt_self {up : TypedAttr.RoundingMode} {d : Nat} (hd : 2 ≤ d) : half up d < d := by
  cases up <;> simp [half] <;> omega

theorem half_monotone {up : TypedAttr.RoundingMode} {a b : Nat} (h : a ≤ b) :
    half up a ≤ half up b := by
  cases up <;> simp [half] <;> omega

/-- Level size after `l` halvings. Level 0 is the full dimension. -/
def levelSize (up : TypedAttr.RoundingMode) (d l : Nat) : Nat :=
  match l with
  | 0 => d
  | l + 1 => half up (levelSize up d l)

theorem levelSize_succ (up : TypedAttr.RoundingMode) (d l : Nat) :
    levelSize up d (l + 1) = half up (levelSize up d l) := rfl

theorem levelSize_pos {up : TypedAttr.RoundingMode} {d : Nat} (hd : 1 ≤ d) (l : Nat) :
    0 < levelSize up d l := by
  induction l with
  | zero => show 0 < d; omega
  | succ l ih =>
    rw [levelSize_succ]
    exact half_pos up _

theorem levelSize_succ_le {up : TypedAttr.RoundingMode} {d : Nat} (hd : 1 ≤ d) (l : Nat) :
    levelSize up d (l + 1) ≤ levelSize up d l := by
  rw [levelSize_succ]
  exact half_le_self (levelSize_pos hd l)

theorem levelSize_antitone {up : TypedAttr.RoundingMode} {d : Nat} (hd : 1 ≤ d) {l l' : Nat}
    (h : l ≤ l') : levelSize up d l' ≤ levelSize up d l := by
  induction l' with
  | zero =>
    have hl : l = 0 := Nat.eq_zero_of_le_zero h
    subst hl
    exact Nat.le_refl _
  | succ l' ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact Nat.le_refl _
    · have hle : l ≤ l' := Nat.lt_succ_iff.mp hlt
      exact Nat.le_trans (levelSize_succ_le hd l') (ih hle)

/-- Number of resolution levels for a dimension: halve until 1. -/
def numLevelsAux (up : TypedAttr.RoundingMode) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, d =>
    if d ≤ 1 then 1
    else 1 + numLevelsAux up fuel (half up d)

/-- Level count for a dimension (search bounded by `d + 1`, which is enough
    because each halving of `d ≥ 2` strictly decreases the dimension). -/
def numLevels (up : TypedAttr.RoundingMode) (d : Nat) : Nat :=
  numLevelsAux up (d + 1) d

theorem numLevelsAux_pos (up : TypedAttr.RoundingMode) (fuel d : Nat) : 0 < numLevelsAux up fuel d := by
  induction fuel generalizing d with
  | zero => simp [numLevelsAux]
  | succ fuel ih =>
    unfold numLevelsAux
    split
    · simp
    · omega

theorem numLevels_pos (up : TypedAttr.RoundingMode) (d : Nat) : 0 < numLevels up d :=
  numLevelsAux_pos up (d + 1) d

/-- Mipmap level count from width/height. -/
def mipmapLevelCount (up : TypedAttr.RoundingMode) (w h : Nat) : Nat :=
  max (numLevels up w) (numLevels up h)

theorem mipmapLevelCount_pos (up : TypedAttr.RoundingMode) (w h : Nat) :
    0 < mipmapLevelCount up w h :=
  Nat.lt_of_lt_of_le (numLevels_pos up w) (Nat.le_max_left ..)

/-! ### Chunk counting -/

/-- Scan-line chunks for a part with `height` rows at `lpb` lines per block. -/
def scanlineChunks (height lpb : Nat) : Nat := (height + lpb - 1) / lpb

theorem scanlineChunks_pos {height lpb : Nat} (hh : 1 ≤ height) (hl : 1 ≤ lpb) :
    0 < scanlineChunks height lpb := by
  unfold scanlineChunks
  have : 0 < height + lpb - 1 := by omega
  exact Nat.div_pos (by omega) (by omega)

theorem scanlineChunks_covers {height lpb : Nat} (hl : 1 ≤ lpb) :
    height ≤ scanlineChunks height lpb * lpb := by
  unfold scanlineChunks
  have h := Nat.div_add_mod (height + lpb - 1) lpb
  have hmod : (height + lpb - 1) % lpb < lpb := Nat.mod_lt _ (by omega)
  rw [Nat.mul_comm]
  omega

/-- Tiles along one dimension. -/
def tilesIn (d tile : Nat) : Nat := (d + tile - 1) / tile

theorem tilesIn_pos {d tile : Nat} (hd : 1 ≤ d) (ht : 1 ≤ tile) :
    0 < tilesIn d tile := by
  unfold tilesIn
  have : 0 < d + tile - 1 := by omega
  exact Nat.div_pos (by omega) (by omega)

theorem tilesIn_covers {d tile : Nat} (ht : 1 ≤ tile) : d ≤ tilesIn d tile * tile := by
  unfold tilesIn
  have h := Nat.div_add_mod (d + tile - 1) tile
  have hmod : (d + tile - 1) % tile < tile := Nat.mod_lt _ (by omega)
  rw [Nat.mul_comm]
  omega

/-- Tiles of one resolution level. -/
def levelTiles (up : TypedAttr.RoundingMode) (tx ty w h l : Nat) : Nat :=
  tilesIn (levelSize up w l) tx * tilesIn (levelSize up h l) ty

theorem levelTiles_pos (up : TypedAttr.RoundingMode) {tx ty w h : Nat} (hw : 1 ≤ w) (hh : 1 ≤ h)
    (htx : 1 ≤ tx) (hty : 1 ≤ ty) (l : Nat) : 0 < levelTiles up tx ty w h l := by
  unfold levelTiles
  exact Nat.mul_pos
    (tilesIn_pos (levelSize_pos hw l) htx)
    (tilesIn_pos (levelSize_pos hh l) hty)

/-- Sum of `f` over `List.range n`. -/
def sumRange (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).sum

theorem le_sumRange {n : Nat} {f : Nat → Nat} (hf : ∀ i, 0 < f i) :
    n ≤ sumRange n f := by
  unfold sumRange
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := hf n
    omega

theorem sumRange_pos {n : Nat} {f : Nat → Nat} (hn : 0 < n) (hf : ∀ i, 0 < f i) :
    0 < sumRange n f :=
  Nat.lt_of_lt_of_le hn (le_sumRange hf)

/-- Total chunk (tile) count for a tiled part. -/
def tiledChunks (mode : TypedAttr.LevelMode) (up : TypedAttr.RoundingMode) (tx ty w h : Nat) : Nat :=
  match mode with
  | .oneLevel =>
    tilesIn w tx * tilesIn h ty
  | .mipmap =>
    sumRange (mipmapLevelCount up w h) (fun l => levelTiles up tx ty w h l)
  | .ripmap =>
    sumRange (numLevels up w) (fun lx =>
      sumRange (numLevels up h) (fun ly =>
        tilesIn (levelSize up w lx) tx * tilesIn (levelSize up h ly) ty))

theorem tiledChunks_pos (mode : TypedAttr.LevelMode) (up : TypedAttr.RoundingMode) {tx ty w h : Nat}
    (htx : 1 ≤ tx) (hty : 1 ≤ ty) (hw : 1 ≤ w) (hh : 1 ≤ h) :
    0 < tiledChunks mode up tx ty w h := by
  unfold tiledChunks
  split
  · exact Nat.mul_pos (tilesIn_pos hw htx) (tilesIn_pos hh hty)
  · exact sumRange_pos (mipmapLevelCount_pos up w h)
      (fun l => levelTiles_pos up hw hh htx hty l)
  · exact sumRange_pos (numLevels_pos up w)
      (fun lx => sumRange_pos (numLevels_pos up h)
        (fun ly => Nat.mul_pos
          (tilesIn_pos (levelSize_pos hw lx) htx)
          (tilesIn_pos (levelSize_pos hh ly) hty)))

end Tiles

end Exr
