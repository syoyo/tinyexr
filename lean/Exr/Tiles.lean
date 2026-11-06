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

/-- Tiles of one resolution level, with independent x/y level indices (RIPMAP). -/
def levelTiles2 (up : TypedAttr.RoundingMode) (tw th w h lx ly : Nat) : Nat :=
  tilesIn (levelSize up w lx) tw * tilesIn (levelSize up h ly) th

theorem levelTiles2_pos (up : TypedAttr.RoundingMode) {tw th w h lx ly : Nat}
    (hw : 1 ≤ w) (hh : 1 ≤ h) (htw : 1 ≤ tw) (hth : 1 ≤ th) :
    0 < levelTiles2 up tw th w h lx ly := by
  unfold levelTiles2
  exact Nat.mul_pos (tilesIn_pos (levelSize_pos hw lx) htw)
    (tilesIn_pos (levelSize_pos hh ly) hth)

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
    sumRange (numLevels up h) (fun ly =>
      sumRange (numLevels up w) (fun lx =>
        levelTiles2 up tx ty w h lx ly))

theorem tiledChunks_pos (mode : TypedAttr.LevelMode) (up : TypedAttr.RoundingMode) {tx ty w h : Nat}
    (htx : 1 ≤ tx) (hty : 1 ≤ ty) (hw : 1 ≤ w) (hh : 1 ≤ h) :
    0 < tiledChunks mode up tx ty w h := by
  unfold tiledChunks
  split
  · exact Nat.mul_pos (tilesIn_pos hw htx) (tilesIn_pos hh hty)
  · exact sumRange_pos (mipmapLevelCount_pos up w h)
      (fun l => levelTiles_pos up hw hh htx hty l)
  · exact sumRange_pos (numLevels_pos up h)
      (fun ly => sumRange_pos (numLevels_pos up w)
        (fun lx => Nat.mul_pos
          (tilesIn_pos (levelSize_pos hw lx) htx)
          (tilesIn_pos (levelSize_pos hh ly) hty)))

/-! ### Tile index ordering (offset-table order)

OpenEXR's reader computes the offset-table index of a tile as a prefix sum over
resolution levels (and, for RIPMAP, over y-levels then x-levels). The model
below mirrors `tile_index()` in `src/exr_reader.c`; the lemmas show the index
stays inside the part's chunk range, so the reader can never index the offset
table out of bounds. -/

/-- Sum of the tile counts of levels `0 .. l-1` (the offset-table prefix). -/
def prefixTiles (up : TypedAttr.RoundingMode) (tw th w h l : Nat) : Nat :=
  sumRange l (fun i => levelTiles up tw th w h i)

/-- One RIPMAP row: all x-levels at a fixed y-level. -/
def rowTiles (up : TypedAttr.RoundingMode) (tw th w h ly : Nat) : Nat :=
  sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly)

/-- Offset-table index of a tile, matching the C reader's `tile_index()`.
    `tx`/`ty` are tile indices within the level, `lx`/`ly` are level indices;
    `tw`/`th` are the tile dimensions. -/
def tileIndex : TypedAttr.LevelMode → TypedAttr.RoundingMode →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | .oneLevel, _, tw, _, w, _, tx, ty, _, _ => ty * tilesIn w tw + tx
  | .mipmap, up, tw, th, w, h, tx, ty, lx, _ =>
      prefixTiles up tw th w h lx + ty * tilesIn (levelSize up w lx) tw + tx
  | .ripmap, up, tw, th, w, h, tx, ty, lx, ly =>
      sumRange ly (fun yy => rowTiles up tw th w h yy)
        + sumRange lx (fun xx => levelTiles2 up tw th w h xx ly)
        + ty * tilesIn (levelSize up w lx) tw + tx

theorem sumRange_succ (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = sumRange n f + f n := by
  unfold sumRange
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem sumRange_le_of_le {f : Nat → Nat} {n m : Nat} (h : n ≤ m) :
    sumRange n f ≤ sumRange m f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    have : n + (k + 1) = (n + k) + 1 := by omega
    rw [this, sumRange_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem sumRange_lt_succ {f : Nat → Nat} (hf : ∀ i, 0 < f i) (n : Nat) :
    sumRange n f < sumRange (n + 1) f := by
  rw [sumRange_succ]
  have := hf n
  omega

/-- A valid tile position `(tx, ty)` is below the level's tile count. -/
theorem tileOffset_lt {nxt nyt tx ty : Nat} (_hnxt : 0 < nxt)
    (htx : tx < nxt) (hty : ty < nyt) :
    ty * nxt + tx < nxt * nyt := by
  have h1 : ty * nxt + tx < (ty + 1) * nxt := by
    rw [Nat.succ_mul]; omega
  calc ty * nxt + tx < (ty + 1) * nxt := h1
    _ = nxt * (ty + 1) := Nat.mul_comm _ _
    _ ≤ nxt * nyt := Nat.mul_le_mul_left nxt (by omega)

/-- The tile index of a `ONE_LEVEL` part is below the part's chunk count. -/
theorem tileIndex_oneLevel_lt {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat}
    (htw : 1 ≤ tw) (_hth : 1 ≤ th)
    (hw : 1 ≤ w) (_hh : 1 ≤ h)
    (hx : tx < tilesIn w tw) (hy : ty < tilesIn h th) :
    tileIndex .oneLevel up tw th w h tx ty lx ly <
      tiledChunks .oneLevel up tw th w h := by
  unfold tileIndex tiledChunks
  exact tileOffset_lt (tilesIn_pos hw htw) hx hy

/-- The tile index of a `MIPMAP` part is below the part's chunk count. -/
theorem tileIndex_mipmap_lt {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat}
    (htw : 1 ≤ tw) (_hth : 1 ≤ th) (hw : 1 ≤ w) (_hh : 1 ≤ h)
    (hx : tx < tilesIn (levelSize up w lx) tw)
    (hy : ty < tilesIn (levelSize up h lx) th)
    (hlx : lx < mipmapLevelCount up w h) :
    tileIndex .mipmap up tw th w h tx ty lx ly <
      tiledChunks .mipmap up tw th w h := by
  unfold tileIndex tiledChunks prefixTiles
  have hq : ty * tilesIn (levelSize up w lx) tw + tx < levelTiles up tw th w h lx := by
    unfold levelTiles
    exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx) htw) hx hy
  have hsucc : sumRange lx (fun i => levelTiles up tw th w h i) +
      levelTiles up tw th w h lx =
      sumRange (lx + 1) (fun i => levelTiles up tw th w h i) := by
    rw [sumRange_succ]
  have hle : sumRange (lx + 1) (fun i => levelTiles up tw th w h i) ≤
      sumRange (mipmapLevelCount up w h) (fun i => levelTiles up tw th w h i) :=
    sumRange_le_of_le (by omega)
  calc sumRange lx (fun i => levelTiles up tw th w h i) +
        ty * tilesIn (levelSize up w lx) tw + tx
      = sumRange lx (fun i => levelTiles up tw th w h i) +
          (ty * tilesIn (levelSize up w lx) tw + tx) := by rw [Nat.add_assoc]
    _ < sumRange lx (fun i => levelTiles up tw th w h i) +
          levelTiles up tw th w h lx := by omega
    _ = sumRange (lx + 1) (fun i => levelTiles up tw th w h i) := hsucc
    _ ≤ sumRange (mipmapLevelCount up w h) (fun i => levelTiles up tw th w h i) := hle

/-- The prefix sum is strictly increasing in the level index. -/
theorem prefixTiles_lt_of_lt (up : TypedAttr.RoundingMode) (tw th w h l1 l2 : Nat)
    (htw : 1 ≤ tw) (hth : 1 ≤ th) (hw : 1 ≤ w) (hh : 1 ≤ h) (hl : l1 < l2) :
    prefixTiles up tw th w h l1 < prefixTiles up tw th w h l2 := by
  have hstep : prefixTiles up tw th w h l1 < prefixTiles up tw th w h (l1 + 1) := by
    unfold prefixTiles
    exact sumRange_lt_succ (fun i => levelTiles_pos up hw hh htw hth i) l1
  have hle : prefixTiles up tw th w h (l1 + 1) ≤ prefixTiles up tw th w h l2 := by
    unfold prefixTiles
    exact sumRange_le_of_le (by omega)
  exact lt_of_lt_of_le hstep hle

theorem tileIndex_mipmap_ge_prefix {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat} :
    prefixTiles up tw th w h lx ≤
      tileIndex .mipmap up tw th w h tx ty lx ly := by
  show prefixTiles up tw th w h lx ≤
    prefixTiles up tw th w h lx + ty * tilesIn (levelSize up w lx) tw + tx
  omega

theorem tileIndex_mipmap_lt_prefix {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat}
    (htw : 1 ≤ tw) (hw : 1 ≤ w)
    (hx : tx < tilesIn (levelSize up w lx) tw)
    (hy : ty < tilesIn (levelSize up h lx) th) :
    tileIndex .mipmap up tw th w h tx ty lx ly < prefixTiles up tw th w h (lx + 1) := by
  unfold tileIndex prefixTiles
  have hq : ty * tilesIn (levelSize up w lx) tw + tx < levelTiles up tw th w h lx := by
    unfold levelTiles
    exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx) htw) hx hy
  have hsucc : sumRange lx (fun i => levelTiles up tw th w h i) +
      levelTiles up tw th w h lx =
      sumRange (lx + 1) (fun i => levelTiles up tw th w h i) := by
    rw [sumRange_succ]
  calc sumRange lx (fun i => levelTiles up tw th w h i) +
        ty * tilesIn (levelSize up w lx) tw + tx
      = sumRange lx (fun i => levelTiles up tw th w h i) +
          (ty * tilesIn (levelSize up w lx) tw + tx) := by rw [Nat.add_assoc]
    _ < sumRange lx (fun i => levelTiles up tw th w h i) +
          levelTiles up tw th w h lx := by omega
    _ = sumRange (lx + 1) (fun i => levelTiles up tw th w h i) := hsucc

/-- A `ONE_LEVEL` tile index determines the tile position. -/
theorem tileIndex_oneLevel_injective {up : TypedAttr.RoundingMode} {tw th w h tx1 ty1 tx2 ty2 lx ly : Nat}
    (hw : 1 ≤ w) (htw : 1 ≤ tw)
    (hx1 : tx1 < tilesIn w tw) (hx2 : tx2 < tilesIn w tw)
    (hidx : tileIndex .oneLevel up tw th w h tx1 ty1 lx ly =
         tileIndex .oneLevel up tw th w h tx2 ty2 lx ly) :
    tx1 = tx2 ∧ ty1 = ty2 := by
  have hn : 0 < tilesIn w tw := tilesIn_pos hw htw
  simp only [tileIndex] at hidx
  have hq : ty1 * tilesIn w tw + tx1 = ty2 * tilesIn w tw + tx2 := by omega
  constructor
  · have e1 : (ty1 * tilesIn w tw + tx1) % tilesIn w tw = tx1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx1]
    have e2 : (ty2 * tilesIn w tw + tx2) % tilesIn w tw = tx2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx2]
    rw [← e1, ← e2, hq]
  · have d1 : (ty1 * tilesIn w tw + tx1) / tilesIn w tw = ty1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right tx1 ty1 hn, Nat.div_eq_of_lt hx1, Nat.zero_add]
    have d2 : (ty2 * tilesIn w tw + tx2) / tilesIn w tw = ty2 := by
      rw [Nat.add_comm, Nat.add_mul_div_right tx2 ty2 hn, Nat.div_eq_of_lt hx2, Nat.zero_add]
    rw [← d1, ← d2, hq]

/-- A `MIPMAP` tile index determines the tile position and the level. -/
theorem tileIndex_mipmap_injective {up : TypedAttr.RoundingMode}
    {tw th w h tx1 ty1 tx2 ty2 lx1 lx2 : Nat}
    (htw : 1 ≤ tw) (hth : 1 ≤ th) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (hx1 : tx1 < tilesIn (levelSize up w lx1) tw)
    (hy1 : ty1 < tilesIn (levelSize up h lx1) th)
    (hx2 : tx2 < tilesIn (levelSize up w lx2) tw)
    (hy2 : ty2 < tilesIn (levelSize up h lx2) th)
    (hidx : tileIndex .mipmap up tw th w h tx1 ty1 lx1 lx1 =
         tileIndex .mipmap up tw th w h tx2 ty2 lx2 lx2) :
    tx1 = tx2 ∧ ty1 = ty2 ∧ lx1 = lx2 := by
  have hlx : lx1 = lx2 := by
    rcases Nat.lt_trichotomy lx1 lx2 with hlt | heq | hgt
    · exfalso
      have hP := prefixTiles_lt_of_lt up tw th w h lx1 lx2 htw hth hw hh hlt
      have hstep : prefixTiles up tw th w h (lx1 + 1) ≤
          prefixTiles up tw th w h lx2 := by
        unfold prefixTiles
        exact sumRange_le_of_le (by omega)
      have hi1 := tileIndex_mipmap_lt_prefix (up := up) htw hw hx1 hy1 (lx := lx1) (ly := lx1)
      have hi2 := tileIndex_mipmap_ge_prefix (up := up) (tw := tw) (th := th) (w := w) (h := h)
        (tx := tx2) (ty := ty2) (lx := lx2) (ly := lx2)
      omega
    · exact heq
    · exfalso
      have hP := prefixTiles_lt_of_lt up tw th w h lx2 lx1 htw hth hw hh hgt
      have hstep : prefixTiles up tw th w h (lx2 + 1) ≤
          prefixTiles up tw th w h lx1 := by
        unfold prefixTiles
        exact sumRange_le_of_le (by omega)
      have hi2 := tileIndex_mipmap_lt_prefix (up := up) htw hw hx2 hy2 (lx := lx2) (ly := lx2)
      have hi1 := tileIndex_mipmap_ge_prefix (up := up) (tw := tw) (th := th) (w := w) (h := h)
        (tx := tx1) (ty := ty1) (lx := lx1) (ly := lx1)
      omega
  subst hlx
  have hn : 0 < tilesIn (levelSize up w lx1) tw :=
    tilesIn_pos (levelSize_pos hw lx1) htw
  simp only [tileIndex] at hidx
  have hq : ty1 * tilesIn (levelSize up w lx1) tw + tx1 =
      ty2 * tilesIn (levelSize up w lx1) tw + tx2 := by omega
  constructor
  · have e1 : (ty1 * tilesIn (levelSize up w lx1) tw + tx1) %
        tilesIn (levelSize up w lx1) tw = tx1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx1]
    have e2 : (ty2 * tilesIn (levelSize up w lx1) tw + tx2) %
        tilesIn (levelSize up w lx1) tw = tx2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx2]
    rw [← e1, ← e2, hq]
  · constructor
    · have d1 : (ty1 * tilesIn (levelSize up w lx1) tw + tx1) /
          tilesIn (levelSize up w lx1) tw = ty1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right tx1 ty1 hn,
          Nat.div_eq_of_lt hx1, Nat.zero_add]
      have d2 : (ty2 * tilesIn (levelSize up w lx1) tw + tx2) /
          tilesIn (levelSize up w lx1) tw = ty2 := by
        rw [Nat.add_comm, Nat.add_mul_div_right tx2 ty2 hn,
          Nat.div_eq_of_lt hx2, Nat.zero_add]
      rw [← d1, ← d2, hq]
    · rfl

/-- The tile index of a `RIPMAP` part is below the part's chunk count. -/
theorem tileIndex_ripmap_lt {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat}
    (htw : 1 ≤ tw) (_hth : 1 ≤ th) (hw : 1 ≤ w) (_hh : 1 ≤ h)
    (hx : tx < tilesIn (levelSize up w lx) tw)
    (hy : ty < tilesIn (levelSize up h ly) th)
    (hlx : lx < numLevels up w) (hly : ly < numLevels up h) :
    tileIndex .ripmap up tw th w h tx ty lx ly <
      tiledChunks .ripmap up tw th w h := by
  unfold tileIndex tiledChunks rowTiles
  have hq : ty * tilesIn (levelSize up w lx) tw + tx <
      levelTiles2 up tw th w h lx ly := by
    unfold levelTiles2
    exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx) htw) hx hy
  have hcol : sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
      (ty * tilesIn (levelSize up w lx) tw + tx) <
      sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly) := by
    have hsucc : sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
        levelTiles2 up tw th w h lx ly =
        sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) := by
      rw [sumRange_succ]
    have hle : sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) ≤
        sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly) :=
      sumRange_le_of_le (by omega)
    calc sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
          (ty * tilesIn (levelSize up w lx) tw + tx)
        < sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
            levelTiles2 up tw th w h lx ly := by omega
      _ = sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) := hsucc
      _ ≤ sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly) := hle
  have hrow : sumRange ly (fun yy => rowTiles up tw th w h yy) +
      sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly) =
      sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) := by
    rw [sumRange_succ]
    rfl
  have hle : sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) ≤
      sumRange (numLevels up h) (fun yy => rowTiles up tw th w h yy) :=
    sumRange_le_of_le (by omega)
  calc (sumRange ly (fun yy => rowTiles up tw th w h yy) +
        sumRange lx (fun xx => levelTiles2 up tw th w h xx ly)) +
        ty * tilesIn (levelSize up w lx) tw + tx
      = sumRange ly (fun yy => rowTiles up tw th w h yy) +
          (sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
            (ty * tilesIn (levelSize up w lx) tw + tx)) := by omega
    _ < sumRange ly (fun yy => rowTiles up tw th w h yy) +
          sumRange (numLevels up w) (fun xx => levelTiles2 up tw th w h xx ly) := by omega
    _ = sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) := hrow
    _ ≤ sumRange (numLevels up h) (fun yy => rowTiles up tw th w h yy) := hle

/-- The row prefix is below a RIPMAP tile's index. -/
theorem tileIndex_ripmap_ge_row {up : TypedAttr.RoundingMode} {tw th w h tx ty lx ly : Nat} :
    sumRange ly (fun yy => rowTiles up tw th w h yy) ≤
      tileIndex .ripmap up tw th w h tx ty lx ly := by
  show sumRange ly (fun yy => rowTiles up tw th w h yy) ≤
    (sumRange ly (fun yy => rowTiles up tw th w h yy) +
      sumRange lx (fun xx => levelTiles2 up tw th w h xx ly)) +
      ty * tilesIn (levelSize up w lx) tw + tx
  omega

/-- A RIPMAP tile's index stays inside its row (below the next row's prefix). -/
theorem tileIndex_ripmap_lt_rowSucc {up : TypedAttr.RoundingMode}
    {tw th w h tx ty lx ly : Nat}
    (htw : 1 ≤ tw) (hw : 1 ≤ w)
    (hx : tx < tilesIn (levelSize up w lx) tw)
    (hy : ty < tilesIn (levelSize up h ly) th)
    (hlx : lx < numLevels up w) :
    tileIndex .ripmap up tw th w h tx ty lx ly <
      sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) := by
  have hq : ty * tilesIn (levelSize up w lx) tw + tx <
      levelTiles2 up tw th w h lx ly := by
    unfold levelTiles2
    exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx) htw) hx hy
  have hsuccB : sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
      levelTiles2 up tw th w h lx ly =
      sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) := by
    rw [sumRange_succ]
  have hleB : sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) ≤
      rowTiles up tw th w h ly := by
    unfold rowTiles
    exact sumRange_le_of_le (by omega)
  have hsuccA : sumRange ly (fun yy => rowTiles up tw th w h yy) +
      rowTiles up tw th w h ly =
      sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) := by
    rw [sumRange_succ]
  show (sumRange ly (fun yy => rowTiles up tw th w h yy) +
      sumRange lx (fun xx => levelTiles2 up tw th w h xx ly)) +
      ty * tilesIn (levelSize up w lx) tw + tx <
      sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy)
  calc (sumRange ly (fun yy => rowTiles up tw th w h yy) +
        sumRange lx (fun xx => levelTiles2 up tw th w h xx ly)) +
        ty * tilesIn (levelSize up w lx) tw + tx
      = sumRange ly (fun yy => rowTiles up tw th w h yy) +
          (sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
            (ty * tilesIn (levelSize up w lx) tw + tx)) := by omega
    _ < sumRange ly (fun yy => rowTiles up tw th w h yy) +
          (sumRange lx (fun xx => levelTiles2 up tw th w h xx ly) +
            levelTiles2 up tw th w h lx ly) := by omega
    _ = sumRange ly (fun yy => rowTiles up tw th w h yy) +
          sumRange (lx + 1) (fun xx => levelTiles2 up tw th w h xx ly) := by rw [hsuccB]
    _ ≤ sumRange ly (fun yy => rowTiles up tw th w h yy) +
          rowTiles up tw th w h ly := by omega
    _ = sumRange (ly + 1) (fun yy => rowTiles up tw th w h yy) := hsuccA

/-- A `RIPMAP` tile index determines the tile position and both level indices. -/
theorem tileIndex_ripmap_injective {up : TypedAttr.RoundingMode}
    {tw th w h tx1 ty1 tx2 ty2 lx1 ly1 lx2 ly2 : Nat}
    (htw : 1 ≤ tw) (_hth : 1 ≤ th) (hw : 1 ≤ w) (_hh : 1 ≤ h)
    (hx1 : tx1 < tilesIn (levelSize up w lx1) tw)
    (hy1 : ty1 < tilesIn (levelSize up h ly1) th)
    (hx2 : tx2 < tilesIn (levelSize up w lx2) tw)
    (hy2 : ty2 < tilesIn (levelSize up h ly2) th)
    (hlx1 : lx1 < numLevels up w) (_hly1 : ly1 < numLevels up h)
    (hlx2 : lx2 < numLevels up w) (hly2 : ly2 < numLevels up h)
    (hidx : tileIndex .ripmap up tw th w h tx1 ty1 lx1 ly1 =
            tileIndex .ripmap up tw th w h tx2 ty2 lx2 ly2) :
    tx1 = tx2 ∧ ty1 = ty2 ∧ lx1 = lx2 ∧ ly1 = ly2 := by
  have hly : ly1 = ly2 := by
    rcases Nat.lt_trichotomy ly1 ly2 with hlt | heq | hgt
    · exfalso
      have h1 := tileIndex_ripmap_lt_rowSucc (up := up) (tw := tw) (w := w)
        (tx := tx1) (ty := ty1) (lx := lx1) (ly := ly1) htw hw hx1 hy1 hlx1
      have hle : sumRange (ly1 + 1) (fun yy => rowTiles up tw th w h yy) ≤
          sumRange ly2 (fun yy => rowTiles up tw th w h yy) :=
        sumRange_le_of_le (by omega)
      have h2 : sumRange ly2 (fun yy => rowTiles up tw th w h yy) ≤
          tileIndex .ripmap up tw th w h tx2 ty2 lx2 ly2 :=
        tileIndex_ripmap_ge_row
      omega
    · exact heq
    · exfalso
      have h2 := tileIndex_ripmap_lt_rowSucc (up := up) (tw := tw) (w := w)
        (tx := tx2) (ty := ty2) (lx := lx2) (ly := ly2) htw hw hx2 hy2 hlx2
      have hle : sumRange (ly2 + 1) (fun yy => rowTiles up tw th w h yy) ≤
          sumRange ly1 (fun yy => rowTiles up tw th w h yy) :=
        sumRange_le_of_le (by omega)
      have h1 : sumRange ly1 (fun yy => rowTiles up tw th w h yy) ≤
          tileIndex .ripmap up tw th w h tx1 ty1 lx1 ly1 :=
        tileIndex_ripmap_ge_row
      omega
  subst hly
  have hB : sumRange lx1 (fun xx => levelTiles2 up tw th w h xx ly1) +
      (ty1 * tilesIn (levelSize up w lx1) tw + tx1) =
      sumRange lx2 (fun xx => levelTiles2 up tw th w h xx ly1) +
      (ty2 * tilesIn (levelSize up w lx2) tw + tx2) := by
    have h' := hidx
    simp only [tileIndex] at h'
    omega
  have hlx : lx1 = lx2 := by
    rcases Nat.lt_trichotomy lx1 lx2 with hlt | heq | hgt
    · exfalso
      have hq1 : ty1 * tilesIn (levelSize up w lx1) tw + tx1 <
          levelTiles2 up tw th w h lx1 ly1 := by
        unfold levelTiles2
        exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx1) htw) hx1 hy1
      have hsucc : sumRange lx1 (fun xx => levelTiles2 up tw th w h xx ly1) +
          levelTiles2 up tw th w h lx1 ly1 =
          sumRange (lx1 + 1) (fun xx => levelTiles2 up tw th w h xx ly1) := by
        rw [sumRange_succ]
      have hle : sumRange (lx1 + 1) (fun xx => levelTiles2 up tw th w h xx ly1) ≤
          sumRange lx2 (fun xx => levelTiles2 up tw th w h xx ly1) :=
        sumRange_le_of_le (by omega)
      have hge : sumRange lx2 (fun xx => levelTiles2 up tw th w h xx ly1) ≤
          sumRange lx2 (fun xx => levelTiles2 up tw th w h xx ly1) +
            (ty2 * tilesIn (levelSize up w lx2) tw + tx2) := by omega
      omega
    · exact heq
    · exfalso
      have hq2 : ty2 * tilesIn (levelSize up w lx2) tw + tx2 <
          levelTiles2 up tw th w h lx2 ly1 := by
        unfold levelTiles2
        exact tileOffset_lt (tilesIn_pos (levelSize_pos hw lx2) htw) hx2 hy2
      have hsucc : sumRange lx2 (fun xx => levelTiles2 up tw th w h xx ly1) +
          levelTiles2 up tw th w h lx2 ly1 =
          sumRange (lx2 + 1) (fun xx => levelTiles2 up tw th w h xx ly1) := by
        rw [sumRange_succ]
      have hle : sumRange (lx2 + 1) (fun xx => levelTiles2 up tw th w h xx ly1) ≤
          sumRange lx1 (fun xx => levelTiles2 up tw th w h xx ly1) :=
        sumRange_le_of_le (by omega)
      have hge : sumRange lx1 (fun xx => levelTiles2 up tw th w h xx ly1) ≤
          sumRange lx1 (fun xx => levelTiles2 up tw th w h xx ly1) +
            (ty1 * tilesIn (levelSize up w lx1) tw + tx1) := by omega
      omega
  subst hlx
  have hn : 0 < tilesIn (levelSize up w lx1) tw :=
    tilesIn_pos (levelSize_pos hw lx1) htw
  have hq : ty1 * tilesIn (levelSize up w lx1) tw + tx1 =
      ty2 * tilesIn (levelSize up w lx1) tw + tx2 := by omega
  constructor
  · have e1 : (ty1 * tilesIn (levelSize up w lx1) tw + tx1) %
        tilesIn (levelSize up w lx1) tw = tx1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx1]
    have e2 : (ty2 * tilesIn (levelSize up w lx1) tw + tx2) %
        tilesIn (levelSize up w lx1) tw = tx2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx2]
    rw [← e1, ← e2, hq]
  · constructor
    · have d1 : (ty1 * tilesIn (levelSize up w lx1) tw + tx1) /
          tilesIn (levelSize up w lx1) tw = ty1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right tx1 ty1 hn,
          Nat.div_eq_of_lt hx1, Nat.zero_add]
      have d2 : (ty2 * tilesIn (levelSize up w lx1) tw + tx2) /
          tilesIn (levelSize up w lx1) tw = ty2 := by
        rw [Nat.add_comm, Nat.add_mul_div_right tx2 ty2 hn,
          Nat.div_eq_of_lt hx2, Nat.zero_add]
      rw [← d1, ← d2, hq]
    · exact ⟨rfl, rfl⟩

end Tiles

end Exr
