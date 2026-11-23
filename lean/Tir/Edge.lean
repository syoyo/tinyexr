/-
  TinyEXR - Lean 4 model of the tir edge mapping / window folding.

  Mirrors the integer core of `tools/resize/src/tir_table.c`:
  `edge_map`, `ifloor_div`, `window_fold`, `ar_window` and the mapped
  min/max bound helper. These are the parts of table construction whose
  correctness is pure index arithmetic (no libm), so everything here is
  proved over `Int`/`Nat`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tir.Geometry

namespace Tir

set_option linter.unusedVariables false

/-- if-then-else rewrites without the deprecated `if_pos`/`if_neg`
  (the lake build promotes deprecation warnings to errors). -/
theorem itePos {c : Prop} [inst : Decidable c] (h : c) {α : Sort u} {t e : α} :
    (if c then t else e) = t := by simp [h]

theorem iteNeg {c : Prop} [inst : Decidable c] (h : ¬c) {α : Sort u} {t e : α} :
    (if c then t else e) = e := by simp [h]

/-- `edge_map`: map an out-of-range source index into `[0, n)`. Mirrors the
  C function including its early `n == 1` return and the in-range identity
  fast path. `Int.emod` is the C `j % n; if (j < 0) j += n;` idiom. -/
def edgeMap (j : Int) (n : Nat) (m : Edge) : Nat :=
  if n ≤ 1 then 0
  else if 0 ≤ j ∧ j < (n : Int) then j.toNat
  else
    match m with
    | .clamp => if j < 0 then 0 else n - 1
    | .wrap => (j % (n : Int)).toNat
    | .reflect =>
        let p : Int := 2 * (n : Int) - 2
        let r := j % p
        if r < (n : Int) then r.toNat else (p - r).toNat

/-- Clamp form: the in-range check of `edgeMap` is what the clamp formula
  already computes. -/
theorem edgeMap_clamp_eq {j : Int} {n : Nat} (hn : 0 < n) :
    edgeMap j n .clamp = if j < 0 then 0 else if j < (n : Int) then j.toNat else n - 1 := by
  unfold edgeMap
  change (if n ≤ 1 then 0
          else if 0 ≤ j ∧ j < (n : Int) then j.toNat
          else if j < 0 then 0 else n - 1) = _
  by_cases hn1 : n ≤ 1
  · have h1 : n = 1 := by omega
    subst h1
    rw [itePos (show (1 : Nat) ≤ 1 by omega)]
    by_cases hneg : j < 0
    · rw [itePos hneg]
    · rw [iteNeg hneg]
      by_cases hin : j < ((1 : Nat) : Int)
      · rw [itePos hin]
        have hz : j = 0 := by omega
        subst hz
        rfl
      · rw [iteNeg hin]
  · rw [iteNeg hn1]
    by_cases hin : 0 ≤ j ∧ j < (n : Int)
    · rw [itePos hin]
      have h1 : ¬ j < 0 := by omega
      rw [iteNeg h1, itePos hin.2]
    · rw [iteNeg hin]
      by_cases hneg : j < 0
      · rw [itePos hneg, itePos hneg]
      · have hge : (n : Int) ≤ j := by omega
        have h1 : ¬ j < (n : Int) := by omega
        simp only [iteNeg hneg, iteNeg h1]

/-- Wrap form: the C `%` + fixup is exactly `Int.emod`. -/
theorem edgeMap_wrap_eq {j : Int} {n : Nat} (hn : 0 < n) :
    edgeMap j n .wrap = (j % (n : Int)).toNat := by
  unfold edgeMap
  change (if n ≤ 1 then 0
          else if 0 ≤ j ∧ j < (n : Int) then j.toNat
          else (j % (n : Int)).toNat) = _
  by_cases hn1 : n ≤ 1
  · have h1 : n = 1 := by omega
    subst h1
    rw [itePos (show (1 : Nat) ≤ 1 by omega)]
    have hmod : j % ((1 : Nat) : Int) = 0 := by simp
    rw [hmod]
    rfl
  · rw [iteNeg hn1]
    by_cases hin : 0 ≤ j ∧ j < (n : Int)
    · rw [itePos hin]
      have hmod : j % (n : Int) = j := Int.emod_eq_of_lt hin.1 hin.2
      rw [hmod]
    · rw [iteNeg hin]

/-- Reflect form: the C period `p = 2n-2` fold. -/
theorem edgeMap_reflect_eq {j : Int} {n : Nat} (hn : 1 < n) :
    edgeMap j n .reflect =
      (let p : Int := 2 * (n : Int) - 2
       let r := j % p
       if r < (n : Int) then r.toNat else (p - r).toNat) := by
  unfold edgeMap
  change (if n ≤ 1 then 0
          else if 0 ≤ j ∧ j < (n : Int) then j.toNat
          else (let p : Int := 2 * (n : Int) - 2
                let r := j % p
                if r < (n : Int) then r.toNat else (p - r).toNat)) = _
  have hn1 : ¬ n ≤ 1 := by omega
  rw [iteNeg hn1]
  by_cases hin : 0 ≤ j ∧ j < (n : Int)
  · rw [itePos hin]
    have hp : (0 : Int) < 2 * (n : Int) - 2 := by omega
    have hjd : j < 2 * (n : Int) - 2 := by omega
    have hmod : j % (2 * (n : Int) - 2) = j := Int.emod_eq_of_lt hin.1 hjd
    simp only [hmod, itePos hin.2]
  · rw [iteNeg hin]

/-- Every mapped index is inside the axis. -/
theorem edgeMap_lt {j : Int} {n : Nat} (m : Edge) (hn : 0 < n) : edgeMap j n m < n := by
  cases m with
  | clamp =>
      rw [edgeMap_clamp_eq hn]
      by_cases hneg : j < 0
      · rw [itePos hneg]
        omega
      · rw [iteNeg hneg]
        by_cases hin : j < (n : Int)
        · rw [itePos hin]
          exact (Int.toNat_lt (by omega)).mpr hin
        · rw [iteNeg hin]
          omega
  | reflect =>
      by_cases hn2 : 1 < n
      · rw [edgeMap_reflect_eq hn2]
        dsimp only
        have hp : (0 : Int) < 2 * (n : Int) - 2 := by omega
        have hr : j % (2 * (n : Int) - 2) < 2 * (n : Int) - 2 := Int.emod_lt_of_pos _ hp
        have hr0 : 0 ≤ j % (2 * (n : Int) - 2) := Int.emod_nonneg _ (by omega)
        by_cases hin : j % (2 * (n : Int) - 2) < (n : Int)
        · rw [itePos hin]
          exact (Int.toNat_lt hr0).mpr hin
        · rw [iteNeg hin]
          exact (Int.toNat_lt (by omega)).mpr (by omega)
      · have h1 : n = 1 := by omega
        subst h1
        simp [edgeMap]
  | wrap =>
      rw [edgeMap_wrap_eq hn]
      have h0 : 0 ≤ j % (n : Int) := Int.emod_nonneg _ (by omega)
      exact (Int.toNat_lt h0).mpr (Int.emod_lt_of_pos _ (by omega))

/-- A mapped index is a valid source index (as an `Int`). -/
theorem edgeMap_lt' {j : Int} {n : Nat} (m : Edge) (hn : 0 < n) :
    (edgeMap j n m : Int) < (n : Int) := by
  exact_mod_cast edgeMap_lt m hn

/-- In-range indices map to themselves. -/
theorem edgeMap_eq_self {j : Int} {n : Nat} (m : Edge)
    (h0 : 0 ≤ j) (h1 : j < (n : Int)) : edgeMap j n m = j.toNat := by
  have hn : 0 < n := by omega
  unfold edgeMap
  by_cases hn1 : n ≤ 1
  · have h1n : n = 1 := by omega
    subst h1n
    have hz : j = 0 := by omega
    subst hz
    rfl
  · rw [iteNeg hn1, itePos ⟨h0, h1⟩]

/-- Wrap has period `n`. -/
theorem edgeMap_wrap_period (j : Int) (n : Nat) (hn : 0 < n) :
    edgeMap (j + (n : Int)) n .wrap = edgeMap j n .wrap := by
  rw [edgeMap_wrap_eq hn, edgeMap_wrap_eq hn]
  have : (j + (n : Int)) % (n : Int) = j % (n : Int) := Int.add_emod_right j (n : Int)
  rw [this]

/-- Reflect has period `2n-2`. -/
theorem edgeMap_reflect_period (j : Int) (n : Nat) (hn : 1 < n) :
    edgeMap (j + (2 * (n : Int) - 2)) n .reflect = edgeMap j n .reflect := by
  rw [edgeMap_reflect_eq hn, edgeMap_reflect_eq hn]
  dsimp only
  have hp : (0 : Int) < 2 * (n : Int) - 2 := by omega
  have hmod : (j + (2 * (n : Int) - 2)) % (2 * (n : Int) - 2) = j % (2 * (n : Int) - 2) :=
    Int.add_emod_right j (2 * (n : Int) - 2)
  rw [hmod]

/-- C `ifloor_div` for positive divisors. Lean's `Int` division is already
  Euclidean (= floor for a positive divisor), so the C sign fixup is the
  identity on this domain. -/
def ifloorDiv (a : Int) (b : Nat) : Int := a / (b : Int)

/-- Floor division is translation-equivariant by whole divisors. -/
theorem ifloorDiv_add (a : Int) (b : Nat) (hb : 0 < b) :
    ifloorDiv (a + (b : Int)) b = ifloorDiv a b + 1 := by
  unfold ifloorDiv
  have hb' : (b : Int) ≠ 0 := by omega
  have h2 := Int.add_mul_ediv_left a (b := (b : Int)) 1 hb'
  simpa [Int.mul_one] using h2

/-- The floor-division quotient never overshoots. -/
theorem ifloorDiv_mul_le (a : Int) (b : Nat) (hb : 0 < b) :
    ifloorDiv a b * (b : Int) ≤ a := by
  unfold ifloorDiv
  exact Int.ediv_mul_le a (by omega)

/-- The floor-division quotient is tight: `a < (q+1)*b`. -/
theorem lt_ifloorDiv_add_one_mul (a : Int) (b : Nat) (hb : 0 < b) :
    a < (ifloorDiv a b + 1) * (b : Int) := by
  unfold ifloorDiv
  exact Int.lt_ediv_add_one_mul_self a (by omega)

/-- The remainder `a - floorDiv a b * b` lies in `[0, b)`. -/
theorem ifloorDiv_sub_bounds (a : Int) (b : Nat) (hb : 0 < b) :
    0 ≤ a - ifloorDiv a b * (b : Int) ∧ a - ifloorDiv a b * (b : Int) < (b : Int) := by
  have hle := ifloorDiv_mul_le a b hb
  have hlt := lt_ifloorDiv_add_one_mul a b hb
  have hlt' : a < ifloorDiv a b * (b : Int) + (b : Int) := by
    rwa [Int.add_mul, Int.one_mul] at hlt
  constructor <;> omega

/-- Mapped min/max scan over `k` consecutive raw indices. -/
def mappedBounds (s : Nat) (m : Edge) (lo : Int) : Nat → Int × Int
  | 0 => ((s : Int), -1)
  | k + 1 =>
      let p := mappedBounds s m lo k
      let v : Int := (edgeMap (lo + (k : Int)) s m : Int)
      (min p.1 v, max p.2 v)

/-- The scanned min/max is a non-empty in-bounds interval whenever at least
  one index was scanned. -/
theorem mappedBounds_bounds {s : Nat} {m : Edge} {lo : Int} :
    ∀ {k : Nat}, 0 < k → 0 < s →
      0 ≤ (mappedBounds s m lo k).1 ∧
      (mappedBounds s m lo k).1 ≤ (mappedBounds s m lo k).2 ∧
      (mappedBounds s m lo k).2 < (s : Int)
  | 0, hk, _ => by omega
  | k + 1, _, hs => by
      have hv : 0 ≤ (edgeMap (lo + (k : Int)) s m : Int) ∧
                 (edgeMap (lo + (k : Int)) s m : Int) < (s : Int) :=
        ⟨by omega, edgeMap_lt' m hs⟩
      by_cases hk : k = 0
      · subst hk
        simp only [mappedBounds]
        refine ⟨?_, Int.le_trans (Int.min_le_right _ _) (Int.le_max_right _ _), ?_⟩
        · rw [Int.le_min]; exact ⟨by omega, hv.1⟩
        · rw [Int.max_lt]; exact ⟨by omega, hv.2⟩
      · obtain ⟨h1, h2, h3⟩ :=
          mappedBounds_bounds (s := s) (m := m) (lo := lo) (k := k) (by omega) hs
        simp only [mappedBounds]
        refine ⟨?_, Int.le_trans (Int.min_le_right _ _) (Int.le_max_right _ _), ?_⟩
        · rw [Int.le_min]; exact ⟨h1, hv.1⟩
        · rw [Int.max_lt]; exact ⟨h3, hv.2⟩

/-- Folded fast run: mapped window becomes one contiguous in-bounds run. -/
structure Fold where
  runLo : Int
  runHi : Int
  deriving Repr, DecidableEq

/-- `window_fold`: classify a raw window `[lo, lo+n)` as a contiguous run
  (`some`) or a wrap exception (`none`), mirroring the C function. -/
def windowFold (s : Nat) (m : Edge) (lo : Int) (n : Nat) : Option Fold :=
  let hi := lo + (n : Int) - 1
  if 0 ≤ lo ∧ hi < (s : Int) then
    some ⟨lo, hi⟩
  else if m = .wrap then
    if s ≤ n then some ⟨0, (s : Int) - 1⟩
    else if ifloorDiv lo s = ifloorDiv hi s then
      let base := ifloorDiv lo s * (s : Int)
      some ⟨lo - base, hi - base⟩
    else none
  else
    let b := mappedBounds s m lo n
    some ⟨b.1, b.2⟩

/-- A folded run is a non-empty in-bounds interval. -/
theorem windowFold_bounds {s : Nat} {m : Edge} {lo : Int} {n : Nat} {f : Fold}
    (hs : 0 < s) (hn : 0 < n) (h : windowFold s m lo n = some f) :
    0 ≤ f.runLo ∧ f.runLo ≤ f.runHi ∧ f.runHi < (s : Int) := by
  obtain ⟨flo, fhi⟩ := f
  unfold windowFold at h
  dsimp only at h
  by_cases h1 : 0 ≤ lo ∧ lo + (n : Int) - 1 < (s : Int)
  · rw [itePos h1] at h
    simp only [Option.some.injEq, Fold.mk.injEq] at h
    obtain ⟨hlo, hhi⟩ := h
    subst flo
    subst fhi
    show 0 ≤ lo ∧ lo ≤ lo + (n : Int) - 1 ∧ lo + (n : Int) - 1 < (s : Int)
    exact ⟨h1.1, by omega, h1.2⟩
  · rw [iteNeg h1] at h
    by_cases hm : m = .wrap
    · subst hm
      rw [itePos rfl] at h
      by_cases h2 : s ≤ n
      · rw [itePos h2] at h
        simp only [Option.some.injEq, Fold.mk.injEq] at h
        obtain ⟨hlo, hhi⟩ := h
        subst flo
        subst fhi
        show 0 ≤ (0 : Int) ∧ (0 : Int) ≤ (s : Int) - 1 ∧ (s : Int) - 1 < (s : Int)
        exact ⟨by omega, by omega, by omega⟩
      · rw [iteNeg h2] at h
        by_cases h3 : ifloorDiv lo s = ifloorDiv (lo + (n : Int) - 1) s
        · rw [itePos h3] at h
          simp only [Option.some.injEq, Fold.mk.injEq] at h
          obtain ⟨hlo, hhi⟩ := h
          subst flo
          subst fhi
          show 0 ≤ lo - ifloorDiv lo s * (s : Int) ∧
            lo - ifloorDiv lo s * (s : Int) ≤
              lo + (n : Int) - 1 - ifloorDiv lo s * (s : Int) ∧
            lo + (n : Int) - 1 - ifloorDiv lo s * (s : Int) < (s : Int)
          have hb := ifloorDiv_sub_bounds lo s hs
          have hb2 := ifloorDiv_sub_bounds (lo + (n : Int) - 1) s hs
          refine ⟨by omega, by omega, ?_⟩
          have : lo + (n : Int) - 1 - ifloorDiv lo s * (s : Int) < (s : Int) := by
            rw [h3]
            exact hb2.2
          omega
        · rw [iteNeg h3] at h
          exact absurd h (by simp)
    · rw [iteNeg hm] at h
      simp only [Option.some.injEq, Fold.mk.injEq] at h
      obtain ⟨hlo, hhi⟩ := h
      subst flo
      subst fhi
      show 0 ≤ (mappedBounds s m lo n).1 ∧
        (mappedBounds s m lo n).1 ≤ (mappedBounds s m lo n).2 ∧
        (mappedBounds s m lo n).2 < (s : Int)
      exact mappedBounds_bounds hn hs

/-- Anti-ringing footprint: the mapped run of the reduced window. Always a
  non-empty in-bounds interval; the C `if (mx < mn) { mn = 0; mx = 0; }`
  fallback cannot be reached with `s ≥ 1`, `k ≥ 1`. -/
def arWindow (s : Nat) (m : Edge) (lo : Int) (k : Nat) : Int × Int :=
  mappedBounds s m lo k

theorem arWindow_bounds {s : Nat} {m : Edge} {lo : Int} {k : Nat}
    (hs : 0 < s) (hk : 0 < k) :
    0 ≤ (arWindow s m lo k).1 ∧
    (arWindow s m lo k).1 ≤ (arWindow s m lo k).2 ∧
    (arWindow s m lo k).2 < (s : Int) :=
  mappedBounds_bounds hk hs

/-- The dead anti-ringing fallback: with a non-empty scan the min is already
  at most the max, so the C `mx < mn` repair branch never fires. -/
theorem arWindow_fallback_unreachable {s : Nat} {m : Edge} {lo : Int} {k : Nat}
    (hs : 0 < s) (hk : 0 < k) :
    ¬ ((arWindow s m lo k).2 < (arWindow s m lo k).1) := by
  have := arWindow_bounds (m := m) (lo := lo) (k := k) hs hk
  omega

/-- Intersecting a mapped run with the filter run keeps it a valid interval,
  provided the two runs actually overlap (they do in `tir__axis_fill`: the
  anti-ringing window is the reduced mapped window and the filter run is the
  mapped full window). -/
theorem intersect_bounds {alo ahi flo fhi : Int} {s : Nat}
    (ha : 0 ≤ alo ∧ alo ≤ ahi ∧ ahi < (s : Int))
    (hf : 0 ≤ flo ∧ flo ≤ fhi ∧ fhi < (s : Int))
    (hov : alo ≤ fhi ∧ flo ≤ ahi) :
    0 ≤ max alo flo ∧ max alo flo ≤ min ahi fhi ∧ min ahi fhi < (s : Int) := by
  constructor
  · exact Int.le_trans ha.1 (Int.le_max_left _ _)
  constructor
  · rw [Int.le_min]
    constructor
    · rw [Int.max_le]; exact ⟨ha.2.1, hov.2⟩
    · rw [Int.max_le]; exact ⟨hov.1, hf.2.1⟩
  · exact Int.lt_of_le_of_lt (Int.min_le_left _ _) ha.2.2

end Tir
