/-
  TinyEXR - Lean 4 model of the tir coefficient-table builder.

  Covers the shape-level parts of `tools/resize/src/tir_table.c` that do not
  depend on libm:

  * the raw window bounds / truncation (`lo`, `hi`, `win_max`) and the
    invariant that a built window has at least one and at most `win_max`
    taps;
  * the zero-tap trim (both ends) and the normalisation step, whose
    algebraic law (`sum = 1`) is proved over `ℚ`;
  * `tir__axis_measure`'s fast/exception classification scan and the
    agreement theorem: a successful measure reports exactly the per-index
    classification that `tir__axis_fill` re-derives, so the two passes
    cannot disagree about the arena layout (the C comment calls that
    disagreement arena corruption).

  Kernel *values* (libm `sin`/`exp`/`sqrt`) are pinned by the C-vs-Lean
  differential gate, not re-derived here.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Mathlib.Tactic
import Tir.Edge

namespace Tir

set_option linter.unusedVariables false

/-! ## Window shape -/

/-- Raw window bounds before trimming: `lo = ceil(center - support)` (or the
  box overlap variant) and `n = hi - lo + 1`, truncated to `win_max`
  (`if (hi - lo + 1 > win_max) hi = lo + win_max - 1;`). -/
structure WinRaw where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- Truncate a raw window to at most `winMax` taps; `hi < lo` is repaired to
  a single tap first, exactly like the C builder. -/
def winTrunc (lo hi : Int) (winMax : Nat) : WinRaw :=
  let hi := if hi < lo then lo else hi
  let hi := if (hi - lo + 1).toNat > winMax then lo + (winMax : Int) - 1 else hi
  ⟨lo, hi⟩

/-- A truncated window has at least one tap when `winMax` is positive. -/
theorem winTrunc_len_ge_one {lo hi : Int} {winMax : Nat} (hw : 0 < winMax) :
    0 < (winTrunc lo hi winMax).hi - (winTrunc lo hi winMax).lo + 1 := by
  unfold winTrunc
  dsimp only
  split
  · omega
  · split
    · omega
    · omega

/-- A truncated window never exceeds `winMax` taps. -/
theorem winTrunc_len_le {lo hi : Int} {winMax : Nat} (hw : 0 < winMax) :
    (winTrunc lo hi winMax).hi - (winTrunc lo hi winMax).lo + 1 ≤ (winMax : Int) := by
  unfold winTrunc
  dsimp only
  split
  · split
    · omega
    · omega
  · split
    · omega
    · omega

/-! ## Trimming zero taps -/

/-- C `fabs(w[i]) <= 1e-10` for f32 coefficients. -/
def smallW (x : Float) : Bool := x.abs ≤ 1e-10

/-- Trim near-zero weights at the front, keeping at least one tap
  (`while (n > 1 && fabs(w[0]) <= 1e-10)`). -/
def trimLeft : List Float → List Float
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if smallW x then trimLeft (y :: rest) else x :: y :: rest

/-- Trim near-zero weights at the back, keeping at least one tap. -/
def trimRight : List Float → List Float :=
  fun l => (trimLeft l.reverse).reverse

/-- Trimming never produces an empty window. -/
theorem trimLeft_pos {l : List Float} (h : l ≠ []) : 0 < (trimLeft l).length := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      cases xs with
      | nil => simp [trimLeft]
      | cons y ys =>
          unfold trimLeft
          split
          · exact ih (by simp)
          · simp

/-- Trimming never produces an empty window (symmetric). -/
theorem trimRight_pos {l : List Float} (h : l ≠ []) : 0 < (trimRight l).length := by
  unfold trimRight
  rw [List.length_reverse]
  apply trimLeft_pos
  intro hrev
  exact (by assumption : l ≠ []) (by simpa using congrArg List.reverse hrev)

/-- Trimming only ever shortens the window. -/
theorem trimLeft_length_le : ∀ l : List Float, (trimLeft l).length ≤ l.length
  | [] => by simp [trimLeft]
  | [_] => by simp [trimLeft]
  | x :: y :: rest => by
      unfold trimLeft
      split
      · have ih := trimLeft_length_le (y :: rest)
        simp only [List.length_cons] at ih ⊢
        omega
      · simp

/-- Trimming only ever shortens the window (symmetric). -/
theorem trimRight_length_le (l : List Float) : (trimRight l).length ≤ l.length := by
  unfold trimRight
  have h := trimLeft_length_le l.reverse
  simpa [List.length_reverse] using h

/-- A window of more than one tap has a non-small first weight after
  trimming (`trimLeft`'s stop condition). -/
theorem trimLeft_head_not_small {l : List Float} (h : 1 < (trimLeft l).length) :
    ∃ x xs, trimLeft l = x :: xs ∧ smallW x = false := by
  induction l with
  | nil => simp [trimLeft] at h
  | cons x xs ih =>
      cases xs with
      | nil => simp [trimLeft] at h
      | cons y ys =>
          unfold trimLeft
          split
          · rename_i hns
            have hns' : smallW x = true := by simpa using hns
            have heq : trimLeft (x :: y :: ys) = trimLeft (y :: ys) := by
              change (if smallW x then trimLeft (y :: ys) else x :: y :: ys) = trimLeft (y :: ys)
              rw [itePos hns']
            rw [heq] at h
            exact ih h
          · rename_i hns
            exact ⟨x, y :: ys, rfl, by simpa using hns⟩

/-! ## Normalisation -/

/-- Normalised weights over `ℚ`: divide by the sum. -/
def normRat (l : List ℚ) (S : ℚ) : List ℚ := l.map (fun x => x / S)

/-- Dividing every weight by the raw sum makes the weights sum to one. -/
theorem sum_map_div (l : List ℚ) (S : ℚ) :
    (l.map (fun x => x / S)).sum = l.sum / S := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.sum_cons, add_div, ih]

/-- Dividing every weight by the raw sum makes the weights sum to one. -/
theorem normRat_sum_one (l : List ℚ) (S : ℚ) (hS : S ≠ 0) (hl : l.sum = S) :
    (normRat l S).sum = 1 := by
  unfold normRat
  rw [sum_map_div, hl, div_self hS]

/-- The zero-sum fallback: a single tap of weight one at the rounded
  centre (`if (sum == 0.0) { lo = c; n = 1; w[0] = 1.0; }`). -/
def zeroSumFallback (c : Int) : WinRaw × List ℚ := (⟨c, c⟩, [1])

theorem zeroSumFallback_sum (c : Int) : (zeroSumFallback c).2.sum = 1 := by
  simp [zeroSumFallback]

/-! ## Measure / fill classification agreement -/

/-- `tir__axis_measure`'s running state. `fastHi = d` means "no suffix
  exception seen yet"; `failed` mirrors the C error return for a fast output
  after a suffix exception. -/
structure Scan where
  fastLo : Nat
  fastHi : Nat
  seenFast : Bool
  failed : Bool
  deriving Repr, DecidableEq

/-- One step of the C measure loop at output index `i`. -/
def scanStep (d : Nat) (st : Scan) (i : Nat) (isFast : Bool) : Scan :=
  if isFast then
    if st.failed then
      { st with seenFast := true }
    else if st.fastHi ≤ i then
      { st with seenFast := true, failed := true }
    else
      { st with seenFast := true }
  else
    { fastLo := if st.seenFast then st.fastLo else i + 1
      fastHi := if st.seenFast && st.fastHi == d then i else st.fastHi
      seenFast := st.seenFast
      failed := st.failed }

/-- The classification pass over the first `k` output indices. -/
def measureScan (d : Nat) (cls : Nat → Bool) : Nat → Scan
  | 0 => ⟨0, d, false, false⟩
  | k + 1 => scanStep d (measureScan d cls k) k (cls k)

/-- The invariant maintained by the measure scan over a processed prefix. -/
def ScanOK (d : Nat) (cls : Nat → Bool) (k : Nat) (st : Scan) : Prop :=
  st.fastLo ≤ k ∧
  st.fastHi ≤ d ∧
  (st.seenFast = false → st.fastHi = d) ∧
  (st.seenFast = false → st.fastLo = k) ∧
  (st.fastHi < d → st.fastHi < k) ∧
  (st.fastLo ≤ st.fastHi ∨ st.failed = true) ∧
  (st.failed = false → ∀ i, i < k → (cls i = false ↔ i < st.fastLo ∨ st.fastHi ≤ i))

/-- The scan maintains `ScanOK`. -/
theorem measureScan_ok (d : Nat) (cls : Nat → Bool) :
    ∀ (k : Nat), k ≤ d → ScanOK d cls k (measureScan d cls k) := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨by simp [measureScan], by simp [measureScan],
        by simp [measureScan], by simp [measureScan], by simp [measureScan],
        by simp [measureScan], ?_⟩
      intro _ i hi
      omega
  | succ k ih =>
      intro hk
      have hkd : k ≤ d := by omega
      have hlt : k < d := by omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih hkd
      rw [measureScan]
      cases hc : cls k with
      | true =>
          have hnewLo : (scanStep d (measureScan d cls k) k true).fastLo =
              (measureScan d cls k).fastLo := by
            by_cases hf : (measureScan d cls k).failed = true <;>
              by_cases hle : (measureScan d cls k).fastHi ≤ k <;>
              simp [scanStep, hf, hle]
          have hnewHi : (scanStep d (measureScan d cls k) k true).fastHi =
              (measureScan d cls k).fastHi := by
            by_cases hf : (measureScan d cls k).failed = true <;>
              by_cases hle : (measureScan d cls k).fastHi ≤ k <;>
              simp [scanStep, hf, hle]
          have hnewSeen : (scanStep d (measureScan d cls k) k true).seenFast = true := by
            by_cases hf : (measureScan d cls k).failed = true <;>
              by_cases hle : (measureScan d cls k).fastHi ≤ k <;>
              simp [scanStep, hf, hle]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hnewLo]; omega
          · rw [hnewHi]; exact h2
          · rw [hnewSeen]; simp
          · rw [hnewSeen]; simp
          · rw [hnewHi]; omega
          · by_cases hfhi : (measureScan d cls k).fastHi ≤ k
            · right
              rw [show (scanStep d (measureScan d cls k) k true).failed = true by
                by_cases hf : (measureScan d cls k).failed = true <;> simp [scanStep, hf, hfhi]]
            · by_cases hf0 : (measureScan d cls k).failed = false
              · left
                rw [hnewLo, hnewHi]
                rcases h6 with hfh | hfd
                · exact hfh
                · rw [hf0] at hfd
                  exact absurd hfd (by simp)
              · right
                have hft : (measureScan d cls k).failed = true := by
                  cases hv : (measureScan d cls k).failed <;> simp_all
                rw [show (scanStep d (measureScan d cls k) k true).failed = true by
                  simp [scanStep, hft]]
          · intro hfail i hi
            have hf0 : (measureScan d cls k).failed = false := by
              by_contra hv
              have hft : (measureScan d cls k).failed = true := by
                cases hv' : (measureScan d cls k).failed <;> simp_all
              have : (scanStep d (measureScan d cls k) k true).failed = true := by
                simp [scanStep, hft]
              simp [this] at hfail
            have hfhi : ¬ (measureScan d cls k).fastHi ≤ k := by
              intro hle
              have : (scanStep d (measureScan d cls k) k true).failed = true := by
                simp [scanStep, hf0, hle]
              simp [this] at hfail
            by_cases hik : i < k
            · have := h7 hf0 i hik
              rw [hnewLo, hnewHi]
              omega
            · have hik' : i = k := by omega
              subst hik'
              rw [hnewLo, hnewHi]
              constructor
              · intro hcontra; rw [hc] at hcontra; contradiction
              · intro hcontra
                omega
      | false =>
          by_cases hseen : (measureScan d cls k).seenFast = true
          · have hseenF : (measureScan d cls k).seenFast = true := hseen
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [scanStep, hseenF]; omega
            · by_cases hfh : (measureScan d cls k).fastHi = d
              · simp [scanStep, hseenF, hfh]; omega
              · simp [scanStep, hseenF, hfh]; omega
            · simp [scanStep, hseenF]
            · simp [scanStep, hseenF]
            · by_cases hfh : (measureScan d cls k).fastHi = d
              · simp [scanStep, hseenF, hfh]
              · simp [scanStep, hseenF, hfh]
                intro hfd
                exact Nat.le_of_lt (h5 (by omega))
            · by_cases hf : (measureScan d cls k).failed = true
              · simp [scanStep, hseenF, hf]
              · have hf' : (measureScan d cls k).failed = false := by
                  cases hv : (measureScan d cls k).failed <;> simp_all
                have hflfh : (measureScan d cls k).fastLo ≤ (measureScan d cls k).fastHi := by
                  rcases h6 with h | h
                  · exact h
                  · rw [hf'] at h; exact absurd h (by simp)
                by_cases hfh : (measureScan d cls k).fastHi = d
                · simp [scanStep, hseenF, hfh]
                  omega
                · simp [scanStep, hseenF, hfh]
                  omega
            · intro hfail i hi
              have hfail' : (measureScan d cls k).failed = false := by
                simpa [scanStep, hc, hseenF] using hfail
              by_cases hfh : (measureScan d cls k).fastHi = d
              · simp [scanStep, hseenF, hfh]
                by_cases hik : i < k
                · have hki : ¬ k ≤ i := by omega
                  have hdi : ¬ d ≤ i := by omega
                  simpa [hfh, hki, hdi] using (h7 hfail' i hik)
                · have hci : cls i = false := by simpa [show i = k by omega] using hc
                  rw [hci]
                  have hik_eq : i = k := by omega
                  rw [hik_eq]
                  simp
              · have hfdlt : (measureScan d cls k).fastHi < d :=
                  Nat.lt_of_le_of_ne h2 hfh
                have hfhlt : (measureScan d cls k).fastHi < k := h5 hfdlt
                simp [scanStep, hseenF, hfh]
                by_cases hik : i < k
                · simpa [hfh] using (h7 hfail' i hik)
                · have hci : cls i = false := by simpa [show i = k by omega] using hc
                  rw [hci]
                  have hik_eq : i = k := by omega
                  rw [hik_eq]
                  simp [Nat.le_of_lt hfhlt]
          · have hseenF : (measureScan d cls k).seenFast = false := by
              cases hv : (measureScan d cls k).seenFast <;> simp_all
            have hfd : (measureScan d cls k).fastHi = d := h3 hseenF
            have hflk : (measureScan d cls k).fastLo = k := h4 hseenF
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [scanStep, hseenF]
            · simp [scanStep, hseenF, hfd]
            · simp [scanStep, hseenF, hfd]
            · simp [scanStep, hseenF]
            · simp [scanStep, hseenF, hfd]
            · simp [scanStep, hseenF, hfd]; omega
            · intro hfail i hi
              have hfail' : (measureScan d cls k).failed = false := by
                simpa [scanStep, hc, hseenF] using hfail
              simp [scanStep, hseenF, hfd]
              by_cases hik : i < k
              case pos =>
                have hci : cls i = false :=
                  (h7 hfail' i hik).mpr (Or.inl (by rw [hflk]; omega))
                rw [hci]
                exact by simp [Nat.le_of_lt hik]
              case neg =>
                have hik' : i = k := by omega
                subst hik'
                simp [hc]

/-- **Measure/fill agreement.** If the measure pass succeeds, then for every
  output index `i < d` the fast/exception classification it recorded
  (`fastLo ≤ i < fastHi`) is exactly the one the fill pass recomputes from
  `window_fold`. The fill pass therefore never takes its fast branch with an
  unset run, and never lands in an exception slot the arena did not size. -/
theorem measureScan_spec {d : Nat} {cls : Nat → Bool}
    (h : (measureScan d cls d).failed = false) :
    ∀ i, i < d →
      (cls i = false ↔ i < (measureScan d cls d).fastLo ∨ (measureScan d cls d).fastHi ≤ i) := by
  have hok := measureScan_ok d cls d (Nat.le_refl d)
  exact hok.2.2.2.2.2.2 h

/-- Count of exceptional (non-fast) outputs in the first `k` indices. -/
def countExc (cls : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => countExc cls k + (if cls k then 0 else 1)

end Tir
