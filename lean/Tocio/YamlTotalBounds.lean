/-
   TinyEXR - remaining-fuel invariant for the total YAML parser.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.YamlTotal

namespace Tocio

set_option linter.unusedVariables false

/-- All three workers return at most the fuel they were given.  The tuple's
third component is the *remaining* fuel (nested-call residuals are discarded),
not a count of parser calls. -/
theorem parseTotal_used_le (fuel : Nat) :
    (∀ (base : Nat) (ls : List YL2) (v : YamlValue) (rem : List YL2) (used : Nat),
        parseValueTotal fuel base ls = some (v, rem, used) → used ≤ fuel) ∧
    (∀ (base : Nat) (ls : List YL2) (acc : List YamlValue)
        (v : YamlValue) (rem : List YL2) (used : Nat),
        parseSeqTotal fuel base ls acc = some (v, rem, used) → used ≤ fuel) ∧
    (∀ (base : Nat) (ls : List YL2) (acc : List (String × YamlValue))
        (v : YamlValue) (rem : List YL2) (used : Nat),
        parseMapTotal fuel base ls acc = some (v, rem, used) → used ≤ fuel) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro base ls v rem used hr
        cases ls with
        | nil =>
            rw [parseValueTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact Nat.le_refl _
        | cons l tail => rw [parseValueTotal.eq_2] at hr; simp at hr
      · intro base ls acc v rem used hr
        cases ls with
        | nil =>
            rw [parseSeqTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact Nat.le_refl _
        | cons l tail =>
            rw [parseSeqTotal.eq_2] at hr
            by_cases h1 : l.indent < base
            · rw [itePos h1] at hr
              have he := someInj hr
              simp only [Prod.mk.injEq] at he
              obtain ⟨e1, e2, e3⟩ := he
              subst e3
              exact Nat.le_refl _
            · rw [iteNeg h1] at hr
              by_cases h2 : l.indent > base
              · rw [itePos h2] at hr
                have he := someInj hr
                simp only [Prod.mk.injEq] at he
                obtain ⟨e1, e2, e3⟩ := he
                subst e3
                exact Nat.le_refl _
              · rw [iteNeg h2] at hr
                by_cases h3 : isSeqItemText l.text = true
                · rw [h3] at hr
                  rw [iteNeg (show ¬((!true) = true) by simp)] at hr
                  simp at hr
                · rw [itePos (show (!isSeqItemText l.text) = true by
                      cases hbb : isSeqItemText l.text with
                      | false => simp
                      | true => exact absurd hbb h3)] at hr
                  have he := someInj hr
                  simp only [Prod.mk.injEq] at he
                  obtain ⟨e1, e2, e3⟩ := he
                  subst e3
                  exact Nat.le_refl _
      · intro base ls acc v rem used hr
        cases ls with
        | nil =>
            rw [parseMapTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact Nat.le_refl _
        | cons l tail =>
            rw [parseMapTotal.eq_2] at hr
            by_cases h1 : l.indent < base
            · rw [itePos h1] at hr
              have he := someInj hr
              simp only [Prod.mk.injEq] at he
              obtain ⟨e1, e2, e3⟩ := he
              subst e3
              exact Nat.le_refl _
            · rw [iteNeg h1] at hr
              by_cases h2 : l.indent > base
              · rw [itePos h2] at hr
                have he := someInj hr
                simp only [Prod.mk.injEq] at he
                obtain ⟨e1, e2, e3⟩ := he
                subst e3
                exact Nat.le_refl _
              · rw [iteNeg h2] at hr
                simp at hr
  | succ n ih =>
      obtain ⟨hV, hS, hM⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro base ls v rem used hr
        cases ls with
        | nil =>
            rw [parseValueTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact by omega
        | cons l tail =>
            rw [parseValueTotal.eq_3] at hr
            by_cases h1 : isSeqItemText l.text = true
            · rw [itePos h1] at hr
              exact Nat.le_trans (hS base (l :: tail) [] v rem used hr) (Nat.le_succ n)
            · rw [iteNeg h1] at hr
              exact Nat.le_trans (hM base (l :: tail) [] v rem used hr) (Nat.le_succ n)
      · intro base ls acc v rem used hr
        cases ls with
        | nil =>
            rw [parseSeqTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact by omega
        | cons l tail =>
            rw [parseSeqTotal.eq_3] at hr
            by_cases h1 : l.indent < base
            · rw [itePos h1] at hr
              have he := someInj hr
              simp only [Prod.mk.injEq] at he
              obtain ⟨e1, e2, e3⟩ := he
              subst e3
              exact by omega
            · rw [iteNeg h1] at hr
              by_cases h2 : l.indent > base
              · rw [itePos h2] at hr
                have he := someInj hr
                simp only [Prod.mk.injEq] at he
                obtain ⟨e1, e2, e3⟩ := he
                subst e3
                exact by omega
              · rw [iteNeg h2] at hr
                by_cases h3 : isSeqItemText l.text = true
                · rw [h3] at hr
                  rw [iteNeg (show ¬((!true) = true) by simp)] at hr
                  rw [optTriple_bind_some] at hr
                  exact Nat.le_trans
                    (hS base tail (YamlValue.str (stripSeqItem l.text) :: acc) v rem used hr)
                    (Nat.le_succ n)
                · rw [itePos (show (!isSeqItemText l.text) = true by
                      cases hbb : isSeqItemText l.text with
                      | false => simp
                      | true => exact absurd hbb h3)] at hr
                  have he := someInj hr
                  simp only [Prod.mk.injEq] at he
                  obtain ⟨e1, e2, e3⟩ := he
                  subst e3
                  exact by omega
      · intro base ls acc v rem used hr
        cases ls with
        | nil =>
            rw [parseMapTotal.eq_1] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e3
            exact by omega
        | cons l tail =>
            rw [parseMapTotal.eq_3] at hr
            by_cases h1 : l.indent < base
            · rw [itePos h1] at hr
              have he := someInj hr
              simp only [Prod.mk.injEq] at he
              obtain ⟨e1, e2, e3⟩ := he
              subst e3
              exact by omega
            · rw [iteNeg h1] at hr
              by_cases h2 : l.indent > base
              · rw [itePos h2] at hr
                have he := someInj hr
                simp only [Prod.mk.injEq] at he
                obtain ⟨e1, e2, e3⟩ := he
                subst e3
                exact by omega
              · rw [iteNeg h2] at hr
                cases hkv : parseKv l.text with
                | none => simp only [hkv] at hr; simp at hr
                | some kv =>
                    simp only [hkv] at hr
                    by_cases h3 : kv.val.isEmpty = true
                    · rw [itePos h3] at hr
                      cases hsub : tail.takeWhile (fun x => x.indent > base) with
                      | nil => rw [hsub] at hr; simp at hr
                      | cons s ss =>
                        rw [hsub] at hr
                        simp [List.head!] at hr
                        cases hv : parseValueTotal n s.indent (s :: ss) with
                        | none => simp only [hv] at hr; simp at hr
                        | some p =>
                            simp only [hv] at hr
                            first
                              | rw [optTriple_bind_some] at hr
                              | rw [optTriple_bind_some2] at hr
                            exact Nat.le_trans
                              (hM base (tail.dropWhile (fun x => x.indent > base))
                                ((kv.key, p.1) :: acc) v rem used hr)
                              (Nat.le_succ n)
                    · rw [iteNeg h3] at hr
                      rw [optTriple_bind_some] at hr
                      exact Nat.le_trans
                        (hM base tail ((kv.key, YamlValue.str kv.val) :: acc) v rem used hr)
                        (Nat.le_succ n)

/-- Entry-point specialization of the remaining-fuel invariant. -/
theorem parseYamlTotalV_used_le (lines : List YL2) (v : YamlValue)
    (rem : List YL2) (used : Nat)
    (h : parseValueTotal yamlEntryFuel 0 lines = some (v, rem, used)) :
    used ≤ yamlEntryFuel :=
  (parseTotal_used_le yamlEntryFuel).1 0 lines v rem used h

end Tocio
