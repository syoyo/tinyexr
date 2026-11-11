/-
  TinyEXR - Lean 4 formalization of a total, depth-bounded YAML parser.

  Fuel-style termination: every recursion site decrements a numeric
  fuel counter (mirroring the C parser's YAML stack cap of 128 and
  the transform-walk cap of 64), making all three workers trivially
  total under `termination_by fuel`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml
import Tocio.YamlParse

namespace Tocio

set_option linter.unusedVariables false

mutual
/-- Sequence height helper (fold-style). -/
def seqHeight : List YamlValue → Nat
  | [] => 0
  | x :: xs => Nat.max x.height (seqHeight xs)

/-- Mapping height helper. -/
def mapHeight : List (String × YamlValue) → Nat
  | [] => 0
  | p :: ps => Nat.max p.2.height (mapHeight ps)

/-- Height of a YAML value. -/
def YamlValue.height (v : YamlValue) : Nat :=
  match v with
  | .null => 1
  | .bool _ => 1
  | .int _ => 1
  | .str _ => 1
  | .seq xs => 1 + seqHeight xs
  | .map kvs => 1 + mapHeight kvs
end

/-- Take-while length lemma. -/
theorem takeWhile_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := by
  revert l
  intro l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : p hd <;> simp [List.takeWhile, h] <;> omega

/-- Drop-while length lemma. -/
theorem dropWhile_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.dropWhile p).length ≤ l.length := by
  revert l
  intro l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : p hd <;> simp [List.dropWhile, h] <;> omega

/-- YAML nesting depth cap from the C side. -/
def yamlMaxDepth : Nat := 128

/-- The dispatcher's entry fuel. The model charges one fuel unit per
  *parsed line* (both nesting and plain items), while the C charges one
  per block (`TOC_YAML_MAX_DEPTH`). Two units per level cover any
  document the C accepts within its cap with at most one item per
  level; docs beyond that budget fail here but are outside real
  configuration shapes. -/
def yamlEntryFuel : Nat := 2 * yamlMaxDepth

/-- A line with indentation and raw text. -/
structure YL2 where
  indent : Nat
  text : String
  deriving Repr, Inhabited

/-- True iff a line starts a sequence item. -/
def isSeqItemText (s : String) : Bool :=
  (trimLeft s).startsWith "- "

/-- Strip the `- ` prefix. -/
def stripSeqItem (s : String) : String :=
  let t := trimLeft s
  if t.startsWith "- " then trimLeft (t.drop 2).toString else t

mutual
/-- Value dispatcher: pick sequence vs mapping from the head line. -/
def parseValueTotal (fuel : Nat) (base : Nat) (ls : List YL2) :
    Option (YamlValue × List YL2 × Nat) :=
  match ls with
  | [] => some (.map [], [], fuel)
  | l :: _ =>
    match fuel with
    | 0 => none
    | n + 1 =>
      if isSeqItemText l.text then
        parseSeqTotal n base ls []
      else
        parseMapTotal n base ls []
termination_by fuel

/-- Mapping worker, fuel += lines consumed. -/
def parseMapTotal (fuel : Nat) (base : Nat) (ls : List YL2)
    (acc : List (String × YamlValue)) : Option (YamlValue × List YL2 × Nat) :=
  match ls with
  | [] => some (.map acc.reverse, [], fuel)
  | l :: rest =>
    if l.indent < base then
      some (.map acc.reverse, ls, fuel)
    else if l.indent > base then
      some (.map acc.reverse, ls, fuel)
    else
      match fuel with
      | 0 => none
      | n + 1 =>
        match parseKv l.text with
        | none => none
        | some kv =>
          if kv.val.isEmpty then
            let sub := rest.takeWhile (fun x => x.indent > base)
            let rem := rest.dropWhile (fun x => x.indent > base)
            match sub with
            | [] => none
            | _ =>
              match parseValueTotal n (sub.head!.indent) sub with
              | none => none
              | some (subVal, _, d2) =>
                parseMapTotal n base rem ((kv.key, subVal) :: acc) >>= fun r =>
                  some (r.1, r.2.1, r.2.2)
          else
            parseMapTotal n base rest ((kv.key, .str kv.val) :: acc) >>= fun r =>
              some (r.1, r.2.1, r.2.2)
termination_by fuel

/-- Sequence worker, fuel += lines consumed. -/
def parseSeqTotal (fuel : Nat) (base : Nat) (ls : List YL2)
    (acc : List YamlValue) : Option (YamlValue × List YL2 × Nat) :=
  match ls with
  | [] => some (.seq acc.reverse, [], fuel)
  | l :: rest =>
    if l.indent < base then
      some (.seq acc.reverse, ls, fuel)
    else if l.indent > base then
      some (.seq acc.reverse, ls, fuel)
    else if !isSeqItemText l.text then
      some (.seq acc.reverse, ls, fuel)
    else
      match fuel with
      | 0 => none
      | n + 1 =>
        parseSeqTotal n base rest (.str (stripSeqItem l.text) :: acc) >>= fun r =>
          some (r.1, r.2.1, r.2.2)
termination_by fuel
end

/-- Full document parse (fuel-bounded; see `yamlEntryFuel`). -/
def parseYamlTotalV (lines : List YL2) : Option YamlValue :=
  match parseValueTotal yamlEntryFuel 0 lines with
  | some (v, _, _) => some v
  | none => none

/-- A right-nested mapping document of depth `n` (one `k{i}:` line per
  level, a scalar leaf at the bottom). -/
def deepMapDoc : Nat → List YL2
  | 0 => [{ indent := 0, text := "leaf: 1" }]
  | n + 1 =>
    ({ indent := 0, text := s!"k{n}:" }) :: (deepMapDoc n).map
      (fun x => { x with indent := x.indent + 2 })

/-- A 100-level document parses. -/
theorem parseYamlTotalV_deep100 :
    (parseYamlTotalV (deepMapDoc 100)).isSome := by native_decide

/-- A 127-level document parses (the model's fuel covers the C's cap). -/
theorem parseYamlTotalV_deep127 :
    (parseYamlTotalV (deepMapDoc 127)).isSome := by native_decide

/-- A 129-level document fails: the model boundary sits at the C's
  `TOC_YAML_MAX_DEPTH` (one fuel unit per level, two charged). -/
theorem parseYamlTotalV_deep129 :
    (parseYamlTotalV (deepMapDoc 129)).isNone := by native_decide


/-- The parsed 100-level document's height is 102 (one level per `k{i}:`
  line plus the leaf and the dispatcher's outer mapping node). -/
theorem parseYamlTotalV_deep100_height :
    (parseYamlTotalV (deepMapDoc 100)).get!.height = 102 := by native_decide


/-- if-then-else rewrites, stated without the deprecated `if_pos`/`if_neg`
  (the lake build promotes deprecation warnings to errors). -/
theorem itePos {c : Prop} [inst : Decidable c] (h : c) {α : Sort u} {t e : α} :
    (if c then t else e) = t := by simp [h]

theorem iteNeg {c : Prop} [inst : Decidable c] (h : ¬c) {α : Sort u} {t e : α} :
    (if c then t else e) = e := by simp [h]

theorem seqHeight_append (l1 l2 : List YamlValue) :
    seqHeight (l1 ++ l2) = Nat.max (seqHeight l1) (seqHeight l2) := by
  induction l1 with
  | nil => simp [seqHeight]
  | cons x xs ih => simp [seqHeight, ih]

theorem mapHeight_append (l1 l2 : List (String × YamlValue)) :
    mapHeight (l1 ++ l2) = Nat.max (mapHeight l1) (mapHeight l2) := by
  induction l1 with
  | nil => simp [mapHeight]
  | cons p ps ih => simp [mapHeight, ih]

theorem seqHeight_reverse (l : List YamlValue) :
    seqHeight l.reverse = seqHeight l := by
  induction l with
  | nil => simp [seqHeight]
  | cons x xs ih =>
      simp [List.reverse_cons, seqHeight_append, ih, seqHeight, Nat.max_comm]

theorem mapHeight_reverse (l : List (String × YamlValue)) :
    mapHeight l.reverse = mapHeight l := by
  induction l with
  | nil => simp [mapHeight]
  | cons p ps ih =>
      simp [List.reverse_cons, mapHeight_append, ih, mapHeight, Nat.max_comm]

/-- A `some` equation in the parser's result-tuple shape. -/
theorem someInj {x r : YamlValue × List YL2 × Nat}
    (h : some x = some r) : x = r := by
  simp only [Option.some.injEq] at h
  exact h

theorem optTriple_bind_some {α β γ : Type} (x : Option (α × β × γ))
    (r : α × β × γ) :
    (x >>= fun q => some (q.1, q.2.1, q.2.2)) = some r ↔ x = some r := by
  cases x with
  | none => simp
  | some q => simp

/-- Max arithmetic used by the height-bound induction (omega cannot see
  through `Nat.max` atoms, so the steps are spelled out). -/
theorem maxGrow (n B : Nat) :
    Nat.max n (Nat.max 1 B) ≤ Nat.max (n + 1) B := by
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · exact Nat.le_trans (Nat.le_succ n) (Nat.le_max_left (n + 1) B)
  · exact Nat.max_le.mpr
      ⟨Nat.le_trans (show (1 : Nat) ≤ n + 1 by omega) (Nat.le_max_left (n + 1) B),
        Nat.le_max_right (n + 1) B⟩

theorem maxSwap (n A B : Nat) (hA : A ≤ Nat.max n 1) :
    Nat.max n (Nat.max A B) ≤ Nat.max (n + 1) B := by
  refine Nat.max_le.mpr ⟨?_, ?_⟩
  · exact Nat.le_trans (Nat.le_succ n) (Nat.le_max_left (n + 1) B)
  · refine Nat.max_le.mpr ⟨?_, Nat.le_max_right (n + 1) B⟩
    exact Nat.le_trans
      (Nat.le_trans hA (Nat.max_le.mpr ⟨show n ≤ n + 1 by omega,
        show (1 : Nat) ≤ n + 1 by omega⟩))
      (Nat.le_max_left (n + 1) B)

theorem maxSucc1 (n : Nat) : 1 + n ≤ Nat.max (n + 1) 1 :=
  Nat.le_trans (show 1 + n ≤ n + 1 by omega) (Nat.le_max_left (n + 1) 1)

/-- `Nat.max 0 a = a`, stated on `Nat.max` so `rw` can match it. -/
theorem maxZero (a : Nat) : Nat.max 0 a = a := Nat.zero_max a

theorem maxZeroR (a : Nat) : Nat.max a 0 = a := by
  induction a with
  | zero => rfl
  | succ m => simp [Nat.max]

/-- `Nat.max`-stated wrappers: the core `Nat.le_max_*` lemmas are stated
  on the `Max.max` instance, whose atoms `omega` cannot match. -/
theorem maxLef (a b : Nat) : a ≤ Nat.max a b := Nat.le_max_left a b

theorem maxRit (a b : Nat) : b ≤ Nat.max a b := Nat.le_max_right a b

/-- Same, for the `Option.bind` head form produced by dsimp
  normalization of the instance application. -/
theorem optTriple_bind_some2 {α β γ : Type} (x : Option (α × β × γ))
    (r : α × β × γ) :
    (Option.bind x fun q => some (q.1, q.2.1, q.2.2)) = some r ↔ x = some r := by
  cases x with
  | none => simp
  | some q => simp

theorem parseTotal_height_bound (fuel : Nat) :
    (∀ (base : Nat) (ls : List YL2) (v : YamlValue) (rem : List YL2) (used : Nat),
        parseValueTotal fuel base ls = some (v, rem, used) →
        v.height ≤ Nat.max fuel 1) ∧
    (∀ (base : Nat) (ls : List YL2) (acc : List YamlValue)
        (v : YamlValue) (rem : List YL2) (used : Nat),
        parseSeqTotal fuel base ls acc = some (v, rem, used) →
        v.height ≤ 1 + Nat.max fuel (seqHeight acc)) ∧
    (∀ (base : Nat) (ls : List YL2) (acc : List (String × YamlValue))
        (v : YamlValue) (rem : List YL2) (used : Nat),
        parseMapTotal fuel base ls acc = some (v, rem, used) →
        v.height ≤ 1 + Nat.max fuel (mapHeight acc)) := by
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
        subst e1
        simp only [YamlValue.height, mapHeight]
        rw [maxZero]
        omega
      | cons l tail => rw [parseValueTotal.eq_2] at hr; simp at hr
    · intro base ls acc v rem used hr
      cases ls with
      | nil =>
        rw [parseSeqTotal.eq_1] at hr
        have he := someInj hr
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1
        simp only [YamlValue.height, seqHeight_reverse]
        rw [maxZero]
        omega
      | cons l tail =>
        rw [parseSeqTotal.eq_2] at hr
        by_cases h1 : l.indent < base
        · rw [itePos h1] at hr
          have he := someInj hr
          simp only [Prod.mk.injEq] at he
          obtain ⟨e1, e2, e3⟩ := he
          subst e1
          simp only [YamlValue.height, seqHeight_reverse]
          rw [maxZero]
          omega
        · rw [iteNeg h1] at hr
          by_cases h2 : l.indent > base
          · rw [itePos h2] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e1
            simp only [YamlValue.height, seqHeight_reverse]
            rw [maxZero]
            omega
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
              subst e1
              simp only [YamlValue.height, seqHeight_reverse]
              rw [maxZero]
              omega
    · intro base ls acc v rem used hr
      cases ls with
      | nil =>
        rw [parseMapTotal.eq_1] at hr
        have he := someInj hr
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1
        simp only [YamlValue.height, mapHeight_reverse]
        rw [maxZero]
        omega
      | cons l tail =>
        rw [parseMapTotal.eq_2] at hr
        by_cases h1 : l.indent < base
        · rw [itePos h1] at hr
          have he := someInj hr
          simp only [Prod.mk.injEq] at he
          obtain ⟨e1, e2, e3⟩ := he
          subst e1
          simp only [YamlValue.height, mapHeight_reverse]
          rw [maxZero]
          omega
        · rw [iteNeg h1] at hr
          by_cases h2 : l.indent > base
          · rw [itePos h2] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e1
            simp only [YamlValue.height, mapHeight_reverse]
            rw [maxZero]
            omega
          · rw [iteNeg h2] at hr
            simp at hr
  | succ n ih =>
    obtain ⟨hV, hS, hM⟩ := ih
    have h0s : seqHeight ([] : List YamlValue) = 0 := rfl
    have h0m : mapHeight ([] : List (String × YamlValue)) = 0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro base ls v rem used hr
      cases ls with
      | nil =>
        rw [parseValueTotal.eq_1] at hr
        have he := someInj hr
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1
        simp only [YamlValue.height, mapHeight]
        have hmax := maxLef (n + 1) 1
        omega
      | cons l tail =>
        rw [parseValueTotal.eq_3] at hr
        by_cases h1 : isSeqItemText l.text = true
        · rw [itePos h1] at hr
          have hb := hS base (l :: tail) [] v rem used hr
          simp only [h0s] at hb
          rw [maxZeroR] at hb
          exact Nat.le_trans hb (maxSucc1 n)
        · rw [iteNeg h1] at hr
          have hb := hM base (l :: tail) [] v rem used hr
          simp only [h0m] at hb
          rw [maxZeroR] at hb
          exact Nat.le_trans hb (maxSucc1 n)
    · intro base ls acc v rem used hr
      cases ls with
      | nil =>
        rw [parseSeqTotal.eq_1] at hr
        have he := someInj hr
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1
        simp only [YamlValue.height, seqHeight_reverse]
        have hmax := maxRit (n + 1) (seqHeight acc)
        omega
      | cons l tail =>
        rw [parseSeqTotal.eq_3] at hr
        by_cases h1 : l.indent < base
        · rw [itePos h1] at hr
          have he := someInj hr
          simp only [Prod.mk.injEq] at he
          obtain ⟨e1, e2, e3⟩ := he
          subst e1
          simp only [YamlValue.height, seqHeight_reverse]
          have hmax := maxRit (n + 1) (seqHeight acc)
          omega
        · rw [iteNeg h1] at hr
          by_cases h2 : l.indent > base
          · rw [itePos h2] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e1
            simp only [YamlValue.height, seqHeight_reverse]
            have hmax := maxRit (n + 1) (seqHeight acc)
            omega
          · rw [iteNeg h2] at hr
            by_cases h3 : isSeqItemText l.text = true
            · rw [h3] at hr
              rw [iteNeg (show ¬((!true) = true) by simp)] at hr
              rw [optTriple_bind_some] at hr
              have hb := hS base tail (YamlValue.str (stripSeqItem l.text) :: acc)
                v rem used hr
              simp only [seqHeight, YamlValue.height] at hb
              have mg := maxGrow n (seqHeight acc)
              exact Nat.le_trans hb (by omega)
            · rw [itePos (show (!isSeqItemText l.text) = true by
                  cases hbb : isSeqItemText l.text with
                  | false => simp
                  | true => exact absurd hbb h3)] at hr
              have he := someInj hr
              simp only [Prod.mk.injEq] at he
              obtain ⟨e1, e2, e3⟩ := he
              subst e1
              simp only [YamlValue.height, seqHeight_reverse]
              have hmax := maxRit (n + 1) (seqHeight acc)
              omega
    · intro base ls acc v rem used hr
      cases ls with
      | nil =>
        rw [parseMapTotal.eq_1] at hr
        have he := someInj hr
        simp only [Prod.mk.injEq] at he
        obtain ⟨e1, e2, e3⟩ := he
        subst e1
        simp only [YamlValue.height, mapHeight_reverse]
        have hmax := maxRit (n + 1) (mapHeight acc)
        omega
      | cons l tail =>
        rw [parseMapTotal.eq_3] at hr
        by_cases h1 : l.indent < base
        · rw [itePos h1] at hr
          have he := someInj hr
          simp only [Prod.mk.injEq] at he
          obtain ⟨e1, e2, e3⟩ := he
          subst e1
          simp only [YamlValue.height, mapHeight_reverse]
          have hmax := maxRit (n + 1) (mapHeight acc)
          omega
        · rw [iteNeg h1] at hr
          by_cases h2 : l.indent > base
          · rw [itePos h2] at hr
            have he := someInj hr
            simp only [Prod.mk.injEq] at he
            obtain ⟨e1, e2, e3⟩ := he
            subst e1
            simp only [YamlValue.height, mapHeight_reverse]
            have hmax := maxRit (n + 1) (mapHeight acc)
            omega
          · rw [iteNeg h2] at hr
            cases hkv : parseKv l.text with
            | none => simp only [hkv] at hr; simp at hr
            | some kv =>
              simp only [hkv] at hr
              by_cases h3 : kv.val.isEmpty = true
              · -- empty value: nested block sub-value
                rw [itePos h3] at hr
                cases hsub : tail.takeWhile (fun x => x.indent > base) with
                | nil => rw [hsub] at hr; simp at hr
                | cons s ss =>
                  rw [hsub] at hr
                  simp [List.head!] at hr
                  cases hv : parseValueTotal n s.indent (s :: ss) with
                  | none => simp only [hv] at hr; simp at hr
                  | some p =>
                    simp only [hv] at hr
                    have hsubH := hV s.indent (s :: ss) p.1 p.2.1 p.2.2 hv
                    first
                      | rw [optTriple_bind_some] at hr
                      | rw [optTriple_bind_some2] at hr
                    have hb := hM base
                      (tail.dropWhile (fun x => x.indent > base)) ((kv.key, p.1) :: acc)
                      v rem used hr
                    simp only [mapHeight] at hb
                    have hb2 : v.height ≤
                        1 + Nat.max n
                          (Nat.max (YamlValue.height p.1) (mapHeight acc)) := hb
                    have mg := maxSwap n (YamlValue.height p.1) (mapHeight acc) hsubH
                    exact Nat.le_trans hb2 (by omega)
              · -- non-empty value: plain string entry
                rw [iteNeg h3] at hr
                rw [optTriple_bind_some] at hr
                have hb := hM base tail ((kv.key, YamlValue.str kv.val) :: acc) v rem used hr
                simp only [mapHeight, YamlValue.height] at hb
                have mg := maxGrow n (mapHeight acc)
                exact Nat.le_trans hb (by omega)
/-- The top-level parser never returns a document taller than the entry
  fuel budget (`yamlEntryFuel = 2 * yamlMaxDepth`). -/
theorem parseYamlTotalV_height_bound (ls : List YL2) (v : YamlValue)
    (h : parseYamlTotalV ls = some v) :
    v.height ≤ 2 * yamlMaxDepth := by
  unfold parseYamlTotalV at h
  cases hp : parseValueTotal yamlEntryFuel 0 ls with
  | none => rw [hp] at h; simp at h
  | some p =>
    rw [hp] at h
    simp at h
    subst h
    have hbound :=
      (parseTotal_height_bound yamlEntryFuel).1 0 ls p.1 p.2.1 p.2.2 hp
    have hfuel : yamlEntryFuel = 2 * yamlMaxDepth := rfl
    rw [hfuel] at hbound
    have hle : Nat.max (2 * yamlMaxDepth) 1 ≤ 2 * yamlMaxDepth := by
      have hmd : yamlMaxDepth = 128 := rfl
      refine Nat.max_le.mpr ⟨?_, ?_⟩ <;> omega
    exact Nat.le_trans hbound hle
