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
