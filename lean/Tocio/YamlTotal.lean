/-
  TinyEXR - Lean 4 formalization of a total YAML document parser.

  Combines mapping and sequence parsing with indentation. Total function
  (returns Option). Handles top-level mappings and sequences.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml
import Tocio.YamlParse
import Tocio.YamlIndent
import Tocio.YamlSeq

namespace Tocio

/-- A YAML line with indentation. -/
structure YL2 where
  indent : Nat
  text : String
  deriving Repr

/-- Parse a value at the given indent. Dispatches to mapping or sequence. -/
partial def parseValue (base : Nat) (lines : List YL2) : Option (YamlValue × List YL2) :=
  match lines with
  | [] => some (YamlValue.map [], [])
  | l :: _ =>
      if l.indent < base then
        some (YamlValue.map [], lines)
      else
        let isSeq := (trimLeft l.text).startsWith "- "
        if isSeq then
          parseSeq base lines
        else
          parseMap base lines
where
  parseMap (base : Nat) (lines : List YL2) : Option (YamlValue × List YL2) :=
    let rec go (acc : List (String × YamlValue)) (ls : List YL2) : Option (YamlValue × List YL2) :=
      match ls with
      | [] => some (YamlValue.map acc.reverse, [])
      | l :: rest =>
          if l.indent < base then
            some (YamlValue.map acc.reverse, ls)
          else if l.indent > base then
            some (YamlValue.map acc.reverse, ls)
          else
            match parseKv l.text with
            | none => none
            | some kv =>
                if kv.val.isEmpty then
                  let subLines := rest.takeWhile (fun x => x.indent > base)
                  let remaining := rest.dropWhile (fun x => x.indent > base)
                  let subBase := match subLines.head? with | some sl => sl.indent | none => base + 1
                  match parseValue subBase (subLines.map (fun x => { indent := x.indent, text := x.text })) with
                  | none => none
                  | some (subVal, _) => go ((kv.key, subVal) :: acc) remaining
                else
                  go ((kv.key, YamlValue.str kv.val) :: acc) rest
    go [] lines
  parseSeq (base : Nat) (lines : List YL2) : Option (YamlValue × List YL2) :=
    let rec go (acc : List YamlValue) (ls : List YL2) : Option (YamlValue × List YL2) :=
      match ls with
      | [] => some (YamlValue.seq acc.reverse, [])
      | l :: rest =>
          if l.indent < base then
            some (YamlValue.seq acc.reverse, ls)
          else if l.indent > base then
            some (YamlValue.seq acc.reverse, ls)
          else if !(trimLeft l.text).startsWith "- " then
            some (YamlValue.seq acc.reverse, ls)
          else
            let itemText := trimLeft ((trimLeft l.text).drop 2).toString
            go (YamlValue.str itemText :: acc) rest
    go [] lines

/-- Parse a full YAML document. -/
def parseYamlTotal (lines : List YL2) : Option YamlValue :=
  (parseValue 0 lines).map (·.1)

end Tocio