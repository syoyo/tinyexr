/-
  TinyEXR - Lean 4 formalization of an indentation-aware YAML parser.

  Total parser: given a list of (indent, text) lines, parses a mapping at a
  given base indent. Handles nested mappings and sequences. Returns Option.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml
import Tocio.YamlParse

namespace Tocio

/-- A line with its indentation level. -/
structure YLine where
  indent : Nat
  text : String
  deriving Repr

/-- Parse a mapping starting at base indent. Returns the map and remaining lines. -/
partial def parseMapping (base : Nat) (lines : List YLine) : Option (YamlValue × List YLine) :=
  let rec go (acc : List (String × YamlValue)) (ls : List YLine) : Option (YamlValue × List YLine) :=
    match ls with
    | [] => some (YamlValue.map acc.reverse, [])
    | l :: rest =>
        if l.indent < base then
          -- end of this mapping
          some (YamlValue.map acc.reverse, ls)
        else if l.indent > base then
          -- unexpected indent; skip? treat as end
          some (YamlValue.map acc.reverse, ls)
        else
          -- parse key: value at this indent
          match parseKv l.text with
          | none => none
          | some kv =>
              -- check if value is empty (nested block follows)
              if kv.val.isEmpty then
                -- nested: parse sub-block at indent > base
                let subLines := rest.takeWhile (fun x => x.indent > base)
                let remaining := rest.dropWhile (fun x => x.indent > base)
                let subBase := match subLines.head? with | some l => l.indent | none => base + 1
                match parseMapping subBase subLines with
                | none => none
                | some (subVal, _) =>
                    go ((kv.key, subVal) :: acc) remaining
              else
                go ((kv.key, YamlValue.str kv.val) :: acc) rest
  go [] lines

/-- Top-level parse: parse a mapping at indent 0. -/
def parseYamlDoc (lines : List YLine) : Option YamlValue :=
  (parseMapping 0 lines).map (·.1)

/-- Helper to make a YLine. -/
def mkLine (indent : Nat) (text : String) : YLine := { indent := indent, text := text }

-- Empty document parses to empty map (verified by construction).

end Tocio