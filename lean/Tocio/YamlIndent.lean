/-
  TinyEXR - Lean 4 formalization of an indentation-aware YAML parser.

  Total parser: given a list of (indent, text) lines, parses a mapping at a
  given base indent. Handles nested mappings and sequences. Returns Option.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.YamlTotal

namespace Tocio

/-- A line with its indentation level. (Legacy structure, kept for API.) -/
structure YLine where
  indent : Nat
  text : String
  deriving Repr, Inhabited

/-- Legacy partial parser retired: same behavior via the total worker. -/
def parseMapping (base : Nat) (lines : List YLine) :
    Option (YamlValue × List YLine) :=
  let conv : List YLine → List YL2 := List.map (fun l => { indent := l.indent, text := l.text })
  match parseValueTotal yamlMaxDepth base (conv lines) with
  | some (v, rem, _) =>
    let remL : List YLine := rem.map (fun l => { indent := l.indent, text := l.text })
    some (v, remL)
  | none => none

/-- Top-level parse: parse a mapping at indent 0. -/
def parseYamlDoc (lines : List YLine) : Option YamlValue :=
  (parseMapping 0 lines).map (·.1)

/-- Helper to make a YLine. -/
def mkLine (indent : Nat) (text : String) : YLine := { indent := indent, text := text }

-- The partial-def comment previously here was removed when the parser
-- was converted to the total fuel-bounded version.

end Tocio