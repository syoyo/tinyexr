/-
  TinyEXR - Lean 4 formalization of YAML sequence parsing.

  Extends the indentation parser to handle sequences (lists of items
  prefixed with "- ").

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.YamlTotal

namespace Tocio

/-- A YAML line with indentation. (Legacy structure, kept for API.) -/
structure YL where
  indent : Nat
  text : String
  deriving Repr, Inhabited

/-- Check if a line is a sequence item. -/
def isSeqItem (l : YL) : Bool :=
  (trimLeft l.text).startsWith "- "

/-- Strip the "- " prefix from a sequence item. -/
def stripSeqPrefix (s : String) : String :=
  let t := trimLeft s
  if t.startsWith "- " then trimLeft (t.drop 2).toString else t

/-- Legacy partial parser retired: same behavior via the total worker. -/
def parseSequence (base : Nat) (lines : List YL) :
    Option (YamlValue × List YL) :=
  let conv : List YL → List YL2 := List.map (fun l => { indent := l.indent, text := l.text })
  match parseValueTotal yamlMaxDepth base (conv lines) with
  | some (v, rem, _) =>
    let remL : List YL := rem.map (fun l => { indent := l.indent, text := l.text })
    some (v, remL)
  | none => none

/-- Parse a top-level sequence at indent 0. -/
def parseYamlSeq (lines : List YL) : Option YamlValue :=
  (parseSequence 0 lines).map (·.1)

end Tocio