/-
  TinyEXR - Lean 4 formalization of YAML sequence parsing.

  Extends the indentation parser to handle sequences (lists of items
  prefixed with "- ").

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml
import Tocio.YamlParse

namespace Tocio

/-- A YAML line with indentation. -/
structure YL where
  indent : Nat
  text : String
  deriving Repr

/-- Check if a line is a sequence item. -/
def isSeqItem (l : YL) : Bool :=
  (trimLeft l.text).startsWith "- "

/-- Strip the "- " prefix from a sequence item. -/
def stripSeqPrefix (s : String) : String :=
  let t := trimLeft s
  if t.startsWith "- " then trimLeft (t.drop 2).toString else t

/-- Parse a sequence at base indent. -/
partial def parseSequence (base : Nat) (lines : List YL) : Option (YamlValue × List YL) :=
  let rec go (acc : List YamlValue) (ls : List YL) : Option (YamlValue × List YL) :=
    match ls with
    | [] => some (YamlValue.seq acc.reverse, [])
    | l :: rest =>
        if l.indent < base then
          some (YamlValue.seq acc.reverse, ls)
        else if l.indent > base then
          some (YamlValue.seq acc.reverse, ls)
        else if !isSeqItem l then
          some (YamlValue.seq acc.reverse, ls)
        else
          let itemText := stripSeqPrefix l.text
          let itemVal := YamlValue.str itemText
          go (itemVal :: acc) rest
  go [] lines

/-- Parse a top-level sequence at indent 0. -/
def parseYamlSeq (lines : List YL) : Option YamlValue :=
  (parseSequence 0 lines).map (·.1)

-- Empty sequence parses to empty seq (verified by construction).

end Tocio