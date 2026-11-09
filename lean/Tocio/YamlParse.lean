/-
  TinyEXR - Lean 4 formalization of a minimal tocio YAML parser.

  First slice: a total parser for a single "key: value" scalar line, plus
  a small lexer. Full indentation-aware parsing comes in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml

namespace Tocio

/-- A parsed key-value pair. -/
structure KvPair where
  key : String
  val : String
  deriving Repr, DecidableEq

/-- Trim leading spaces. -/
def trimLeft (s : String) : String := (s.dropWhile (· = ' ')).toString

/-- Trim trailing spaces. -/
def trimRight (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· = ' ')).reverse

/-- Trim both sides. -/
def trim (s : String) : String := trimLeft (trimRight s)

/-- Split a line at the first ':'. Returns none if no colon. -/
def splitColon (s : String) : Option (String × String) :=
  let parts := s.splitOn ":"
  match parts with
  | k :: rest => some (k, ":".intercalate rest)
  | [] => none

/-- Parse a single "key: value" line. -/
def parseKv (line : String) : Option KvPair :=
  match splitColon (trimLeft line) with
  | some (k, v) =>
      let key := trim k
      let val := trim v
      if key.isEmpty then none else some { key := key, val := val }
  | none => none

/-- A line is a comment if it starts with '#'. -/
def isComment (line : String) : Bool :=
  (trimLeft line).startsWith "#"

/-- A line is blank if empty after trim. -/
def isBlank (line : String) : Bool :=
  (trimLeft line).isEmpty

theorem parseKv_empty_none : parseKv "" = none := by
  native_decide

/-- Parse a list of lines into a YAML mapping (skipping blanks/comments). -/
def parseLines (lines : List String) : YamlValue :=
  let pairs := lines.filterMap (fun l =>
    if isBlank l || isComment l then none else parseKv l)
  YamlValue.map (pairs.map (fun p => (p.key, YamlValue.str p.val)))

/-- A single key-value line round-trips through parseKv. -/
theorem parseKv_simple : parseKv "foo: bar" = some { key := "foo", val := "bar" } := by
  native_decide

end Tocio