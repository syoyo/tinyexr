/-
  TinyEXR - Lean 4 formalization of the tocio YAML subset parser
  (`toc_yaml_parse`), first slice: block + flow surface *without*
  `!<Tag>` handling.

  This module mirrors the C parser's covered surface 1:1 so the
  `tocio-yaml-diff` differential gate can pin the model: line
  preprocessing (indent scan with tab rejection, quote-aware comment
  strip, blank / `---` / `...` handling), the block parser (mappings
  with quote-aware colon scan, dash sequences with rewritten item
  lines, nested blocks, block scalars, bare scalars, anchor/alias
  rejection), the flow parser (`{k: v, ...}`, `[a, b]`, quoted and
  escaped scalars), and the C's exact accept/reject guards (trailing
  unparsed content, depth cap 128).

  Termination: every recursive call decrements a work fuel computed
  from the input size, and the C's depth budget (`TOC_YAML_MAX_DEPTH`)
  is threaded as an exact counter (`cap`), so the model fails exactly
  where the C's depth cap fails.

  The tree dump (`dumpYaml`) matches the C generator's discipline
  byte-for-byte: `s(t)` / `S(...)` / `M(k=v,...)` with backslash
  escaping of `\`, newline, `(`, `)`, `,`, `=` inside dumped text.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.Yaml

namespace Tocio

set_option linter.unusedVariables false

/-! ## Line preprocessing (the `toc_yaml_parse` front end) -/

/-- A significant line: indentation and postprocessed text. -/
structure YL2 where
  indent : Nat
  text : String
  deriving Repr

/-- `strip_comment`: quote-aware `#` cut. Faithful to the C state
machine — no escape handling inside the quote scan, and the quote
state simply persists to end-of-line. -/
def stripComment (s : List Char) : List Char :=
  go s none true
where
  go : List Char → Option Char → Bool → List Char
    | [], _, _ => []
    | c :: rest, q, ok =>
      match q with
      | some qc =>
        if c == qc then c :: go rest none false else c :: go rest q false
      | none =>
        if c == '"' || c == '\'' then c :: go rest (some c) false
        else if c == '#' && ok then []
        else c :: go rest none (c == ' ' || c == '\t')

/-- Indent scan: count leading spaces; any tab in the indentation is a
parse error (`none`). -/
def indentScan : List Char → Option (Nat × List Char)
  | [] => some (0, [])
  | ' ' :: rest =>
    match indentScan rest with
    | some (n, t) => some (n + 1, t)
    | none => none
  | '\t' :: _ => none
  | c :: rest => some (0, c :: rest)

/-- Trailing trim of `' '`, `'\t'` and `'\r'`. -/
def trailingTrim (s : List Char) : List Char :=
  (s.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')).reverse

/-- Split the document into significant lines. -/
def splitLinesGo : List String → List YL2 → Option (List YL2)
  | [], acc => some acc.reverse
  | l :: rest, acc =>
    match indentScan l.toList with
    | none => none
    | some (ind, body) =>
      let st := trailingTrim (stripComment body)
      if st.isEmpty then splitLinesGo rest acc
      else if st == ['-','-','-'] then splitLinesGo rest acc
      else if st.length ≥ 3 && st[0]! == '.' && st[1]! == '.' && st[2]! == '.' then
        some acc.reverse
      else splitLinesGo rest ({ indent := ind, text := String.ofList st } :: acc)

/-! ## Scalar helpers -/

/-- `find_colon`: index of the key-separator `:` — quote-aware, and a
`{`/`[` aborts (flow value, not a block key). The colon only separates
when followed by a space or end-of-line (mirroring the C; a tab does
not count). -/
def findColon (s : List Char) : Option Nat :=
  go s 0 none
where
  go : List Char → Nat → Option Char → Option Nat
    | [], _, _ => none
    | c :: rest, i, q =>
      match q with
      | some qc =>
        if c == qc then go rest (i + 1) none else go rest (i + 1) q
      | none =>
        if c == '"' then go rest (i + 1) (some '"')
        else if c == '\'' then go rest (i + 1) (some '\'')
        else if c == '{' || c == '[' then none
        else if c == ':' then
          match rest with
          | [] => some i
          | ' ' :: _ => some i
          | _ :: _ => go rest (i + 1) none
        else go rest (i + 1) none

/-- Double-quote inner escapes: `\n`, `\t`, and `\x` drops the
backslash; a trailing lone backslash stays literal. -/
def unescapeDq : List Char → List Char
  | [] => []
  | '\\' :: [] => ['\\']
  | '\\' :: c :: rest =>
    (if c == 'n' then '\n' else if c == 't' then '\t' else c) :: unescapeDq rest
  | c :: rest => c :: unescapeDq rest

/-- Single-quote inner escapes: `''` collapses to `'`. -/
def unescapeSq : List Char → List Char
  | [] => []
  | '\'' :: '\'' :: rest => '\'' :: unescapeSq rest
  | c :: rest => c :: unescapeSq rest

/-- `unescape_scalar`: trims trailing spaces/tabs, then strips matching
quotes and minimal escapes (faithful to the C, including its quirk
that the opening and closing quotes must *match*). -/
def unescape (s : List Char) : String :=
  let t := (s.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse
  match t with
  | [] => ""
  | [_] => String.ofList t
  | hd :: mid =>
    match mid.reverse with
    | last :: revMid' =>
      if hd == '"' && last == '"' then String.ofList (unescapeDq revMid'.reverse)
      else if hd == '\'' && last == '\'' then
        String.ofList (unescapeSq revMid'.reverse)
      else String.ofList t
    | [] => String.ofList t

/-! ## Flow parser (`parse_flow`) -/

/-- Skip spaces and tabs. -/
def skipFlowWs : List Char → List Char :=
  fun s => s.dropWhile (fun c => c == ' ' || c == '\t')

/-- Double-quoted flow scan (escapes skip the next char). -/
def flowDqScan : List Char → List Char
  | [] => []
  | '\\' :: c :: rest => '\\' :: c :: flowDqScan rest
  | '"' :: _ => ['"']
  | c :: rest => c :: flowDqScan rest

/-- Single-quoted flow scan. -/
def flowSqScan : List Char → List Char
  | [] => []
  | '\'' :: _ => ['\'']
  | c :: rest => c :: flowSqScan rest

/-- Plain flow scan: stops at `,` `}` `]` or a separator `:`
(colon followed by whitespace, a flow delimiter, or end). -/
def flowPlainScan : List Char → List Char
  | [] => []
  | ',' :: _ => []
  | '}' :: _ => []
  | ']' :: _ => []
  | ':' :: rest =>
    match rest with
    | [] => []
    | ' ' :: _ => []
    | '\t' :: _ => []
    | ',' :: _ => []
    | '}' :: _ => []
    | ']' :: _ => []
    | _ => ':' :: flowPlainScan rest
  | c :: rest => c :: flowPlainScan rest

/-- `flow_scalar_end`: the consumed scalar token. -/
def flowScalarEnd (s : List Char) : List Char :=
  match s with
  | '"' :: rest => '"' :: flowDqScan rest
  | '\'' :: rest => '\'' :: flowSqScan rest
  | _ => flowPlainScan s

/-- Block scalar body: concatenate the deeper lines (each followed by
`\n`) while the indentation reaches `childIndent`. -/
def blockScalar (childIndent : Nat) (ls : List YL2) (acc : List Char) :
    YamlValue × List YL2 :=
  match ls with
  | [] => (YamlValue.str (String.ofList acc.reverse), [])
  | l :: rest =>
    if l.indent >= childIndent then
      blockScalar childIndent rest (('\n' :: l.text.toList.reverse) ++ acc)
    else (YamlValue.str (String.ofList acc.reverse), l :: rest)

mutual
/-- A flow value parse (`parse_flow`): consumes one depth unit
(exact `TOC_YAML_MAX_DEPTH` semantics) and one fuel unit. -/
def parseFlowInner (cap fuel : Nat) (s : List Char) :
    Option (YamlValue × List Char) :=
  match cap, fuel with
  | 0, _ => none
  | _, 0 => none
  | c + 1, f + 1 =>
    let s1 := skipFlowWs s
    match s1 with
    | [] => some (YamlValue.str "", [])
    | '{' :: rest => parseFlowMapLoop c f (skipFlowWs rest) []
    | '[' :: rest => parseFlowSeqLoop c f (skipFlowWs rest) []
    | _ =>
      let tok := flowScalarEnd s1
      some (YamlValue.str (unescape tok), s1.drop tok.length)

/-- Flow sequence loop (`[a, b, ...]`). -/
def parseFlowSeqLoop (cap fuel : Nat) (s : List Char) (acc : List YamlValue) :
    Option (YamlValue × List Char) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match s with
    | [] => some (YamlValue.seq (YamlValue.str "" :: acc).reverse, [])
    | ']' :: rest => some (YamlValue.seq acc.reverse, rest)
    | _ =>
      let tok := flowScalarEnd s
      match if tok.isEmpty then some (YamlValue.str "", s)
            else parseFlowInner cap f' s with
      | none => none
      | some (v, s4) =>
        let s5 := skipFlowWs s4
        match s5 with
        | ',' :: rest => parseFlowSeqLoop cap f' (skipFlowWs rest) (v :: acc)
        | ']' :: rest => some (YamlValue.seq (v :: acc).reverse, rest)
        | _ => some (YamlValue.seq (v :: acc).reverse, s5)

/-- Flow mapping loop (`{k: v, ...}`). -/
def parseFlowMapLoop (cap fuel : Nat) (s : List Char)
    (acc : List (String × YamlValue)) : Option (YamlValue × List Char) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match s with
    | [] => some (YamlValue.map [("", YamlValue.str "")], [])
    | '}' :: rest => some (YamlValue.map acc.reverse, rest)
    | _ =>
      let keyTok := flowScalarEnd s
      let key := unescape keyTok
      let s1 := skipFlowWs (s.drop keyTok.length)
      let s2 := match s1 with | ':' :: r => skipFlowWs r | _ => s1
      match if flowScalarEnd s2 = [] then some (YamlValue.str "", s2)
            else parseFlowInner cap f' s2 with
      | none => none
      | some (v, s4) =>
        let s5 := skipFlowWs s4
        match s5 with
        | ',' :: rest => parseFlowMapLoop cap f' (skipFlowWs rest) ((key, v) :: acc)
        | '}' :: rest => some (YamlValue.map ((key, v) :: acc).reverse, rest)
        | _ => some (YamlValue.map ((key, v) :: acc).reverse, s5)
end

/-! ## Block parser (`parse_block`) -/

/-- `line_is_dash`: first char `-`, then end-of-line or a space (a tab
does not make a dash line). -/
def isDashLine (s : String) : Bool :=
  match s.toList with
  | '-' :: [] => true
  | '-' :: ' ' :: _ => true
  | _ => false

/-- Rewrite a dash line: skip `-` and the following spaces; returns the
content column offset (relative to the line indent) and the content. -/
def dashContent (s : String) : Option (Nat × String) :=
  match s.toList with
  | '-' :: rest =>
    let nSpaces := (rest.takeWhile (· == ' ')).length
    some (1 + nSpaces, String.ofList (rest.drop nSpaces))
  | _ => none

mutual
/-- A block parse (`parse_block`): consumes one depth unit (exact
`TOC_YAML_MAX_DEPTH` semantics) and one fuel unit, and fails on an
empty line list (as the C does). -/
def parseBlock (cap fuel indent : Nat) (ls : List YL2) :
    Option (YamlValue × List YL2) :=
  match cap, fuel, ls with
  | 0, _, _ => none
  | _, 0, _ => none
  | _, _, [] => none
  | c + 1, f + 1, _ => parseBlockInner c f indent ls

/-- `parse_block_inner` (tag handling is outside this slice). -/
def parseBlockInner (cap fuel indent : Nat) (ls : List YL2) :
    Option (YamlValue × List YL2) :=
  match ls with
  | [] => none
  | l :: _ =>
    if isDashLine l.text then parseSeqLoop cap fuel indent ls []
    else
      match findColon l.text.toList with
      | none => some (YamlValue.str (unescape l.text.toList), ls.tail)
      | some _ => parseMapLoop cap fuel indent ls []

/-- Dash-sequence loop. -/
def parseSeqLoop (cap fuel indent : Nat) (ls : List YL2) (acc : List YamlValue) :
    Option (YamlValue × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match ls with
    | [] => some (YamlValue.seq acc.reverse, [])
    | l :: rest =>
      if l.indent != indent || !isDashLine l.text then
        some (YamlValue.seq acc.reverse, ls)
      else
        match dashContent l.text with
        | none => none
        | some (cc, ctext) =>
          if ctext.isEmpty then
            -- item block on the following deeper lines (line consumed)
            match rest with
            | l2 :: _ =>
              if l2.indent > l.indent then
                match parseBlock cap f' l2.indent rest with
                | none => none
                | some (it, rem) => parseSeqLoop cap f' indent rem (it :: acc)
              else
                parseSeqLoop cap f' indent rest (YamlValue.str "" :: acc)
            | [] => parseSeqLoop cap f' indent [] (YamlValue.str "" :: acc)
          else
            -- rewrite the line at the content column, parse as a block
            let rewritten : YL2 := { indent := l.indent + cc, text := ctext }
            match parseBlock cap f' (l.indent + cc) (rewritten :: rest) with
            | none => none
            | some (it, rem) => parseSeqLoop cap f' indent rem (it :: acc)

/-- Mapping loop. -/
def parseMapLoop (cap fuel indent : Nat) (ls : List YL2)
    (acc : List (String × YamlValue)) : Option (YamlValue × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match ls with
    | [] => some (YamlValue.map acc.reverse, [])
    | l :: rest =>
      if l.indent != indent || isDashLine l.text then
        some (YamlValue.map acc.reverse, ls)
      else
        match findColon l.text.toList with
        | none => some (YamlValue.map acc.reverse, ls)
        | some i =>
          let key := unescape (l.text.toList.take i)
          let val0 := (l.text.toList.drop (i + 1)).dropWhile (· == ' ')
          let childIndent :=
            match rest with
            | l2 :: _ => if l2.indent > indent then l2.indent else indent + 1
            | [] => indent + 1
          match parseInlineOrBlock cap f' val0 childIndent rest with
          | none => none
          | some (v, rem) => parseMapLoop cap f' indent rem ((key, v) :: acc)

/-- `parse_inline_or_block`: the value after `key:` — inline scalar,
flow value, block scalar (`|` / `>`), or a deeper block. -/
def parseInlineOrBlock (cap fuel : Nat) (val : List Char) (childIndent : Nat)
    (ls : List YL2) : Option (YamlValue × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match val.dropWhile (fun c => c == ' ' || c == '\t') with
    | [] =>
      match ls with
      | l2 :: _ =>
        if l2.indent >= childIndent then parseBlock cap f' l2.indent ls
        else some (YamlValue.str "", ls)
      | [] => some (YamlValue.str "", [])
    | '&' :: _ => none
    | '*' :: _ => none
    | '|' :: _ => some (blockScalar childIndent ls [])
    | '>' :: _ => some (blockScalar childIndent ls [])
    | '{' :: _ =>
      match parseFlowInner cap f' val with
      | none => none
      | some (fv, _) => some (fv, ls)
    | '[' :: _ =>
      match parseFlowInner cap f' val with
      | none => none
      | some (fv, _) => some (fv, ls)
    | _ => some (YamlValue.str (unescape val), ls)
end

/-! ## Entry point -/

/-- Work fuel: a generous over-approximation of the C parser's total
work (every recursive call consumes one unit; the C's own progress
guarantees mean the C never does more work than this on an accepted
input). -/
def yamlWorkFuel (text : String) : Nat := 8 * text.length + 1024

/-- `toc_yaml_parse` for the tag-free subset. -/
def yamlParse (text : String) : Option YamlValue :=
  match splitLinesGo (text.splitOn "\n") [] with
  | none => none
  | some [] => some (YamlValue.map [])
  | some ls =>
    match ls with
    | [] => some (YamlValue.map [])
    | l :: _ =>
      match parseBlock 128 (yamlWorkFuel text) l.indent ls with
      | none => none
      | some (v, rem) => if rem.isEmpty then some v else none

/-! ## Tree dump (matches the C generator byte-for-byte) -/

def dumpText (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    match c with
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '(' | ')' | ',' | '=' => ['\\', c]
    | c => [c])

def dumpYaml : YamlValue → String
  | .null => "n()"
  | .bool _ => "b()"
  | .int _ => "i()"
  | .str s => "s(" ++ dumpText s ++ ")"
  | .seq xs => "S(" ++ String.intercalate "," (dumpSeqAll xs) ++ ")"
  | .map kvs =>
    "M(" ++ String.intercalate "," (dumpMapAll kvs) ++ ")"
where
  dumpSeqAll : List YamlValue → List String
    | [] => []
    | x :: rest => dumpYaml x :: dumpSeqAll rest
  dumpMapAll : List (String × YamlValue) → List String
    | [] => []
    | (k, v) :: rest => (dumpText k ++ "=" ++ dumpYaml v) :: dumpMapAll rest

end Tocio
