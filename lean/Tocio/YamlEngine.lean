/-
  TinyEXR - Lean 4 formalization of the tocio YAML subset parser
  (`toc_yaml_parse`).

  This module mirrors the C parser's surface 1:1 so the
  `tocio-yaml-diff` differential gate can pin the model: line
  preprocessing (indent scan with tab rejection, quote-aware comment
  strip, blank / `---` / `...` handling), the block parser (mappings
  with quote-aware colon scan, dash sequences with rewritten item
  lines, nested blocks, block scalars, bare scalars, anchor/alias
  rejection), the flow parser (`{k: v, ...}`, `[a, b]`, quoted and
  escaped scalars), the `!<Tag>` property attachment (block-level tag
  lines, value tags, the C's tag-overwrite on nested values), and the
  C's exact accept/reject guards (trailing unparsed content, depth cap
  128).

  Termination: every recursive call decrements a work fuel computed
  from the input size, and the C's depth budget (`TOC_YAML_MAX_DEPTH`)
  is threaded as an exact counter (`cap`), so the model fails exactly
  where the C's depth cap fails.

  The tree dump (`dumpTree`) matches the C generator's discipline
  byte-for-byte: `s(t)` / `S(...)` / `M(k=v,...)` with backslash
  escaping of `\`, newline, `(`, `)`, `,`, `=` inside dumped text, and
  a `<tag>` prefix on tagged nodes.

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
state simply persists to end-of-line. Quote characters themselves stay
in the line (the C only uses the scan to find the cut index). -/
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

/-! ## Parsed tree (values plus `!<Tag>` properties) -/

/-- A parsed node: an optional `!<Tag>` property plus the value. Tags
reach nodes exactly where the C sets `node->tag` (block tag lines, the
map-value tag scan, and the unconditional overwrite in
`parse_inline_or_block`). -/
inductive YTree where
  | scalar (tag : Option String) (s : String)
  | seq (tag : Option String) (xs : List YTree)
  | map (tag : Option String) (kvs : List (String × YTree))
  deriving Repr

/-- Replace a node's tag (the C's `node->tag = tag` assignments). -/
def YTree.setTag : YTree → Option String → YTree
  | .scalar _ s, t => .scalar t s
  | .seq _ xs, t => .seq t xs
  | .map _ kvs, t => .map t kvs

/-- Skip spaces only (the tag scan's `while (*rest == ' ')`; tabs are
not skipped there). -/
def skipSpaces : List Char → List Char :=
  fun s => s.dropWhile (fun c => c == ' ')

/-- Leading `!<Tag>` scan. Returns the tag text (everything up to the
first `>`, or the whole remainder when the `>` is missing — the C takes
`strndup(gt, k)` with `k = tl` in that case) and the text after the
tag. `none` when the text does not start with `!<`. -/
def takeTag (s : List Char) : Option (String × List Char) :=
  match s with
  | '!' :: '<' :: gt =>
    let tl := gt.length
    let k := (gt.takeWhile (fun c => c != '>')).length
    let tag := String.ofList (gt.take k)
    let rest := if k < tl then gt.drop (k + 1) else gt.drop k
    some (tag, rest)
  | _ => none

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
`\n`) while the indentation reaches `childIndent`; the value carries
the map-value tag. -/
def blockScalar (childIndent : Nat) (ls : List YL2) (tag : Option String)
    (acc : List Char) : YTree × List YL2 :=
  match ls with
  | [] => (YTree.scalar tag (String.ofList acc.reverse), [])
  | l :: rest =>
    if l.indent >= childIndent then
      blockScalar childIndent rest tag (('\n' :: l.text.toList.reverse) ++ acc)
    else (YTree.scalar tag (String.ofList acc.reverse), l :: rest)

mutual
/-- A flow value parse (`parse_flow`): consumes one depth unit
(exact `TOC_YAML_MAX_DEPTH` semantics) and one fuel unit. Flow nodes
never carry tags (the C sets tags only on the node the enclosing
context tags). -/
def parseFlowInner (cap fuel : Nat) (s : List Char) :
    Option (YTree × List Char) :=
  match cap, fuel with
  | 0, _ => none
  | _, 0 => none
  | c + 1, f + 1 =>
    let s1 := skipFlowWs s
    match s1 with
    | [] => some (YTree.scalar none "", [])
    | '{' :: rest => parseFlowMapLoop c f (skipFlowWs rest) []
    | '[' :: rest => parseFlowSeqLoop c f (skipFlowWs rest) []
    | _ =>
      let tok := flowScalarEnd s1
      some (YTree.scalar none (unescape tok), s1.drop tok.length)

/-- Flow sequence loop (`[a, b, ...]`). -/
def parseFlowSeqLoop (cap fuel : Nat) (s : List Char) (acc : List YTree) :
    Option (YTree × List Char) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match s with
    | [] => some (YTree.seq none (YTree.scalar none "" :: acc).reverse, [])
    | ']' :: rest => some (YTree.seq none acc.reverse, rest)
    | _ =>
      let tok := flowScalarEnd s
      match if tok.isEmpty then some (YTree.scalar none "", s)
            else parseFlowInner cap f' s with
      | none => none
      | some (v, s4) =>
        let s5 := skipFlowWs s4
        match s5 with
        | ',' :: rest => parseFlowSeqLoop cap f' (skipFlowWs rest) (v :: acc)
        | ']' :: rest => some (YTree.seq none (v :: acc).reverse, rest)
        | _ => some (YTree.seq none (v :: acc).reverse, s5)

/-- Flow mapping loop (`{k: v, ...}`). -/
def parseFlowMapLoop (cap fuel : Nat) (s : List Char)
    (acc : List (String × YTree)) : Option (YTree × List Char) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match s with
    | [] => some (YTree.map none [("", YTree.scalar none "")], [])
    | '}' :: rest => some (YTree.map none acc.reverse, rest)
    | _ =>
      let keyTok := flowScalarEnd s
      let key := unescape keyTok
      let s1 := skipFlowWs (s.drop keyTok.length)
      let s2 := match s1 with | ':' :: r => skipFlowWs r | _ => s1
      match if flowScalarEnd s2 = [] then some (YTree.scalar none "", s2)
            else parseFlowInner cap f' s2 with
      | none => none
      | some (v, s4) =>
        let s5 := skipFlowWs s4
        match s5 with
        | ',' :: rest => parseFlowMapLoop cap f' (skipFlowWs rest) ((key, v) :: acc)
        | '}' :: rest => some (YTree.map none ((key, v) :: acc).reverse, rest)
        | _ => some (YTree.map none ((key, v) :: acc).reverse, s5)
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
    Option (YTree × List YL2) :=
  match cap, fuel, ls with
  | 0, _, _ => none
  | _, 0, _ => none
  | _, _, [] => none
  | c + 1, f + 1, _ => parseBlockInner c f indent ls

/-- `parse_block_inner`, including the leading `!<Tag>` block property.
A tag-only line is consumed and the tag applies either to the following
deeper-block value or to an empty scalar; a tag followed by an inline
flow value consumes the line and returns that tagged flow; anything
else rewrites the line in place (same indent) and parses it as a
normal block, tagging the result. -/
def parseBlockInner (cap fuel indent : Nat) (ls : List YL2) :
    Option (YTree × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match ls with
    | [] => none
    | l :: rest =>
      match if isDashLine l.text then none else takeTag l.text.toList with
      | some (t, rc) =>
        let r := skipSpaces rc
        if r.isEmpty then
          match rest with
          | l2 :: _ =>
            if l2.indent >= indent then
              match parseBlock cap f' l2.indent rest with
              | none => none
              | some (child, rem) =>
                some (YTree.setTag child (some t), rem)
            else some (YTree.setTag (YTree.scalar none "") (some t), rest)
          | [] => some (YTree.setTag (YTree.scalar none "") (some t), [])
        else if r.head! == '{' || r.head! == '[' then
          match parseFlowInner cap f' r with
          | none => none
          | some (v, _) => some (YTree.setTag v (some t), rest)
        else
          parseBlockBody cap f' indent
            ({ indent := l.indent, text := String.ofList r } :: rest) (some t)
      | none => parseBlockBody cap f' indent ls none

/-- The dash/map/bare-scalar body of `parse_block_inner` (after any
block-tag rewrite); `blkTag` applies to the produced node. -/
def parseBlockBody (cap fuel indent : Nat) (ls : List YL2)
    (blkTag : Option String) : Option (YTree × List YL2) :=
  match ls with
  | [] => none
  | l :: rest =>
    if isDashLine l.text then
      match parseSeqLoop cap fuel indent ls [] with
      | none => none
      | some (v, rem) => some (YTree.setTag v blkTag, rem)
    else
      match findColon l.text.toList with
      | none =>
        some (YTree.setTag (YTree.scalar none (unescape l.text.toList)) blkTag,
          rest)
      | some _ =>
        match parseMapLoop cap fuel indent ls [] with
        | none => none
        | some (v, rem) => some (YTree.setTag v blkTag, rem)

/-- Dash-sequence loop. -/
def parseSeqLoop (cap fuel indent : Nat) (ls : List YL2) (acc : List YTree) :
    Option (YTree × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match ls with
    | [] => some (YTree.seq none acc.reverse, [])
    | l :: rest =>
      if l.indent != indent || !isDashLine l.text then
        some (YTree.seq none acc.reverse, ls)
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
                parseSeqLoop cap f' indent rest (YTree.scalar none "" :: acc)
            | [] => parseSeqLoop cap f' indent [] (YTree.scalar none "" :: acc)
          else
            -- rewrite the line at the content column, parse as a block
            let rewritten : YL2 := { indent := l.indent + cc, text := ctext }
            match parseBlock cap f' (l.indent + cc) (rewritten :: rest) with
            | none => none
            | some (it, rem) => parseSeqLoop cap f' indent rem (it :: acc)

/-- Mapping loop, including the per-value `!<Tag>` scan. -/
def parseMapLoop (cap fuel indent : Nat) (ls : List YL2)
    (acc : List (String × YTree)) : Option (YTree × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    match ls with
    | [] => some (YTree.map none acc.reverse, [])
    | l :: rest =>
      if l.indent != indent || isDashLine l.text then
        some (YTree.map none acc.reverse, ls)
      else
        match findColon l.text.toList with
        | none => some (YTree.map none acc.reverse, ls)
        | some i =>
          let key := unescape (l.text.toList.take i)
          let val0 := (l.text.toList.drop (i + 1)).dropWhile (· == ' ')
          let (vtag, val) :=
            match takeTag val0 with
            | some (t, rc) => (some t, skipSpaces rc)
            | none => (none, val0)
          let childIndent : Nat :=
            match rest with
            | l2 :: _ => if l2.indent > indent then l2.indent else indent + 1
            | [] => indent + 1
          match parseInlineOrBlock cap f' val vtag childIndent rest with
          | none => none
          | some (v, rem) => parseMapLoop cap f' indent rem ((key, v) :: acc)

/-- `parse_inline_or_block`: the value after `key:` — inline scalar,
flow value, block scalar (`|` / `>`), or a deeper block. The value tag
is applied to every kind; a nested block's own tag is overwritten
unconditionally (the C assigns `child->tag = tag` even when the tag is
NULL). -/
def parseInlineOrBlock (cap fuel : Nat) (val : List Char) (tag : Option String)
    (childIndent : Nat) (ls : List YL2) : Option (YTree × List YL2) :=
  match fuel with
  | 0 => none
  | f' + 1 =>
    let v := val.dropWhile (fun c => c == ' ' || c == '\t')
    match v with
    | [] =>
      match ls with
      | l2 :: _ =>
        if l2.indent >= childIndent then
          match parseBlock cap f' l2.indent ls with
          | none => none
          | some (child, rem) => some (YTree.setTag child tag, rem)
        else some (YTree.scalar tag "", ls)
      | [] => some (YTree.scalar tag "", [])
    | '&' :: _ => none
    | '*' :: _ => none
    | '|' :: _ => some (blockScalar childIndent ls tag [])
    | '>' :: _ => some (blockScalar childIndent ls tag [])
    | '{' :: _ =>
      match parseFlowInner cap f' v with
      | none => none
      | some (fv, _) => some (YTree.setTag fv tag, ls)
    | '[' :: _ =>
      match parseFlowInner cap f' v with
      | none => none
      | some (fv, _) => some (YTree.setTag fv tag, ls)
    | _ => some (YTree.scalar tag (unescape v), ls)
end

/-! ## Entry point -/

/-- Work fuel: a generous over-approximation of the C parser's total
work (every recursive call consumes one unit; the C's own progress
guarantees mean the C never does more work than this on an accepted
input). -/
def yamlWorkFuel (text : String) : Nat := 8 * text.length + 1024

/-- `toc_yaml_parse` for the full modelled surface (including tags). -/
def yamlParse (text : String) : Option YTree :=
  match splitLinesGo (text.splitOn "\n") [] with
  | none => none
  | some [] => some (YTree.map none [])
  | some ls =>
    match ls with
    | [] => some (YTree.map none [])
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

/-- `<tag>` prefix for tagged nodes, empty otherwise. -/
def dumpTag : Option String → String
  | none => ""
  | some t => "<" ++ dumpText t ++ ">"

def dumpTree : YTree → String
  | .scalar tag s => dumpTag tag ++ "s(" ++ dumpText s ++ ")"
  | .seq tag xs => dumpTag tag ++ "S(" ++ String.intercalate "," (dumpSeqAll xs) ++ ")"
  | .map tag kvs =>
    dumpTag tag ++ "M(" ++ String.intercalate "," (dumpMapAll kvs) ++ ")"
where
  dumpSeqAll : List YTree → List String
    | [] => []
    | x :: rest => dumpTree x :: dumpSeqAll rest
  dumpMapAll : List (String × YTree) → List String
    | [] => []
    | (k, v) :: rest => (dumpText k ++ "=" ++ dumpTree v) :: dumpMapAll rest

end Tocio
