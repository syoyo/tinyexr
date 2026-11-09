/-
  TinyEXR - Lean 4 formalization of the CLF minimal XML reader.

  Cursor-based ports of the streaming helpers in
  `sandbox/tocio/src/toc_clf.c` (`xs`, `xat`, `xtag`, `xa`, `xc`, `xt`,
  `xskip_close`, `xskip_elem`). The C reader is a flat pointer cursor
  without a DOM tree; the Lean version threads an explicit `List Char`
  remainder through fuel-bounded loops (each non-terminal iteration
  consumes at least one character, matching the C's progress
  guarantee; bytes are compared as `Char` code points, mirroring the
  C's unsigned-char discipline for non-ASCII bytes).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

set_option linter.unusedVariables false

/-- Whitespace test: C's `(unsigned char)*p <= 0x20`. -/
def xsp (c : Char) : Bool := c.val ≤ 32

/-- Drop whitespace only (no comments). -/
def dropSp (cs : List Char) : List Char := cs.dropWhile xsp

/-- Skip to the end of a `<!--` comment body (searching for `-->`).
  Consumes through the `-->` if found, else leaves the last two
  characters (mirroring C's bounded `p + 2 < end` search). -/
def skipCommentBody : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    match cs with
    | '-' :: '-' :: '>' :: rest => rest
    | [_, _] => cs
    | _ :: rest => skipCommentBody fuel rest
    | [] => []

/-- Skip to the end of a `<?` processing instruction (searching for
  `?>`). -/
def skipPiBody : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    match cs with
    | '?' :: '>' :: rest => rest
    | _ :: rest => skipPiBody fuel rest
    | [] => []

/-- `xs`: skip whitespace, XML comments and processing instructions,
  looping until none apply. Fuel-bounded. -/
def xsAux : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    let stripped := dropSp cs
    match stripped with
    | '<' :: '!' :: '-' :: '-' :: rest =>
      xsAux fuel (skipCommentBody (rest.length + 1) rest)
    | '<' :: '?' :: rest =>
      xsAux fuel (skipPiBody (rest.length + 1) rest)
    | _ => stripped

/-- Skip whitespace, comments and PIs. -/
def xs (cs : List Char) : List Char := xsAux (cs.length + 1) cs

/-- `xat`: is the next significant character `<`? -/
def xat (cs : List Char) : Bool :=
  match xs cs with
  | '<' :: _ => true
  | _ => false

/-- Tag-name character: any non-space, non-`>` (and for opening tags
  non-`/`), compared as unsigned bytes. -/
def xnameChar (cs : List Char) : List Char :=
  cs.takeWhile (fun c => c.val > 32 && c != '>')

/-- `xtag`: advance past character data to `<`, then read the tag name.
  Returns `(true, name, rest)` for an opening tag (rest just past the
  name, before attributes) and `(false, name, rest)` for a closing tag
  (name after `/`). `false` with empty name means no tag was found.
  Names are capped at 63 characters, as in C. -/
def xtag (cs0 : List Char) : Bool × String × List Char :=
  match (xs cs0).dropWhile (· != '<') with
  | [] => (false, "", [])
  | '<' :: '/' :: rest2 =>
    let nm := xnameChar rest2
    (false, String.ofList (nm.take 63), rest2.drop nm.length)
  | '<' :: rest =>
    let nm := rest.takeWhile (fun c => c.val > 32 && c != '>' && c != '/')
    let nm := nm.take 63
    (nm.length > 0, String.ofList nm, rest.drop nm.length)
  | _ => (false, "", [])

/-- `xa`: read one `key="val"` attribute. Returns
  `(true, key, val, rest)` when an attribute was read (with `val` empty
  for an unquoted value, as in C) and `(false, "", "", rest)` at `>`
  or input end. -/
def xa (cs0 : List Char) : Bool × String × String × List Char :=
  let cs := xs cs0
  match cs with
  | [] => (false, "", "", [])
  | '>' :: _ => (false, "", "", cs)
  | '/' :: _ => (false, "", "", cs)
  | _ =>
    let key := cs.takeWhile (fun c => c != '=' && c.val > 32)
    let key := key.take 63
    let rest := cs.drop key.length
    let rest := match rest with | '=' :: t => t | _ => rest
    let rest := xs rest
    match rest with
    | q :: tail =>
      if q == '"' || q == '\'' then
        let val := tail.takeWhile (· != q)
        let val := val.take 63
        (true, String.ofList key, String.ofList val, tail.drop val.length |>.drop 1)
      else
        (true, String.ofList key, "", rest)
    | _ => (true, String.ofList key, "", rest)

/-- `xc`: skip attributes/consume `>` (or `/>`). Returns
  `(selfClosing, rest)`. -/
def xc (cs0 : List Char) : Bool × List Char :=
  let cs := xs cs0
  let selfc := cs.takeWhile (· != '>')
  match cs.dropWhile (· != '>') with
  | '>' :: rest => (selfc.any (· == '/'), rest)
  | _ => (selfc.any (· == '/'), cs.dropWhile (· != '>'))

/-- `xt`: read text content up to the next `<`. Returns the raw text
  and the remainder (positioned at `<`, or at end of input). -/
def xt (cs0 : List Char) : String × List Char :=
  let cs := xs cs0
  let txt := cs.takeWhile (· != '<')
  (String.ofList txt, cs.drop txt.length)

/-- `xskip_close`: skip forward past the closing tag's `>`. -/
def xskipClose (cs : List Char) : Bool × List Char :=
  let rest := cs.dropWhile (· != '>')
  if rest.isEmpty then (false, rest) else (true, rest.drop 1)

/-- `xskip_elem`: skip the rest of an element whose opening tag name
  was just read (its attributes, text and child elements, and the
  matching close tag). Returns the remainder past `</tag>`, or at end
  of input when the close tag is absent. -/
def xskipElem (cs0 : List Char) (tag : String) : List Char :=
  let (selfc, afterAttrs) := xc cs0
  if selfc then afterAttrs
  else
    let chars := tag.toList
    let rec scan (fuel : Nat) (cs : List Char) : List Char :=
      match fuel, cs with
      | 0, _ => cs
      | _, [] => []
      | fuel + 1, '<' :: '/' :: rest =>
        let nm := rest.takeWhile (fun c => c.val > 32)
        let matchTag := nm.take chars.length == chars &&
          (nm.length = chars.length &&
           (rest.drop nm.length == [] || (rest.drop nm.length).headD ' ' == '>' ||
            xsp ((rest.drop nm.length).headD ' ')))
        if matchTag then (xskipClose (rest.drop nm.length)).2
        else scan fuel ('<' :: '/' :: rest |>.drop 1)
      | fuel + 1, _ :: rest => scan fuel rest
    scan (afterAttrs.length + 1) afterAttrs

/-- `clf_prefix`: is `pre` a prefix of `s`? -/
def clfPrefix (s pre : String) : Bool :=
  decide (s.toList.take pre.length == pre.toList)

/-! ## Small sanity certificates -/

/-- `xs` strips leading whitespace. -/
example : xs [' ', '\t', 'a'] = ['a'] := by native_decide
/-- `xtag` reads an opening tag name. -/
example : (xtag ['<', 'M', 'a', 't', 'r', 'i', 'x', '>']).2.1 == "Matrix" := by
  native_decide
/-- `xc` sees a self-closing tag. -/
example : (xc ['<', 'x', '/', '>']).1 = true := by native_decide
/-- `xt` reads text up to `<`. -/
example : (xt ['h', 'e', 'l', 'l', 'o', '<', 'f']).1 == "hello" := by native_decide
/-- `clfPrefix` works offset-free. -/
example : clfPrefix "monCurveMirrorFwd" "monCurve" = true := by native_decide

end Tocio
