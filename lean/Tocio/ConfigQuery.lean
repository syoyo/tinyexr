/-
  TinyEXR - Lean 4 formalization of the tocio config query layer
  (`toc_config.c`): colorspace/role/display/view/view-transform/look
  lookups over the parsed YAML tree, including the alias matching rules
  and the transform-attribute priority.

  This module mirrors the C query surface 1:1; the
  `tocio-config-diff` gate builds the same query transcript on both
  sides and compares it byte-for-byte. Queries are derived from the
  document content (sequence order / map order), so the two sides
  enumerate identically as long as the parse trees agree (pinned by
  `tocio-yaml-diff`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Tocio.YamlEngine

namespace Tocio

set_option linter.unusedVariables false

/-! ## Node accessors (the `toc_node_map_get` / `toc_node_scalar` pair) -/

/-- First `key` entry of a mapping (`none` on non-maps). Matches the C's
`strcmp` lookup and first-match semantics. -/
def YTree.mapGet (t : YTree) (k : String) : Option YTree :=
  match t with
  | .map _ kvs => (kvs.find? (fun p => p.1 = k)).map (·.2)
  | _ => none

/-- The scalar value of a node (`none` unless it is a scalar). -/
def YTree.scalarVal : YTree → Option String
  | .scalar _ s => some s
  | _ => none

/-- Sequence items (`none` unless it is a sequence). -/
def YTree.seqItems : YTree → Option (List YTree)
  | .seq _ xs => some xs
  | _ => none

/-- Mapping pairs (`none` unless it is a mapping). -/
def YTree.mapPairs : YTree → Option (List (String × YTree))
  | .map _ kvs => some kvs
  | _ => none

/-- `toc_node_scalar(toc_node_map_get t k)`. -/
def getScalar (t : YTree) (k : String) : Option String :=
  (t.mapGet k).bind (·.scalarVal)

/-! ## Lookups -/

/-- `name_matches`: the node's `name`, or an `aliases` sequence/scalar
entry, equals the query name. -/
def nameMatches (cs : YTree) (name : String) : Bool :=
  (match getScalar cs "name" with
   | some s => s == name
   | none => false) ||
  (match cs.mapGet "aliases" with
   | some (.seq _ xs) =>
     xs.any (fun x => match x.scalarVal with
                      | some s => s == name
                      | none => false)
   | some (.scalar _ s) => s == name
   | _ => false)

/-- `find_in_seq`: first item of a sequence whose `name`/aliases match. -/
def findInSeq (seq : Option YTree) (name : String) : Option YTree :=
  match seq with
  | some (.seq _ xs) => xs.find? (fun x => nameMatches x name)
  | _ => none

/-- `toc_cfg_find_colorspace`: `colorspaces` first, then
`display_colorspaces`. -/
def findColorspace (root : YTree) (name : String) : Option YTree :=
  match findInSeq (root.mapGet "colorspaces") name with
  | some r => some r
  | none => findInSeq (root.mapGet "display_colorspaces") name

/-- `toc_cfg_resolve_role`: follow `roles.<name>` when it is a scalar. -/
def resolveRole (root : YTree) (name : String) : String :=
  match (root.mapGet "roles").bind (fun r => getScalar r name) with
  | some cs => cs
  | none => name

/-- `toc_cfg_is_data`: `isdata` is `true` or `1`. -/
def isData (cs : YTree) : Bool :=
  match getScalar cs "isdata" with
  | some s => s == "true" || s == "1"
  | none => false

/-- `toc_cfg_cs_in_display_section`: the (role-resolved) name is found in
`display_colorspaces`. -/
def inDisplaySection (root : YTree) (name : String) : Bool :=
  (findInSeq (root.mapGet "display_colorspaces") (resolveRole root name)).isSome

/-- First present attribute among `keys` (presence only, as in the C). -/
def firstPresent (cs : YTree) : List String → Option String
  | [] => none
  | k :: rest =>
    match cs.mapGet k with
    | some _ => some k
    | none => firstPresent cs rest

/-- `toc_cfg_cs_transform`: attribute name plus the invert flag. The C
recognises the v1 names first, then the scene-referred and
display-referred v2 names. -/
def csTransform (cs : YTree) (wantToRef : Bool) : Option (String × Bool) :=
  let to := firstPresent cs
    ["to_reference", "to_scene_reference", "to_display_reference"]
  let fromA := firstPresent cs
    ["from_reference", "from_scene_reference", "from_display_reference"]
  if wantToRef then
    match to with
    | some a => some (a, false)
    | none => fromA.map (fun a => (a, true))
  else
    match fromA with
    | some a => some (a, false)
    | none => to.map (fun a => (a, true))

/-- `vt_seq`: `view_transforms`, then the singular `view_transform`. -/
def vtSeq (root : YTree) : Option YTree :=
  match root.mapGet "view_transforms" with
  | some v => some v
  | none => root.mapGet "view_transform"

/-- `toc_cfg_find_view_transform`. -/
def findViewTransform (root : YTree) (name : String) : Option YTree :=
  findInSeq (vtSeq root) name

/-- `toc_cfg_default_view_transform`: the named transform when present,
else the first one. -/
def defaultViewTransform (root : YTree) : Option YTree :=
  let fallback : Option YTree :=
    match vtSeq root with
    | some (.seq _ (x :: _)) => some x
    | _ => none
  match getScalar root "default_view_transform" with
  | some s =>
    (match findViewTransform root s with
     | some vt => some vt
     | none => fallback)
  | none => fallback

/-- `toc_cfg_find_look`. -/
def findLook (root : YTree) (name : String) : Option YTree :=
  findInSeq (root.mapGet "looks") name

/-- `toc_cfg_view_looks`: split `looks` on commas, skipping spaces and
commas before each token (spaces inside a token are kept, matching the
C's in-place scan). -/
def viewLookNames (s : String) : List String :=
  go [] [] s.toList
where
  go (acc : List Char) (out : List String) : List Char → List String
    | [] => out.reverse ++ (if acc.isEmpty then [] else [String.ofList acc.reverse])
    | c :: rest =>
      if c == ',' then
        go [] (if acc.isEmpty then out else String.ofList acc.reverse :: out) rest
      else if c == ' ' && acc.isEmpty then go acc out rest
      else go (c :: acc) out rest

/-- The `name` scalar of a node (the C's `node_name` helper). -/
def nodeName : Option YTree → Option String
  | some v => getScalar v "name"
  | none => none

/-- The look names of a view node. -/
def viewLooks (vnode : YTree) : List String :=
  match getScalar vnode "looks" with
  | some s => viewLookNames s
  | none => []

/-! ## Canonical query transcript (mirrors `test/v3/config_vectors.c`) -/

/-- Escape a transcript value; `none` renders as `~`. -/
def escQuery (o : Option String) : String :=
  match o with
  | none => "~"
  | some s =>
    String.ofList (s.toList.flatMap fun c =>
      match c with
      | '\\' => ['\\', '\\']
      | ';' => ['\\', ';']
      | '=' => ['\\', '=']
      | '|' => ['\\', '|']
      | '\n' => ['\\', 'n']
      | c => [c])

/-- Bit `b` as `0`/`1`. -/
def bitStr (b : Bool) : String := if b then "1" else "0"

def seqOf : Option YTree → List YTree
  | some (.seq _ xs) => xs
  | _ => []

def pairsOf : Option YTree → List (String × YTree)
  | some (.map _ kvs) => kvs
  | _ => []

/-- The canonical transcript of the config queries over a parsed tree.
Every entry is `key=value`; values are escaped and `~` means NULL. -/
def queryTranscript (root : YTree) : String :=
  let entries : List String :=
    Id.run do
      let mut es : List String := []
      let csItems := seqOf (root.mapGet "colorspaces")
      es := es ++ [s!"ncs={csItems.length}"]
      for (i, cs) in List.zip (List.range csItems.length) csItems do
        let nm := getScalar cs "name"
        es := es ++ [s!"csv.{i}={escQuery nm}"]
        es := es ++ [s!"fd.{i}={escQuery (nm.bind (fun n => nodeName (findColorspace root n)))}"]
        es := es ++ [s!"fam.{i}={escQuery (getScalar cs "family")}"]
        es := es ++ [s!"enc.{i}={escQuery (getScalar cs "encoding")}"]
        es := es ++ [s!"data.{i}={bitStr (isData cs)}"]
        es := es ++ [s!"inds.{i}={bitStr (nm.map (inDisplaySection root) |>.getD false)}"]
        match csTransform cs true with
        | some (a, inv) =>
          es := es ++ [s!"to.{i}={escQuery (some a)}", s!"toinv.{i}={bitStr inv}"]
        | none => es := es ++ [s!"to.{i}=~", s!"toinv.{i}=0"]
        match csTransform cs false with
        | some (a, inv) =>
          es := es ++ [s!"fr.{i}={escQuery (some a)}", s!"frinv.{i}={bitStr inv}"]
        | none => es := es ++ [s!"fr.{i}=~", s!"frinv.{i}=0"]
        let aliases : List (Option String) :=
          match cs.mapGet "aliases" with
          | some (.seq _ xs) => xs.map (·.scalarVal)
          | some (.scalar _ s) => [some s]
          | _ => []
        es := es ++ [s!"nal.{i}={aliases.length}"]
        for (j, a) in List.zip (List.range aliases.length) aliases do
          es := es ++ [s!"al.{i}.{j}={escQuery a}"]
          es := es ++
            [s!"alr.{i}.{j}={escQuery (a.bind (fun n => nodeName (findColorspace root n)))}"]
      let dcItems := seqOf (root.mapGet "display_colorspaces")
      es := es ++ [s!"ndcs={dcItems.length}"]
      for (i, cs) in List.zip (List.range dcItems.length) dcItems do
        es := es ++ [s!"dcs.{i}={escQuery (getScalar cs "name")}"]
      let rolesNode := root.mapGet "roles"
      let rolePairs := match rolesNode with
        | some r => pairsOf r
        | none => []
      es := es ++ [s!"nroles={rolePairs.length}"]
      for (i, p) in List.zip (List.range rolePairs.length) rolePairs do
        es := es ++ [s!"role.{i}.k={escQuery (some p.1)}"]
        es := es ++ [s!"role.{i}.v={escQuery ((rolePairs.find? (fun q => q.1 = p.1)).bind (fun q => q.2.scalarVal))}"]
        es := es ++ [s!"role.{i}.r={escQuery (some (resolveRole root p.1))}"]
      let dispPairs := pairsOf (root.mapGet "displays")
      es := es ++ [s!"ndisp={dispPairs.length}"]
      for (i, p) in List.zip (List.range dispPairs.length) dispPairs do
        es := es ++ [s!"disp.{i}={escQuery (some p.1)}"]
        let views := seqOf (some p.2)
        es := es ++ [s!"nviews.{i}={views.length}"]
        for (j, v) in List.zip (List.range views.length) views do
          es := es ++ [s!"view.{i}.{j}={escQuery (getScalar v "name")}"]
          let looks := viewLooks v
          es := es ++ [s!"nvl.{i}.{j}={looks.length}"]
          for (k, lk) in List.zip (List.range looks.length) looks do
            es := es ++ [s!"vl.{i}.{j}.{k}={escQuery (some lk)}"]
      let vts := seqOf (vtSeq root)
      es := es ++ [s!"nvt={vts.length}"]
      for (i, vt) in List.zip (List.range vts.length) vts do
        es := es ++ [s!"vt.{i}={escQuery (getScalar vt "name")}"]
      es := es ++
        [s!"vtd={escQuery (nodeName (defaultViewTransform root))}"]
      let lookItems := seqOf (root.mapGet "looks")
      es := es ++ [s!"nlooks={lookItems.length}"]
      for (i, lk) in List.zip (List.range lookItems.length) lookItems do
        let lnm := getScalar lk "name"
        es := es ++ [s!"look.{i}={escQuery lnm}"]
        es := es ++ [s!"lkf.{i}={escQuery (lnm.bind (fun n => nodeName (findLook root n)))}"]
      match root.mapGet "active_displays" with
      | none => es := es ++ ["nad=-1"]
      | some a =>
        let xs := seqOf (some a)
        es := es ++ [s!"nad={xs.length}"]
        for (i, x) in List.zip (List.range xs.length) xs do
          es := es ++ [s!"ad.{i}={escQuery x.scalarVal}"]
      match root.mapGet "active_views" with
      | none => es := es ++ ["nav=-1"]
      | some a =>
        let xs := seqOf a
        es := es ++ [s!"nav={xs.length}"]
        for (i, x) in List.zip (List.range xs.length) xs do
          es := es ++ [s!"av.{i}={escQuery x.scalarVal}"]
      return es
  String.intercalate ";" entries

end Tocio
