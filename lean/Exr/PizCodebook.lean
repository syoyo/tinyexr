/-
  TinyEXR - checked PIZ canonical-code trie construction and symbol parsing.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizBits

namespace Exr.Piz.Codebook

inductive Trie where
  | empty
  | leaf (symbol : Nat)
  | node (left right : Trie)
  deriving Repr, DecidableEq

inductive Path : Trie → Nat → List Bool → Prop where
  | leaf (symbol : Nat) : Path (.leaf symbol) symbol []
  | left {l r symbol bits} : Path l symbol bits → Path (.node l r) symbol (false::bits)
  | right {l r symbol bits} : Path r symbol bits → Path (.node l r) symbol (true::bits)

def fork (side : Bool) (child other : Trie) : Trie :=
  if side then .node other child else .node child other

def descend (side : Bool) : Trie → Option (Trie × Trie)
  | .empty => some (.empty,.empty)
  | .leaf _ => none
  | .node l r => if side then some (r,l) else some (l,r)

/-- Reject duplicate codes and every prefix collision at insertion time. -/
def insert : List Bool → Nat → Trie → Option Trie
  | [], symbol, .empty => some (.leaf symbol)
  | [], _, _ => none
  | side::bits, symbol, trie => do
    let (child,other) ← descend side trie
    let next ← insert bits symbol child
    pure (fork side next other)

def decode : Trie → List Bool → Option (Nat × List Bool)
  | .empty, _ => none
  | .leaf symbol, bits => some (symbol,bits)
  | .node l _, false::bits => decode l bits
  | .node _ r, true::bits => decode r bits
  | .node _ _, [] => none

theorem decode_path {trie : Trie} {symbol : Nat} {bits : List Bool}
    (hp : Path trie symbol bits) (suffix : List Bool) :
    decode trie (bits ++ suffix) = some (symbol,suffix) := by
  induction hp with
  | leaf symbol => rfl
  | left _ ih => exact ih
  | right _ ih => exact ih

theorem path_fork (side : Bool) (child other : Trie) (symbol : Nat) (bits : List Bool)
    (hp : Path child symbol bits) : Path (fork side child other) symbol (side::bits) := by
  cases side with
  | false => exact Path.left hp
  | true => exact Path.right hp

theorem insert_path (bits : List Bool) (symbol : Nat) (trie next : Trie)
    (hi : insert bits symbol trie = some next) : Path next symbol bits := by
  induction bits generalizing trie next with
  | nil =>
    cases trie with
    | empty => cases Option.some.inj hi; exact Path.leaf symbol
    | leaf s => simp [insert] at hi
    | node l r => simp [insert] at hi
  | cons side bits ih =>
    cases hd : descend side trie with
    | none => simp [insert, hd] at hi
    | some pair =>
      rcases pair with ⟨child,other⟩
      cases hc : insert bits symbol child with
      | none => simp [insert, hd, hc] at hi
      | some updated =>
        have he : fork side updated other = next := by simpa [insert, hd, hc] using hi
        rw [← he]
        exact path_fork side updated other symbol bits (ih child updated hc)

/-- An old path either follows the insertion child, or the untouched sibling. -/
theorem path_descend (side : Bool) (trie child other : Trie)
    (hd : descend side trie = some (child,other)) (symbol : Nat) (bits : List Bool)
    (hp : Path trie symbol bits) :
    (∃ tail, bits = side::tail ∧ Path child symbol tail) ∨
      (∃ tail, bits = (!side)::tail ∧ Path other symbol tail) := by
  cases trie with
  | empty => cases hp
  | leaf s => simp [descend] at hd
  | node l r =>
    cases side with
    | false =>
      have he : (l,r) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      cases hp with
      | left hp => exact Or.inl ⟨_,rfl,hp⟩
      | right hp => exact Or.inr ⟨_,rfl,hp⟩
    | true =>
      have he : (r,l) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      cases hp with
      | left hp => exact Or.inr ⟨_,rfl,hp⟩
      | right hp => exact Or.inl ⟨_,rfl,hp⟩

theorem insert_preserves (bits : List Bool) (symbol : Nat) (trie next : Trie)
    (hi : insert bits symbol trie = some next) (old : Nat) (code : List Bool)
    (hp : Path trie old code) : Path next old code := by
  induction bits generalizing trie next old code with
  | nil =>
    cases trie with
    | empty => cases hp
    | leaf s => simp [insert] at hi
    | node l r => simp [insert] at hi
  | cons side bits ih =>
    cases hd : descend side trie with
    | none => simp [insert, hd] at hi
    | some pair =>
      rcases pair with ⟨child,other⟩
      cases hc : insert bits symbol child with
      | none => simp [insert, hd, hc] at hi
      | some updated =>
        have he : fork side updated other = next := by simpa [insert, hd, hc] using hi
        rw [← he]
        rcases path_descend side trie child other hd old code hp with hcase | hcase
        · obtain ⟨tail,rfl,hchild⟩ := hcase
          exact path_fork side updated other old tail (ih child updated hc old tail hchild)
        · obtain ⟨tail,rfl,hother⟩ := hcase
          cases side with
          | false => exact Path.right hother
          | true => exact Path.left hother

/-- Packed table entries store length in six low bits and code above it. -/
def wordBits (word : Nat) : List Bool := Huffman.codeBits (word%64) (word/64)

def insertWords : List (Nat × Nat) → Trie → Option Trie
  | [], trie => some trie
  | (symbol,word)::rest, trie =>
    if word = 0 then insertWords rest trie else
      if 0 < word%64 ∧ word%64 ≤ 58 ∧ word/64 < 2^(word%64) then do
        let next ← insert (wordBits word) symbol trie
        insertWords rest next
      else none

theorem insertWords_preserves (entries : List (Nat × Nat)) (trie next : Trie)
    (he : insertWords entries trie = some next) (symbol : Nat) (bits : List Bool)
    (hp : Path trie symbol bits) : Path next symbol bits := by
  induction entries generalizing trie with
  | nil => cases Option.some.inj he; exact hp
  | cons entry rest ih =>
    rcases entry with ⟨s,w⟩
    by_cases hz : w = 0
    · exact ih trie (by simpa [insertWords, hz] using he) hp
    · by_cases hv : 0 < w%64 ∧ w%64 ≤ 58 ∧ w/64 < 2^(w%64)
      · cases hi : insert (wordBits w) s trie with
        | none => simp [insertWords, hz, hv, hi] at he
        | some updated =>
          have ht : insertWords rest updated = some next := by
            simpa [insertWords, hz, hv, hi] using he
          exact ih updated ht (insert_preserves _ _ _ _ hi symbol bits hp)
      · simp [insertWords, hz, hv] at he

theorem insertWords_paths (entries : List (Nat × Nat)) (trie next : Trie)
    (he : insertWords entries trie = some next) :
    ∀ entry ∈ entries, entry.2 ≠ 0 → Path next entry.1 (wordBits entry.2) := by
  induction entries generalizing trie with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨s,w⟩
    by_cases hz : w = 0
    · have ht : insertWords rest trie = some next := by simpa [insertWords, hz] using he
      intro entry hm hw
      rcases List.mem_cons.mp hm with hm | hm
      · subst entry; exact False.elim (hw hz)
      · exact ih trie ht entry hm hw
    · by_cases hv : 0 < w%64 ∧ w%64 ≤ 58 ∧ w/64 < 2^(w%64)
      · cases hi : insert (wordBits w) s trie with
        | none => simp [insertWords, hz, hv, hi] at he
        | some updated =>
          have ht : insertWords rest updated = some next := by
            simpa [insertWords, hz, hv, hi] using he
          intro entry hm hw
          rcases List.mem_cons.mp hm with hm | hm
          · subst entry
            exact insertWords_preserves rest updated next ht s (wordBits w) (insert_path _ _ _ _ hi)
          · exact ih updated ht entry hm hw
      · simp [insertWords, hz, hv] at he

def entries (lengths : List Nat) : List (Nat × Nat) :=
  ((canonicalTable lengths).zipIdx).map (fun p => (p.2,p.1))

def build (lengths : List Nat) : Option Trie := insertWords (entries lengths) .empty

/-- The code-path hypotheses required by symbol inversion are derived from
checked construction of the actual canonical table, rather than supplied by
an external caller. Malformed prefix/duplicate tables are rejected. -/
theorem build_paths (lengths : List Nat) (trie : Trie) (hb : build lengths = some trie)
    (entry : Nat × Nat) (hm : entry ∈ entries lengths) (hw : entry.2 ≠ 0) :
    Path trie entry.1 (wordBits entry.2) := insertWords_paths _ _ _ hb entry hm hw

theorem decode_built (lengths : List Nat) (trie : Trie) (hb : build lengths = some trie)
    (entry : Nat × Nat) (hm : entry ∈ entries lengths) (hw : entry.2 ≠ 0) (suffix : List Bool) :
    decode trie (wordBits entry.2 ++ suffix) = some (entry.1,suffix) :=
  decode_path (build_paths lengths trie hb entry hm hw) suffix

theorem decode_sound (trie : Trie) (bits : List Bool) (symbol : Nat) (rest : List Bool)
    (hd : decode trie bits = some (symbol,rest)) :
    ∃ code, Path trie symbol code ∧ bits = code ++ rest := by
  induction trie generalizing bits with
  | empty => simp [decode] at hd
  | leaf s =>
    have he : (s,bits) = (symbol,rest) := Option.some.inj hd
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨[], Path.leaf _, rfl⟩
  | node l r ihl ihr =>
    cases bits with
    | nil => simp [decode] at hd
    | cons b tail =>
      cases b with
      | false =>
        obtain ⟨code,hp,he⟩ := ihl tail hd
        exact ⟨false::code, Path.left hp, by simp [he]⟩
      | true =>
        obtain ⟨code,hp,he⟩ := ihr tail hd
        exact ⟨true::code, Path.right hp, by simp [he]⟩

def Trie.NonLeaf : Trie → Prop
  | .leaf _ => False
  | _ => True

theorem insert_nonleaf (bits : List Bool) (symbol : Nat) (trie next : Trie)
    (hp : 0 < bits.length) (hi : insert bits symbol trie = some next) : next.NonLeaf := by
  cases bits with
  | nil => simp at hp
  | cons b rest =>
    cases hc : descend b trie with
    | none => simp [insert, hc] at hi
    | some pair =>
      rcases pair with ⟨child,other⟩
      cases hs : insert rest symbol child with
      | none => simp [insert, hc, hs] at hi
      | some updated =>
        have he : fork b updated other = next := by simpa [insert, hc, hs] using hi
        rw [← he]
        cases b <;> trivial

theorem insertWords_nonleaf (entries : List (Nat × Nat)) (trie next : Trie)
    (he : insertWords entries trie = some next) (hn : trie.NonLeaf) : next.NonLeaf := by
  induction entries generalizing trie with
  | nil => cases Option.some.inj he; exact hn
  | cons entry rest ih =>
    rcases entry with ⟨s,w⟩
    by_cases hz : w = 0
    · exact ih trie (by simpa [insertWords, hz] using he) hn
    · by_cases hv : 0 < w%64 ∧ w%64 ≤ 58 ∧ w/64 < 2^(w%64)
      · cases hi : insert (wordBits w) s trie with
        | none => simp [insertWords, hz, hv, hi] at he
        | some updated =>
          have ht : insertWords rest updated = some next := by
            simpa [insertWords, hz, hv, hi] using he
          exact ih updated ht (insert_nonleaf _ _ _ _ (by simpa [wordBits, Bits.codeBits_length] using hv.1) hi)
      · simp [insertWords, hz, hv] at he

theorem build_nonleaf (lengths : List Nat) (trie : Trie) (hb : build lengths = some trie) :
    trie.NonLeaf := insertWords_nonleaf _ _ _ hb (by trivial)

/-- A checked codebook cannot decode zero-bit symbols. Every successful
symbol read strictly advances the input, even for a singleton alphabet. -/
theorem decode_progress (lengths : List Nat) (trie : Trie) (hb : build lengths = some trie)
    (bits : List Bool) (symbol : Nat) (rest : List Bool)
    (hd : decode trie bits = some (symbol,rest)) : rest.length < bits.length := by
  obtain ⟨code,hp,he⟩ := decode_sound trie bits symbol rest hd
  have hn := build_nonleaf lengths trie hb
  have hc : 0 < code.length := by
    cases hp with
    | leaf s => exact False.elim hn
    | left hp => simp
    | right hp => simp
  rw [he, List.length_append]
  omega

theorem canonicalTable_getElem? (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    (canonicalTable lengths)[i]? = some (canonicalWord lengths i) := by
  simp only [canonicalTable, List.getElem?_map, List.getElem?_range hi, Option.map_some]

theorem canonicalTable_getD (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    (canonicalTable lengths).getD i 0 = canonicalWord lengths i := by
  rw [List.getD_eq_getElem?_getD, canonicalTable_getElem? lengths i hi, Option.getD_some]

theorem canonical_entry_mem (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    (i,canonicalWord lengths i) ∈ entries lengths := by
  apply List.mem_map.mpr
  refine ⟨(canonicalWord lengths i,i), ?_, rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (canonicalTable_getElem? lengths i hi)

/-- Every active symbol's actual packed canonical word follows a checked
trie path, so no external tree/path witness is needed by payload inversion. -/
theorem decode_canonical (lengths : List Nat) (trie : Trie) (hb : build lengths = some trie)
    (i : Nat) (hi : i < lengths.length) (hl : 0 < lengths.getD i 0)
    (hmax : lengths.getD i 0 < 64) (suffix : List Bool) :
    decode trie (wordBits ((canonicalTable lengths).getD i 0) ++ suffix) = some (i,suffix) := by
  rw [canonicalTable_getD lengths i hi]
  have hw : canonicalWord lengths i ≠ 0 := by
    intro hz
    have hn := canonicalWord_length lengths i hmax
    rw [hz] at hn
    omega
  exact decode_built lengths trie hb _ (canonical_entry_mem lengths i hi) hw suffix

/-- Concrete malformed-table regressions are kernel-checked, not native oracles. -/
theorem reject_oversubscribed : build [1,1,1] = none := by decide

theorem reject_prefix_collision : build [1,2] = none := by decide

end Exr.Piz.Codebook
