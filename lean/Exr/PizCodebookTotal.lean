/-
  TinyEXR - total checked trie construction for prefix-free PIZ codes.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizCodebook

namespace Exr.Piz.Codebook

/-- Inserted tries never contain an internal node with no leaf below it. -/
inductive Trie.WellFormed : Trie → Prop where
  | empty : WellFormed .empty
  | leaf (symbol : Nat) : WellFormed (.leaf symbol)
  | node {left right : Trie} : WellFormed left → WellFormed right →
      (left ≠ .empty ∨ right ≠ .empty) → WellFormed (.node left right)

theorem path_not_empty {trie : Trie} {symbol : Nat} {bits : List Bool}
    (hp : Path trie symbol bits) : trie ≠ .empty := by
  intro he
  subst trie
  cases hp

theorem Trie.WellFormed.path_exists {trie : Trie} (hw : trie.WellFormed) (hn : trie ≠ .empty) :
    ∃ symbol bits, Path trie symbol bits := by
  induction hw with
  | empty => exact False.elim (hn rfl)
  | leaf symbol => exact ⟨symbol,[],Path.leaf symbol⟩
  | node hl hr hchild ihl ihr =>
    rcases hchild with hc | hc
    · obtain ⟨symbol,bits,hp⟩ := ihl hc
      exact ⟨symbol,false::bits,Path.left hp⟩
    · obtain ⟨symbol,bits,hp⟩ := ihr hc
      exact ⟨symbol,true::bits,Path.right hp⟩

def Compatible (a b : List Bool) : Prop := ¬(a <+: b ∨ b <+: a)

theorem Compatible.cons (bit : Bool) {a b : List Bool} (hc : Compatible a b) :
    Compatible (bit::a) (bit::b) := by
  simpa only [Compatible,List.cons_prefix_cons,true_and] using hc

theorem fork_wellFormed (bit : Bool) (child other : Trie)
    (hc : child.WellFormed) (ho : other.WellFormed) (hn : child ≠ .empty) :
    (fork bit child other).WellFormed := by
  cases bit with
  | false => exact Trie.WellFormed.node hc ho (Or.inl hn)
  | true => exact Trie.WellFormed.node ho hc (Or.inr hn)

/-- The actual checked insertion succeeds whenever its code has no prefix
collision with an existing leaf. This includes empty tries and singleton codes. -/
theorem insert_exists (bits : List Bool) (symbol : Nat) (trie : Trie)
    (hw : trie.WellFormed) (hf : ∀ old code, Path trie old code → Compatible bits code) :
    ∃ next, insert bits symbol trie = some next ∧ next.WellFormed := by
  induction bits generalizing trie with
  | nil =>
    cases trie with
    | empty => exact ⟨.leaf symbol,rfl,Trie.WellFormed.leaf symbol⟩
    | leaf old =>
      exact False.elim ((hf old [] (Path.leaf old)) (Or.inl List.nil_prefix))
    | node left right =>
      obtain ⟨old,code,hp⟩ := hw.path_exists (by intro he; cases he)
      exact False.elim ((hf old code hp) (Or.inl List.nil_prefix))
  | cons bit bits ih =>
    cases trie with
    | empty =>
      obtain ⟨child,hi,hchild⟩ := ih .empty Trie.WellFormed.empty (by intro old code hp; cases hp)
      refine ⟨fork bit child .empty,?_,fork_wellFormed bit child .empty hchild Trie.WellFormed.empty ?_⟩
      · simp [insert,descend,hi]
      · exact path_not_empty (insert_path bits symbol .empty child hi)
    | leaf old =>
      exact False.elim ((hf old [] (Path.leaf old)) (Or.inr List.nil_prefix))
    | node left right =>
      cases hw with
      | node hleft hright _ =>
        cases bit with
        | false =>
          have hfree : ∀ old code, Path left old code → Compatible bits code := by
            intro old code hp hcollision
            apply hf old (false::code) (Path.left hp)
            simpa only [List.cons_prefix_cons,true_and] using hcollision
          obtain ⟨child,hi,hchild⟩ := ih left hleft hfree
          refine ⟨.node child right,?_,Trie.WellFormed.node hchild hright (Or.inl ?_)⟩
          · simp [insert,descend,hi,fork]
          · exact path_not_empty (insert_path bits symbol left child hi)
        | true =>
          have hfree : ∀ old code, Path right old code → Compatible bits code := by
            intro old code hp hcollision
            apply hf old (true::code) (Path.right hp)
            simpa only [List.cons_prefix_cons,true_and] using hcollision
          obtain ⟨child,hi,hchild⟩ := ih right hright hfree
          refine ⟨.node left child,?_,Trie.WellFormed.node hleft hchild (Or.inr ?_)⟩
          · simp [insert,descend,hi,fork]
          · exact path_not_empty (insert_path bits symbol right child hi)

theorem descend_path (bit : Bool) (trie child other : Trie)
    (hd : descend bit trie = some (child,other)) (symbol : Nat) (code : List Bool)
    (hp : Path child symbol code) : Path trie symbol (bit::code) := by
  cases trie with
  | empty =>
    have he : (.empty,.empty) = (child,other) := Option.some.inj hd
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    cases hp
  | leaf old => simp [descend] at hd
  | node left right =>
    cases bit with
    | false =>
      have he : (left,right) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact Path.left hp
    | true =>
      have he : (right,left) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      exact Path.right hp

theorem descend_flip (bit : Bool) (trie child other : Trie)
    (hd : descend bit trie = some (child,other)) : descend (!bit) trie = some (other,child) := by
  cases trie with
  | empty =>
    have he : (.empty,.empty) = (child,other) := Option.some.inj hd
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    cases bit <;> rfl
  | leaf symbol => simp [descend] at hd
  | node left right =>
    cases bit with
    | false =>
      have he : (left,right) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      rfl
    | true =>
      have he : (right,left) = (child,other) := Option.some.inj hd
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      rfl

/-- Insertion creates exactly its new leaf path and preserves old paths;
it cannot invent an unrelated code that could cause a later collision. -/
theorem insert_paths_only (bits : List Bool) (symbol : Nat) (trie next : Trie)
    (hi : insert bits symbol trie = some next) (old : Nat) (code : List Bool)
    (hp : Path next old code) : Path trie old code ∨ (old = symbol ∧ code = bits) := by
  induction bits generalizing trie next old code with
  | nil =>
    cases trie with
    | empty =>
      have he : Trie.leaf symbol = next := Option.some.inj hi
      rw [← he] at hp
      cases hp
      exact Or.inr ⟨rfl,rfl⟩
    | leaf s => simp [insert] at hi
    | node l r => simp [insert] at hi
  | cons bit bits ih =>
    cases hd : descend bit trie with
    | none => simp [insert,hd] at hi
    | some pair =>
      rcases pair with ⟨child,other⟩
      cases hc : insert bits symbol child with
      | none => simp [insert,hd,hc] at hi
      | some updated =>
        have he : fork bit updated other = next := by simpa [insert,hd,hc] using hi
        rw [← he] at hp
        have hparts := path_descend bit (fork bit updated other) updated other (by cases bit <;> rfl) old code hp
        rcases hparts with ⟨tail,hcode,hpath⟩ | ⟨tail,hcode,hpath⟩
        · rcases ih child updated hc old tail hpath with hold | ⟨hs,ht⟩
          · left
            rw [hcode]
            exact descend_path bit trie child other hd old tail hold
          · exact Or.inr ⟨hs,by rw [hcode,ht]⟩
        · left
          rw [hcode]
          exact descend_path (!bit) trie other child (descend_flip bit trie child other hd) old tail hpath

theorem Compatible.symm {a b : List Bool} (hc : Compatible a b) : Compatible b a := by
  simpa only [Compatible,or_comm] using hc

def Representable (word : Nat) : Prop := 0 < word%64 ∧ word%64 ≤ 58 ∧ word/64 < 2^(word%64)

def PrefixFreeEntries (entries : List (Nat × Nat)) : Prop :=
  entries.Pairwise (fun a b => a.2 = 0 ∨ b.2 = 0 ∨ Compatible (wordBits a.2) (wordBits b.2))

/-- Totality of the actual checked entry-list constructor, with zero entries
skipped exactly as in C. Prefix-freedom and packed-word bounds suffice. -/
theorem insertWords_exists (entries : List (Nat × Nat)) (trie : Trie)
    (hw : trie.WellFormed)
    (hv : ∀ entry ∈ entries, entry.2 ≠ 0 → Representable entry.2)
    (hf : PrefixFreeEntries entries)
    (hc : ∀ entry ∈ entries, entry.2 ≠ 0 → ∀ old code, Path trie old code → Compatible (wordBits entry.2) code) :
    ∃ next, insertWords entries trie = some next ∧ next.WellFormed := by
  induction entries generalizing trie with
  | nil => exact ⟨trie,rfl,hw⟩
  | cons entry rest ih =>
    have hp := List.pairwise_cons.mp hf
    have hvalid : ∀ e ∈ rest, e.2 ≠ 0 → Representable e.2 := fun e he => hv e (List.mem_cons_of_mem _ he)
    by_cases hz : entry.2 = 0
    · obtain ⟨next,he,hn⟩ := ih trie hw hvalid hp.2 (fun e he => hc e (List.mem_cons_of_mem _ he))
      exact ⟨next,by simpa [insertWords,hz] using he,hn⟩
    · have hvhead := hv entry List.mem_cons_self hz
      obtain ⟨updated,hi,hu⟩ := insert_exists (wordBits entry.2) entry.1 trie hw
        (hc entry List.mem_cons_self hz)
      have hcross : ∀ e ∈ rest, e.2 ≠ 0 → ∀ old code, Path updated old code → Compatible (wordBits e.2) code := by
        intro e he hnonzero old code hpath
        rcases insert_paths_only (wordBits entry.2) entry.1 trie updated hi old code hpath with hold | ⟨_,hcode⟩
        · exact hc e (List.mem_cons_of_mem _ he) hnonzero old code hold
        · rw [hcode]
          rcases hp.1 e he with hzero | hzero | hfree
          · exact False.elim (hz hzero)
          · exact False.elim (hnonzero hzero)
          · exact hfree.symm
      obtain ⟨next,he,hn⟩ := ih updated hu hvalid hp.2 hcross
      refine ⟨next,?_,hn⟩
      have hcheck : 0 < entry.2%64 ∧ entry.2%64 ≤ 58 ∧ entry.2/64 < 2^(entry.2%64) := hvhead
      simpa [insertWords,hz,hcheck,hi] using he

/-- Canonical-table acceptance reduces to representable packed words and
prefix-freedom of the table's actual entries, with no external trie witness. -/
theorem build_exists_of_prefixFree (lengths : List Nat)
    (hv : ∀ entry ∈ entries lengths, entry.2 ≠ 0 → Representable entry.2)
    (hf : PrefixFreeEntries (entries lengths)) : ∃ trie, build lengths = some trie := by
  obtain ⟨trie,he,_⟩ := insertWords_exists (entries lengths) .empty Trie.WellFormed.empty hv hf
    (by intro entry he hz old code hp; cases hp)
  exact ⟨trie,he⟩

end Exr.Piz.Codebook
