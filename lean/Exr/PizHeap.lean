/-
  TinyEXR - PIZ frequency heap and Huffman merge construction.
  The array binary heap uses the same strict comparisons and left-child tie
  preference as src/exr_piz.c; frequency order is reversed for a min heap.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
module
public import Batteries.Data.BinaryHeap
import all Batteries.Data.BinaryHeap.Lemmas
import all Batteries.Data.BinaryHeap.Basic
import Batteries.Classes.Order


public section

namespace Exr.Piz.Frequency

inductive Tree where
  | leaf (symbol : Nat)
  | branch (left right : Tree)
  deriving Repr, DecidableEq

def Tree.leaves : Tree → List Nat
  | .leaf s => [s]
  | .branch l r => l.leaves ++ r.leaves

def Tree.depths : Tree → List (Nat × Nat)
  | .leaf s => [(s,0)]
  | .branch l r => (l.depths ++ r.depths).map (fun p => (p.1,p.2+1))

structure Entry where
  representative : Nat
  weight : Nat
  tree : Tree
  deriving Repr, DecidableEq

instance : Ord Entry := (inferInstance : Ord Int).on (fun e => -(e.weight : Int))
instance : Std.TransOrd Entry := Std.TransOrd.instOn (fun e : Entry => -(e.weight : Int))

abbrev Heap := Batteries.BinaryHeap Entry

/-- The second extracted representative survives, matching C's m/ mm merge. -/
def merge (first second : Entry) : Entry :=
  ⟨second.representative, first.weight + second.weight, .branch second.tree first.tree⟩

def combine (heap : Heap) : Option Heap := do
  let first ← heap.max
  let rest := heap.popMax
  let second ← rest.max
  pure (rest.popMax.insert (merge first second))

theorem combine_wf (heap next : Heap) (hw : heap.WF) (hc : combine heap = some next) :
    next.WF := by
  unfold combine at hc
  cases h1 : heap.max with
  | none => simp [h1] at hc
  | some first =>
    cases h2 : heap.popMax.max with
    | none => simp [h1,h2] at hc
    | some second =>
      have he : next = heap.popMax.popMax.insert (merge first second) := by
        simpa [h1,h2] using hc.symm
      rw [he]
      exact Batteries.BinaryHeap.insert_wf
        (Batteries.BinaryHeap.popMax_wf (Batteries.BinaryHeap.popMax_wf hw))

theorem combine_size (heap next : Heap) (hc : combine heap = some next) :
    next.size + 1 = heap.size := by
  unfold combine at hc
  cases h1 : heap.max with
  | none => simp [h1] at hc
  | some first =>
    cases h2 : heap.popMax.max with
    | none => simp [h1,h2] at hc
    | some second =>
      have he : next = heap.popMax.popMax.insert (merge first second) := by
        simpa [h1,h2] using hc.symm
      have hn := Batteries.BinaryHeap.size_pos_of_max h2
      rw [Batteries.BinaryHeap.size_popMax] at hn
      rw [he, Batteries.BinaryHeap.size_insert, Batteries.BinaryHeap.size_popMax,
        Batteries.BinaryHeap.size_popMax]
      omega

private theorem sum_perm {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b rest => simp [Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Aggregate over the current forest, not over mutable frequency slots. -/
def total (f : Entry → Nat) (heap : Heap) : Nat := (heap.arr.toList.map f).sum

theorem total_pop (f : Entry → Nat) (heap : Heap) (entry : Entry)
    (hm : heap.max = some entry) : total f heap = f entry + total f heap.popMax := by
  have hp := Batteries.BinaryHeap.popMax_perm (Batteries.BinaryHeap.size_pos_of_max hm)
  rw [← Batteries.BinaryHeap.max_eq_arr_zero hm] at hp
  have hs := sum_perm (hp.map f)
  simpa [total] using hs.symm

theorem total_insert (f : Entry → Nat) (heap : Heap) (entry : Entry) :
    total f (heap.insert entry) = total f heap + f entry := by
  have hp := Batteries.BinaryHeap.heapifyUp_perm
    (a := heap.vector.push entry) (i := ⟨heap.size, Nat.lt_succ_self _⟩)
  have hs := sum_perm (hp.toList.map f)
  simpa [total, Batteries.BinaryHeap.insert, Vector.toList_push, Batteries.BinaryHeap.vector, Vector.toList] using hs

/-- A merge conserves total frequency mass for every successful step. -/
theorem combine_total (f : Entry → Nat)
    (hf : ∀ a b, f (merge a b) = f a + f b)
    (heap next : Heap) (hc : combine heap = some next) :
    total f next = total f heap := by
  unfold combine at hc
  cases h1 : heap.max with
  | none => simp [h1] at hc
  | some first =>
    cases h2 : heap.popMax.max with
    | none => simp [h1,h2] at hc
    | some second =>
      have he : next = heap.popMax.popMax.insert (merge first second) := by
        simpa [h1,h2] using hc.symm
      have ha := total_pop f heap first h1
      have hb := total_pop f heap.popMax second h2
      rw [he, total_insert]
      rw [hf]
      omega

theorem combine_weight (heap next : Heap) (hc : combine heap = some next) :
    total Entry.weight next = total Entry.weight heap :=
  combine_total Entry.weight (fun _ _ => rfl) heap next hc

def leafCount (symbol : Nat) (entry : Entry) : Nat := entry.tree.leaves.count symbol

theorem combine_leafCount (symbol : Nat) (heap next : Heap) (hc : combine heap = some next) :
    total (leafCount symbol) next = total (leafCount symbol) heap := by
  apply combine_total (leafCount symbol) ?_ heap next hc
  intro a b
  simp [leafCount, merge, Tree.leaves, List.count_append, Nat.add_comm]

theorem compare_isGE (a b : Entry) : (compare a b).isGE = true ↔ a.weight ≤ b.weight := by
  change (compare (-(a.weight : Int)) (-(b.weight : Int))).isGE = true ↔ _
  rw [Std.LawfulLECmp.isGE_iff_ge]
  omega

theorem minimum_weight (heap : Heap) (hw : heap.WF) (entry : Entry)
    (hm : heap.max = some entry) (other : Entry) (ho : other ∈ heap) :
    entry.weight ≤ other.weight := by
  have hg := Batteries.BinaryHeap.max_ge_all hw ho (Batteries.BinaryHeap.size_pos_of_max hm)
  simp only [hm, Option.get_some] at hg
  exact (compare_isGE entry other).mp hg

theorem combine_exists (heap : Heap) (hn : 2 ≤ heap.size) : ∃ next, combine heap = some next := by
  cases h1 : heap.max with
  | none =>
    have hz := Batteries.BinaryHeap.max_eq_none_iff.mp h1
    omega
  | some first =>
    cases h2 : heap.popMax.max with
    | none =>
      have hz := Batteries.BinaryHeap.max_eq_none_iff.mp h2
      rw [Batteries.BinaryHeap.size_popMax] at hz
      omega
    | some second =>
      exact ⟨heap.popMax.popMax.insert (merge first second), by simp [combine, h1, h2]⟩

def buildGo : Nat → Heap → Option Entry
  | 0, _ => none
  | fuel + 1, heap =>
    if heap.size = 1 then heap.max else do
      let next ← combine heap
      buildGo fuel next

/-- The heap-size decrease supplies enough fuel for all merges. -/
theorem buildGo_exists (heap : Heap) (fuel : Nat) (hp : 0 < heap.size)
    (hf : heap.size ≤ fuel) : ∃ entry, buildGo fuel heap = some entry := by
  induction fuel generalizing heap with
  | zero => omega
  | succ fuel ih =>
    by_cases hs : heap.size = 1
    · cases hm : heap.max with
      | none =>
        have hz := Batteries.BinaryHeap.max_eq_none_iff.mp hm
        omega
      | some entry => exact ⟨entry, by simp [buildGo, hs, hm]⟩
    · obtain ⟨next, hn⟩ := combine_exists heap (by omega)
      have hsize := combine_size heap next hn
      obtain ⟨entry, he⟩ := ih next (by omega) (by omega)
      exact ⟨entry, by simp [buildGo, hs, hn, he]⟩

/-- Any additive aggregate conserved by a merge is conserved by the complete
construction. In particular this accounts for every input symbol, including RLE. -/
theorem buildGo_total (f : Entry → Nat) (ha : ∀ a b, f (merge a b) = f a + f b)
    (fuel : Nat) (heap : Heap) (entry : Entry) (he : buildGo fuel heap = some entry) :
    f entry = total f heap := by
  induction fuel generalizing heap with
  | zero => simp [buildGo] at he
  | succ fuel ih =>
    by_cases hs : heap.size = 1
    · have hm : heap.max = some entry := by simpa [buildGo, hs] using he
      have hp := total_pop f heap entry hm
      have hz : heap.popMax.size = 0 := by rw [Batteries.BinaryHeap.size_popMax, hs]
      have harr : heap.popMax.arr = #[] := by
        apply Array.eq_empty_iff_size_eq_zero.mpr
        exact hz
      simpa [total, harr] using hp.symm
    · cases hn : combine heap with
      | none => simp [buildGo, hs, hn] at he
      | some next =>
        have hc : buildGo fuel next = some entry := by simpa [buildGo, hs, hn] using he
        exact (ih next hc).trans (combine_total f ha heap next hn)

/-- Full construction preserves frequency mass. -/
theorem buildGo_weight (fuel : Nat) (heap : Heap) (entry : Entry)
    (he : buildGo fuel heap = some entry) : entry.weight = total Entry.weight heap :=
  buildGo_total Entry.weight (fun _ _ => rfl) fuel heap entry he

/-- Full construction preserves the multiplicity of every symbol. -/
theorem buildGo_leafCount (symbol fuel : Nat) (heap : Heap) (entry : Entry)
    (he : buildGo fuel heap = some entry) :
    leafCount symbol entry = total (leafCount symbol) heap := by
  apply buildGo_total (leafCount symbol) ?_ fuel heap entry he
  intro a b
  simp [leafCount, merge, Tree.leaves, List.count_append, Nat.add_comm]


/-- The choices made by the two forms of sift-down, including equal keys.
Index zero is the old root; one/two are left/right children. -/
def cPick (root left right : Nat) : Nat :=
  let selected := if left < root then 1 else 0
  if right < (if selected = 1 then left else root) then 2 else selected

def heapPick (root left right : Nat) : Nat :=
  let child := if right < left then 2 else 1
  if (if child = 2 then right else left) < root then child else 0

theorem cPick_eq_heapPick (root left right : Nat) :
    cPick root left right = heapPick root left right := by
  by_cases hl : left < root <;> by_cases hr : right < root <;>
    by_cases hc : right < left <;> simp [cPick, heapPick, hl, hr, hc] <;> omega

/-- Trailing absent symbols do not move the synthetic run marker. The marker
is one greater than the largest used sample symbol and has frequency one. -/
def seeds (used : List Nat) : List Entry :=
  (List.range used.length).filterMap (fun i =>
    let f := used.getD i 0
    if f = 0 then none else some (⟨i, f, .leaf i⟩ : Entry)) ++
    [⟨used.length, 1, .leaf used.length⟩]

/-- Enumerate sparse frequencies once instead of repeatedly indexing a list. -/
def sparseSeeds (used : List Nat) : List Entry :=
  used.zipIdx.filterMap (fun p =>
    if p.1 = 0 then none else some (⟨p.2,p.1,.leaf p.2⟩ : Entry)) ++
    [⟨used.length,1,.leaf used.length⟩]

@[csimp] theorem seeds_sparse : seeds = sparseSeeds := by
  funext used
  have he : (List.range used.length).map (fun i => (used.getD i 0,i)) = used.zipIdx := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < used.length
    · simp [List.getElem?_zipIdx, List.getElem?_range hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have hn : used.length ≤ i := by omega
      simp [hn]
  unfold seeds sparseSeeds
  rw [← he, List.filterMap_map]
  rfl

def prepare (frequencies : List Nat) : Option (List Entry) :=
  let used := (frequencies.reverse.dropWhile (· == 0)).reverse
  if used.isEmpty then none else some (seeds used)

def build (frequencies : List Nat) : Option Entry := do
  let entries ← prepare frequencies
  let heap := entries.toArray.toBinaryHeap
  buildGo heap.size heap

/-- Construct the same length array as C's hlink/scode accumulation. A tree
merge increases every leaf depth once. Overlong codes are explicitly rejected. -/
def lengths (frequencies : List Nat) : Option (List Nat) := do
  let root ← build frequencies
  let depths := root.tree.depths
  if depths.any (fun p => p.2 > 58) then none else
    pure ((depths.foldl (fun a p => a.set! p.1 p.2)
      (Array.replicate (frequencies.length+1) 0)).toList)

theorem prepare_nonempty (frequencies : List Nat) (entries : List Entry)
    (he : prepare frequencies = some entries) : entries ≠ [] := by
  dsimp only [prepare] at he
  split at he
  · simp at he
  · cases Option.some.inj he
    simp [seeds]

theorem build_exists (frequencies : List Nat) (entries : List Entry)
    (he : prepare frequencies = some entries) : ∃ root, build frequencies = some root := by
  have hn := prepare_nonempty frequencies entries he
  have hp : 0 < entries.length := List.length_pos_iff.mpr hn
  have hs : entries.toArray.toBinaryHeap.size = entries.length := by simp
  obtain ⟨root, hr⟩ := buildGo_exists entries.toArray.toBinaryHeap _ (by omega) (Nat.le_refl _)
  exact ⟨root, by simpa [build, he] using hr⟩

theorem lengths_size (frequencies result : List Nat) (he : lengths frequencies = some result) :
    result.length = frequencies.length + 1 := by
  unfold lengths at he
  cases hb : build frequencies with
  | none => simp [hb] at he
  | some root =>
    simp only [hb] at he
    change (if root.tree.depths.any (fun p => p.2 > 58) then none else
      some ((root.tree.depths.foldl (fun a p => a.set! p.1 p.2)
        (Array.replicate (frequencies.length+1) 0)).toList)) = some result at he
    split at he
    · simp at he
    · have hs : ∀ (depths : List (Nat × Nat)) (a : Array Nat),
          (depths.foldl (fun a p => a.set! p.1 p.2) a).size = a.size := by
        intro depths
        induction depths with
        | nil => intro a; rfl
        | cons p rest ih =>
          intro a
          simp only [List.foldl_cons]
          rw [ih]
          simp
      have hresult := Option.some.inj he
      rw [← hresult]
      simpa using hs root.tree.depths (Array.replicate (frequencies.length+1) 0)


theorem combine_minima (heap next : Heap) (hw : heap.WF) (hc : combine heap = some next) :
    ∃ first second, heap.max = some first ∧ heap.popMax.max = some second ∧
      (∀ other ∈ heap, first.weight ≤ other.weight) ∧
      (∀ other ∈ heap.popMax, second.weight ≤ other.weight) := by
  unfold combine at hc
  cases h1 : heap.max with
  | none => simp [h1] at hc
  | some first =>
    cases h2 : heap.popMax.max with
    | none => simp [h1,h2] at hc
    | some second =>
      exact ⟨first, second, rfl, rfl, minimum_weight heap hw first h1,
        minimum_weight heap.popMax (Batteries.BinaryHeap.popMax_wf hw) second h2⟩

theorem merged_weight_bounded (heap : Heap) (first second : Entry)
    (h1 : heap.max = some first) (h2 : heap.popMax.max = some second)
    (limit : Nat) (hb : total Entry.weight heap ≤ limit) :
    (merge first second).weight ≤ limit := by
  have ha := total_pop Entry.weight heap first h1
  have hc := total_pop Entry.weight heap.popMax second h2
  simp only [merge]
  omega

theorem Tree.leaves_pos (tree : Tree) : 0 < tree.leaves.length := by
  induction tree with
  | leaf s => simp [Tree.leaves]
  | branch l r ihl ihr => simp only [Tree.leaves, List.length_append]; omega

theorem Tree.depths_symbols (tree : Tree) : tree.depths.map Prod.fst = tree.leaves := by
  induction tree with
  | leaf s => rfl
  | branch l r ihl ihr =>
    simp only [Tree.depths, Tree.leaves, List.map_map, List.map_append]
    change l.depths.map Prod.fst ++ r.depths.map Prod.fst = l.leaves ++ r.leaves
    rw [ihl, ihr]

/-- Depth cannot exceed the number of merges above a leaf. This establishes
a structural bound independently of the codec's explicit 58-bit cap. -/
theorem Tree.depth_bound (tree : Tree) : ∀ p ∈ tree.depths, p.2 < tree.leaves.length := by
  induction tree with
  | leaf symbol =>
    intro p hp
    simp only [Tree.depths, List.mem_singleton] at hp
    subst p
    simp [Tree.leaves]
  | branch l r ihl ihr =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hl := l.leaves_pos
    have hr := r.leaves_pos
    simp only [Tree.leaves, List.length_append]
    rcases List.mem_append.mp hq with hq | hq
    · have hb := ihl q hq
      omega
    · have hb := ihr q hq
      omega

theorem buildGo_leafNumber (fuel : Nat) (heap : Heap) (entry : Entry)
    (he : buildGo fuel heap = some entry) :
    entry.tree.leaves.length = total (fun e => e.tree.leaves.length) heap := by
  apply buildGo_total (fun e => e.tree.leaves.length) ?_ fuel heap entry he
  intro a b
  simp [merge, Tree.leaves, List.length_append, Nat.add_comm]


private theorem depths_fold_bounded (depths : List (Nat × Nat)) (a : Array Nat)
    (hd : ∀ p ∈ depths, p.2 ≤ 58) (ha : ∀ v ∈ a, v ≤ 58) :
    ∀ v ∈ depths.foldl (fun a p => a.set! p.1 p.2) a, v ≤ 58 := by
  induction depths generalizing a with
  | nil => exact ha
  | cons p rest ih =>
    apply ih (a.set! p.1 p.2) (fun q hq => hd q (List.mem_cons_of_mem p hq))
    intro v hv
    rw [Array.set!_eq_setIfInBounds] at hv
    rcases Array.mem_or_eq_of_mem_setIfInBounds hv with hv | hv
    · exact ha v hv
    · rw [hv]
      exact hd p List.mem_cons_self

/-- Every emitted table length is representable in the codec's 58-bit code
format. The constructor never silently truncates an overlong Huffman tree. -/
theorem lengths_bound (frequencies result : List Nat) (he : lengths frequencies = some result) :
    ∀ depth ∈ result, depth ≤ 58 := by
  unfold lengths at he
  cases hb : build frequencies with
  | none => simp [hb] at he
  | some root =>
    simp only [hb] at he
    change (if root.tree.depths.any (fun p => p.2 > 58) then none else
      some ((root.tree.depths.foldl (fun a p => a.set! p.1 p.2)
        (Array.replicate (frequencies.length+1) 0)).toList)) = some result at he
    split at he
    · simp at he
    · rename_i hcap
      have hd : ∀ p ∈ root.tree.depths, p.2 ≤ 58 := by
        intro p hp
        by_cases hl : p.2 ≤ 58
        · exact hl
        · have ht : root.tree.depths.any (fun p => p.2 > 58) = true :=
            List.any_eq_true.mpr ⟨p, hp, by simp [show 58 < p.2 by omega]⟩
          exact False.elim (hcap ht)
      have hs := depths_fold_bounded root.tree.depths
        (Array.replicate (frequencies.length+1) 0) hd (by simp)
      have hr := Option.some.inj he
      intro depth hm
      rw [← hr] at hm
      exact hs depth (by simpa using hm)


private theorem filtered_leaf_ids (indices frequencies : List Nat) :
    ((indices.filterMap (fun i =>
      if frequencies.getD i 0 = 0 then none else
        some (⟨i, frequencies.getD i 0, .leaf i⟩ : Entry))).flatMap (fun e => e.tree.leaves)) =
    indices.filter (fun i => frequencies.getD i 0 != 0) := by
  simp only [List.getD_eq_getElem?_getD]
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    by_cases hz : frequencies[i]?.getD 0 = 0
    · simp [hz, ih]
    · simp [hz, ih, Tree.leaves]

theorem seeds_leaves (used : List Nat) :
    (seeds used).flatMap (fun e => e.tree.leaves) =
      (List.range used.length).filter (fun i => used.getD i 0 != 0) ++ [used.length] := by
  simp only [seeds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Tree.leaves, List.append_nil, filtered_leaf_ids]

theorem seeds_nodup (used : List Nat) :
    ((seeds used).flatMap (fun e => e.tree.leaves)).Nodup := by
  rw [seeds_leaves, List.nodup_append]
  refine ⟨List.Pairwise.filter _ List.nodup_range, by simp, ?_⟩
  intro a ha b hb
  have hh := List.mem_range.mp (List.mem_filter.mp ha).1
  have he := List.mem_singleton.mp hb
  omega

theorem total_initial (f : Entry → Nat) (entries : List Entry) :
    total f entries.toArray.toBinaryHeap = (entries.map f).sum := by
  have hp := Batteries.BinaryHeap.mkHeap_perm (a := (⟨entries.toArray, rfl⟩ : Vector Entry entries.length))
  have ht := (Array.perm_iff_toList_perm.mp hp).map f
  simpa [total, Array.toBinaryHeap] using sum_perm ht

theorem total_leafCount_initial (symbol : Nat) (entries : List Entry) :
    total (leafCount symbol) entries.toArray.toBinaryHeap =
      ((entries.flatMap (fun e => e.tree.leaves)).count symbol) := by
  rw [total_initial]
  exact (List.count_flatMap).symm

/-- No merge loses or duplicates a symbol; the synthetic run marker is
outside the original symbol range, so the final code tree has unique leaves. -/
theorem build_nodup (frequencies : List Nat) (root : Entry) (hb : build frequencies = some root) :
    root.tree.leaves.Nodup := by
  unfold build at hb
  cases hp : prepare frequencies with
  | none => simp [hp] at hb
  | some entries =>
    have he : buildGo entries.toArray.toBinaryHeap.size entries.toArray.toBinaryHeap = some root := by
      simpa [hp] using hb
    have hn : (entries.flatMap (fun e => e.tree.leaves)).Nodup := by
      dsimp only [prepare] at hp
      split at hp
      · simp at hp
      · have hr := Option.some.inj hp
        rw [← hr]
        exact seeds_nodup _
    apply List.nodup_iff_count.mpr
    intro symbol
    have hc := buildGo_leafCount symbol _ _ root he
    rw [total_leafCount_initial] at hc
    change leafCount symbol root ≤ 1
    rw [hc]
    exact List.nodup_iff_count.mp hn symbol


theorem buildGo_mem_initial (symbol fuel : Nat) (entries : List Entry) (root : Entry)
    (he : buildGo fuel entries.toArray.toBinaryHeap = some root) :
    symbol ∈ root.tree.leaves ↔ symbol ∈ entries.flatMap (fun e => e.tree.leaves) := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  change 0 < leafCount symbol root ↔ _
  rw [buildGo_leafCount symbol fuel _ root he, total_leafCount_initial]

theorem seeds_symbols_bounded (used : List Nat) (symbol : Nat)
    (hm : symbol ∈ (seeds used).flatMap (fun e => e.tree.leaves)) : symbol ≤ used.length := by
  rw [seeds_leaves] at hm
  rcases List.mem_append.mp hm with hm | hm
  · have hi := List.mem_range.mp (List.mem_filter.mp hm).1
    omega
  · exact Nat.le_of_eq (List.mem_singleton.mp hm)

/-- Every leaf, including the synthetic run marker, fits the output length
array. No successful length construction drops an out-of-bounds symbol. -/
theorem build_symbols_bounded (frequencies : List Nat) (root : Entry)
    (hb : build frequencies = some root) : ∀ symbol ∈ root.tree.leaves, symbol ≤ frequencies.length := by
  unfold build at hb
  cases hp : prepare frequencies with
  | none => simp [hp] at hb
  | some entries =>
    have he : buildGo entries.toArray.toBinaryHeap.size entries.toArray.toBinaryHeap = some root := by
      simpa [hp] using hb
    intro symbol hm
    have hi := (buildGo_mem_initial symbol _ entries root he).mp hm
    dsimp only [prepare] at hp
    split at hp
    · simp at hp
    · have hs := Option.some.inj hp
      rw [← hs] at hi
      have hbound := seeds_symbols_bounded _ symbol hi
      have hlen := (List.dropWhile_sublist (l := frequencies.reverse) (· == 0)).length_le
      simp only [List.length_reverse] at hbound hlen
      omega

theorem build_depth_indices_bounded (frequencies : List Nat) (root : Entry)
    (hb : build frequencies = some root) (p : Nat × Nat) (hp : p ∈ root.tree.depths) :
    p.1 < frequencies.length + 1 := by
  have hm : p.1 ∈ root.tree.leaves := by
    rw [← root.tree.depths_symbols]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hi := build_symbols_bounded frequencies root hb p.1 hm
  omega


end Exr.Piz.Frequency
