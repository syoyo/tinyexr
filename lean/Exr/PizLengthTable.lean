/-
  TinyEXR - exact emitted PIZ Huffman length-table profile.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
module
public import Exr.PizKraft
import all Exr.PizHeap
import all Exr.PizKraft

public section
namespace Exr.Piz.Frequency

def depthWrites (depths : List (Nat × Nat)) (data : Array Nat) : Array Nat :=
  depths.foldl (fun a p => a.set! p.1 p.2) data

theorem depthWrites_size (depths : List (Nat × Nat)) (data : Array Nat) :
    (depthWrites depths data).size = data.size := by
  induction depths generalizing data with
  | nil => rfl
  | cons p rest ih =>
    change (depthWrites rest (data.set! p.1 p.2)).size = data.size
    rw [ih,Array.size_set!]

theorem depthWrites_absent (depths : List (Nat × Nat)) (data : Array Nat) (i : Nat)
    (hn : ∀ p ∈ depths, p.1 ≠ i) : (depthWrites depths data)[i]! = data[i]! := by
  induction depths generalizing data with
  | nil => rfl
  | cons p rest ih =>
    change (depthWrites rest (data.set! p.1 p.2))[i]! = _
    rw [ih _ (fun p hp => hn p (List.mem_cons_of_mem _ hp))]
    exact Array.getElem!_set!_ne data _ _ _ (hn p List.mem_cons_self)

theorem depthWrites_mem (depths : List (Nat × Nat)) (data : Array Nat)
    (hn : (depths.map Prod.fst).Nodup) (hb : ∀ p ∈ depths, p.1 < data.size)
    (p : Nat × Nat) (hp : p ∈ depths) : (depthWrites depths data)[p.1]! = p.2 := by
  induction depths generalizing data with
  | nil => simp at hp
  | cons q rest ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      change (depthWrites rest (data.set! q.1 q.2))[q.1]! = _
      rw [depthWrites_absent rest _ q.1 (by
        intro p hp he
        exact hnd.1 (List.mem_map.mpr ⟨p,hp,he⟩))]
      exact Array.getElem!_set!_self data _ _ (hb q List.mem_cons_self)
    · change (depthWrites rest (data.set! q.1 q.2))[p.1]! = _
      exact ih _ hnd.2 (fun p hp => by simpa only [Array.size_set!] using hb p (List.mem_cons_of_mem _ hp)) hp

theorem lengths_eq_depthWrites (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result) :
    result = (depthWrites root.tree.depths (Array.replicate (frequencies.length+1) 0)).toList := by
  unfold lengths at he
  simp only [hb] at he
  change (if root.tree.depths.any (fun p => p.2 > 58) then none else
    some (depthWrites root.tree.depths (Array.replicate (frequencies.length+1) 0)).toList) = some result at he
  split at he
  · simp at he
  · exact (Option.some.inj he).symm

theorem natArray_list_getD (data : Array Nat) (i : Nat) (hi : i < data.size) :
    data.toList.getD i 0 = data[i]! := by
  have hl : i < data.toList.length := by simpa using hi
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some,
    Array.getElem_toList,getElem!_pos data i hi]

/-- Every active leaf's exact tree depth is retained at its symbol index.
Unique leaves and bounded indices are derived from the actual heap build. -/
theorem lengths_leaf_depth (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result)
    (p : Nat × Nat) (hp : p ∈ root.tree.depths) : result.getD p.1 0 = p.2 := by
  have hn : (root.tree.depths.map Prod.fst).Nodup := by
    rw [Tree.depths_symbols]
    exact build_nodup frequencies root hb
  have hbound : ∀ q ∈ root.tree.depths, q.1 < (Array.replicate (frequencies.length+1) 0).size := by
    intro q hq
    simpa only [Array.size_replicate] using build_depth_indices_bounded frequencies root hb q hq
  rw [lengths_eq_depthWrites frequencies result root hb he]
  rw [natArray_list_getD _ p.1 (by rw [depthWrites_size]; exact hbound p hp)]
  exact depthWrites_mem _ _ hn hbound p hp

/-- Slots without a tree leaf remain absent symbols (length zero). -/
theorem lengths_absent (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result)
    (i : Nat) (hi : i < result.length) (hn : i ∉ root.tree.leaves) : result.getD i 0 = 0 := by
  have hindex : i < frequencies.length+1 := by rw [lengths_size frequencies result he] at hi; exact hi
  rw [lengths_eq_depthWrites frequencies result root hb he]
  rw [natArray_list_getD _ i (by simp only [depthWrites_size,Array.size_replicate]; exact hindex)]
  rw [depthWrites_absent _ _ i (by
    intro p hp heq
    have hm : p.1 ∈ root.tree.leaves := by
      rw [← root.tree.depths_symbols]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    exact hn (heq ▸ hm))]
  rw [getElem!_pos (Array.replicate (frequencies.length+1) 0) i (by simpa only [Array.size_replicate] using hindex)]
  simp

theorem list_weight_set (values : List Nat) (i value : Nat) (weight : Nat → Nat)
    (hw : weight 0 = 0) (hi : i < values.length) (hz : values[i] = 0) :
    ((values.set i value).map weight).sum = (values.map weight).sum+weight value := by
  induction values generalizing i with
  | nil => simp at hi
  | cons head rest ih =>
    cases i with
    | zero =>
      have he : head = 0 := hz
      simp [he,hw,Nat.add_comm]
    | succ i =>
      have hi' : i < rest.length := by simp only [List.length_cons] at hi; omega
      have hz' : rest[i] = 0 := hz
      simp only [List.set_cons_succ,List.map_cons,List.sum_cons]
      rw [ih i hi' hz',Nat.add_assoc]

theorem array_weight_set (data : Array Nat) (i value : Nat) (weight : Nat → Nat)
    (hw : weight 0 = 0) (hi : i < data.size) (hz : data[i]! = 0) :
    ((data.set! i value).toList.map weight).sum = (data.toList.map weight).sum+weight value := by
  have hl : i < data.toList.length := by simpa using hi
  have hz' : data.toList[i] = 0 := by
    simpa only [Array.getElem_toList,getElem!_pos data i hi] using hz
  simpa only [Array.toList_set!] using list_weight_set data.toList i value weight hw hl hz'

/-- Distinct in-bounds depth writes add exactly their weighted leaf mass to
an initially absent set of slots; no depth is lost or counted twice. -/
theorem depthWrites_weight (depths : List (Nat × Nat)) (data : Array Nat) (weight : Nat → Nat)
    (hw : weight 0 = 0) (hn : (depths.map Prod.fst).Nodup)
    (hb : ∀ p ∈ depths, p.1 < data.size) (hz : ∀ p ∈ depths, data[p.1]! = 0) :
    ((depthWrites depths data).toList.map weight).sum =
      (data.toList.map weight).sum+(depths.map (fun p => weight p.2)).sum := by
  induction depths generalizing data with
  | nil => simp [depthWrites]
  | cons p rest ih =>
    have hnd := List.nodup_cons.mp hn
    have hz' : ∀ q ∈ rest, (data.set! p.1 p.2)[q.1]! = 0 := by
      intro q hq
      rw [Array.getElem!_set!_ne _ p.1 q.1 _ (by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨q,hq,he.symm⟩))]
      exact hz q (List.mem_cons_of_mem _ hq)
    change ((depthWrites rest (data.set! p.1 p.2)).toList.map weight).sum = _
    rw [ih _ hnd.2 (fun q hq => by simpa only [Array.size_set!] using hb q (List.mem_cons_of_mem _ hq)) hz',
      array_weight_set data p.1 p.2 weight hw (hb p List.mem_cons_self) (hz p List.mem_cons_self)]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

@[expose] def tableMass (ceiling : Nat) (lengths : List Nat) : Nat :=
  (lengths.map (fun depth => if depth = 0 then 0 else 2^(ceiling-depth))).sum

/-- Full binary trees with at least two leaves have no zero-length leaf. -/
theorem Tree.branch_depths_positive (left right : Tree) :
    ∀ p ∈ (Tree.branch left right).depths, 0 < p.2 := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  omega

/-- Exact Kraft mass transfers from the accepted tree to the emitted length
array, provided its root is a branch (proved for prepared frequency heaps). -/
theorem lengths_mass_of_branch (frequencies result : List Nat) (left right : Tree)
    (root : Entry) (ht : root.tree = .branch left right)
    (hb : build frequencies = some root) (he : lengths frequencies = some result) :
    tableMass 58 result = 2^58 := by
  let weight := fun depth => if depth = 0 then 0 else 2^(58-depth)
  have hw : weight 0 = 0 := rfl
  have hn : (root.tree.depths.map Prod.fst).Nodup := by
    rw [Tree.depths_symbols]
    exact build_nodup frequencies root hb
  have hbound : ∀ p ∈ root.tree.depths, p.1 < (Array.replicate (frequencies.length+1) 0).size := by
    intro p hp
    simpa only [Array.size_replicate] using build_depth_indices_bounded frequencies root hb p hp
  have hz : ∀ p ∈ root.tree.depths, (Array.replicate (frequencies.length+1) 0)[p.1]! = 0 := by
    intro p hp
    rw [getElem!_pos (Array.replicate (frequencies.length+1) 0) p.1 (hbound p hp)]
    simp
  have hm := depthWrites_weight root.tree.depths (Array.replicate (frequencies.length+1) 0) weight hw hn hbound hz
  have hinit : ((Array.replicate (frequencies.length+1) 0).toList.map weight).sum = 0 := by simp [hw]
  have hmap : root.tree.depths.map (fun p => weight p.2) =
      root.tree.depths.map (fun p => 2^(58-p.2)) := by
    apply List.map_congr_left
    intro p hp
    have hp' : 0 < p.2 := by rw [ht] at hp; exact Tree.branch_depths_positive left right p hp
    exact ite_eq_right (by omega)
  rw [hinit,Nat.zero_add,hmap] at hm
  rw [lengths_eq_depthWrites frequencies result root hb he]
  change ((depthWrites root.tree.depths (Array.replicate (frequencies.length+1) 0)).toList.map weight).sum = _
  rw [hm]
  exact accepted_tree_mass frequencies result root hb he

theorem trimmed_has_active (frequencies : List Nat)
    (hn : (frequencies.reverse.dropWhile (· == 0)).reverse ≠ []) :
    ∃ i, i < (frequencies.reverse.dropWhile (· == 0)).reverse.length ∧
      (frequencies.reverse.dropWhile (· == 0)).reverse.getD i 0 ≠ 0 := by
  let tail := frequencies.reverse.dropWhile (· == 0)
  have ht : tail ≠ [] := by
    intro he
    apply hn
    change tail.reverse = []
    rw [he]
    rfl
  have hh := List.head_dropWhile_not (fun n : Nat => n == 0) (l := frequencies.reverse) ht
  have hm : tail.head ht ∈ tail.reverse := List.mem_reverse.mpr (List.head_mem ht)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,hi,?_⟩
  change tail.reverse.getD i 0 ≠ 0
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he]
  intro hz
  rw [hz] at hh
  simp at hh

/-- Every successfully prepared heap contains a real active symbol and the
separate run marker. Its final tree therefore cannot be a singleton leaf. -/
theorem build_is_branch (frequencies : List Nat) (root : Entry) (hb : build frequencies = some root) :
    ∃ left right, root.tree = .branch left right := by
  unfold build at hb
  cases hp : prepare frequencies with
  | none => simp [hp] at hb
  | some entries =>
    have hgo : buildGo entries.toArray.toBinaryHeap.size entries.toArray.toBinaryHeap = some root := by
      simpa [hp] using hb
    dsimp only [prepare] at hp
    split at hp
    · simp at hp
    · rename_i hnonempty
      let used := (frequencies.reverse.dropWhile (· == 0)).reverse
      have hn : used ≠ [] := by
        intro he
        apply hnonempty
        change used.isEmpty = true
        rw [he]
        rfl
      obtain ⟨i,hi,hactive⟩ := trimmed_has_active frequencies hn
      have hil : i < used.length := hi
      have hseeds : seeds used = entries := Option.some.inj hp
      have hiSeed : i ∈ (seeds used).flatMap (fun e => e.tree.leaves) := by
        rw [seeds_leaves]
        apply List.mem_append_left
        exact List.mem_filter.mpr ⟨List.mem_range.mpr hi,by simpa using hactive⟩
      have hmSeed : used.length ∈ (seeds used).flatMap (fun e => e.tree.leaves) := by
        rw [seeds_leaves]
        exact List.mem_append_right _ List.mem_cons_self
      have hrootI := (buildGo_mem_initial i _ entries root hgo).mpr (hseeds ▸ hiSeed)
      have hrootM := (buildGo_mem_initial used.length _ entries root hgo).mpr (hseeds ▸ hmSeed)
      cases ht : root.tree with
      | leaf symbol =>
        rw [ht] at hrootI hrootM
        simp only [Tree.leaves,List.mem_singleton] at hrootI hrootM
        omega
      | branch left right => exact ⟨left,right,rfl⟩

theorem build_depths_positive (frequencies : List Nat) (root : Entry) (hb : build frequencies = some root) :
    ∀ p ∈ root.tree.depths, 0 < p.2 := by
  obtain ⟨left,right,ht⟩ := build_is_branch frequencies root hb
  rw [ht]
  exact Tree.branch_depths_positive left right

/-- Every accepted emitted length array, not only its abstract tree, has
an exact integer Kraft sum. Absent slots contribute zero mass. -/
theorem lengths_mass (frequencies result : List Nat) (he : lengths frequencies = some result) :
    tableMass 58 result = 2^58 := by
  cases hb : build frequencies with
  | none => simp [lengths,hb] at he
  | some root =>
    obtain ⟨left,right,ht⟩ := build_is_branch frequencies root hb
    exact lengths_mass_of_branch frequencies result left right root ht hb he

/-- Every retained leaf, including the run marker, has a representable
positive length in the actual emitted table. -/
theorem lengths_leaf_active (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result)
    (symbol : Nat) (hm : symbol ∈ root.tree.leaves) :
    0 < result.getD symbol 0 ∧ result.getD symbol 0 < 59 := by
  rw [← root.tree.depths_symbols] at hm
  obtain ⟨p,hp,hindex⟩ := List.mem_map.mp hm
  have hi : p.1 < result.length := by
    rw [lengths_size frequencies result he]
    exact build_depth_indices_bounded frequencies root hb p hp
  have hlookup := lengths_leaf_depth frequencies result root hb he p hp
  have hmem : result.getD p.1 0 ∈ result := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    exact List.getElem_mem hi
  have hcap := lengths_bound frequencies result he _ hmem
  have hpositive := build_depths_positive frequencies root hb p hp
  rw [← hindex,hlookup]
  rw [hlookup] at hcap
  exact ⟨hpositive,by omega⟩

theorem lengths_active_iff (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result)
    (symbol : Nat) (hi : symbol < result.length) :
    0 < result.getD symbol 0 ↔ symbol ∈ root.tree.leaves := by
  constructor
  · intro ha
    by_contra hn
    have hz := lengths_absent frequencies result root hb he symbol hi hn
    omega
  · intro hm
    exact (lengths_leaf_active frequencies result root hb he symbol hm).1


/-- Exact support of the actual heap tree: positive used frequencies plus
one synthetic run marker, including inputs with trailing absent slots. -/
theorem build_support (frequencies : List Nat) (root : Entry) (hb : build frequencies = some root)
    (symbol : Nat) :
    symbol ∈ root.tree.leaves ↔
      (symbol < (frequencies.reverse.dropWhile (· == 0)).reverse.length ∧
        (frequencies.reverse.dropWhile (· == 0)).reverse.getD symbol 0 ≠ 0) ∨
      symbol = (frequencies.reverse.dropWhile (· == 0)).reverse.length := by
  unfold build at hb
  cases hp : prepare frequencies with
  | none => simp [hp] at hb
  | some entries =>
    have hgo : buildGo entries.toArray.toBinaryHeap.size entries.toArray.toBinaryHeap = some root := by
      simpa [hp] using hb
    dsimp only [prepare] at hp
    split at hp
    · simp at hp
    · have hseeds := Option.some.inj hp
      rw [buildGo_mem_initial symbol _ entries root hgo,← hseeds,seeds_leaves]
      simp

theorem used_eq_self (frequencies : List Nat) (hlast : frequencies.reverse.head? ≠ some 0) :
    (frequencies.reverse.dropWhile (· == 0)).reverse = frequencies := by
  rw [List.dropWhile_beq_eq_self_of_head?_ne hlast,List.reverse_reverse]

/-- An active source frequency has a positive emitted code length. For a
histogram ending at its largest source symbol, trimming changes no index. -/
theorem lengths_frequency_active (frequencies result : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (symbol : Nat) (hi : symbol < frequencies.length) (hz : frequencies.getD symbol 0 ≠ 0) :
    0 < result.getD symbol 0 ∧ result.getD symbol 0 < 59 := by
  cases hb : build frequencies with
  | none => simp [lengths,hb] at he
  | some root =>
    apply lengths_leaf_active frequencies result root hb he symbol
    rw [build_support frequencies root hb symbol,used_eq_self frequencies hlast]
    exact Or.inl ⟨hi,hz⟩

theorem lengths_marker_active (frequencies result : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0) :
    0 < result.getD frequencies.length 0 ∧ result.getD frequencies.length 0 < 59 := by
  cases hb : build frequencies with
  | none => simp [lengths,hb] at he
  | some root =>
    apply lengths_leaf_active frequencies result root hb he frequencies.length
    rw [build_support frequencies root hb frequencies.length,used_eq_self frequencies hlast]
    exact Or.inr rfl

theorem lengths_frequency_zero (frequencies result : List Nat)
    (he : lengths frequencies = some result) (hlast : frequencies.reverse.head? ≠ some 0)
    (symbol : Nat) (hi : symbol < frequencies.length) (hz : frequencies.getD symbol 0 = 0) :
    result.getD symbol 0 = 0 := by
  cases hb : build frequencies with
  | none => simp [lengths,hb] at he
  | some root =>
    apply lengths_absent frequencies result root hb he symbol (by rw [lengths_size frequencies result he]; omega)
    rw [build_support frequencies root hb symbol,used_eq_self frequencies hlast]
    intro hs
    rcases hs with hs | hs
    · exact hs.2 hz
    · omega

/-- Public expansion for use by the legacy-format canonical-code modules,
without exposing implementation bodies across the Lean module boundary. -/
theorem tableMass_eq_sum (ceiling : Nat) (result : List Nat) :
    tableMass ceiling result = (result.map (fun depth => if depth = 0 then 0 else 2^(ceiling-depth))).sum := rfl

end Exr.Piz.Frequency
