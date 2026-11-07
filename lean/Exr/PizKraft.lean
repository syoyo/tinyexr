/-
  TinyEXR - exact Kraft mass of full PIZ frequency-merge trees.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
module
public import Exr.PizHeap
import all Exr.PizHeap

public section
namespace Exr.Piz.Frequency

theorem Tree.depths_nonempty (tree : Tree) : tree.depths ≠ [] := by
  induction tree with
  | leaf symbol => simp [Tree.depths]
  | branch left right ihl _ =>
    intro he
    have he' : (left.depths ++ right.depths).map (fun p => (p.1,p.2+1)) = [] := he
    exact ihl (List.append_eq_nil_iff.mp (List.eq_nil_of_map_eq_nil he')).1

/-- Each leaf at depth d occupies 2^(ceiling-d) slots of a complete
binary tree. This is an integer form of the Kraft sum, with no rationals. -/
def Tree.mass (tree : Tree) (ceiling : Nat) : Nat :=
  (tree.depths.map (fun p => 2^(ceiling-p.2))).sum

/-- Every full binary frequency tree fills its code space exactly. This
supplies the conservation law needed for descending canonical assignment. -/
theorem Tree.mass_eq (tree : Tree) (ceiling : Nat)
    (hb : ∀ p ∈ tree.depths, p.2 ≤ ceiling) : tree.mass ceiling = 2^ceiling := by
  induction tree generalizing ceiling with
  | leaf symbol => simp [Tree.mass, Tree.depths]
  | branch left right ihl ihr =>
    have hex : ∃ p, p ∈ left.depths := by
      cases he : left.depths with
      | nil => exact False.elim (left.depths_nonempty he)
      | cons p rest => exact ⟨p,by simp⟩
    obtain ⟨p,hp⟩ := hex
    have hp' := hb (p.1,p.2+1) (List.mem_map.mpr ⟨p,List.mem_append_left _ hp,rfl⟩)
    cases ceiling with
    | zero => omega
    | succ ceiling =>
      have hl : ∀ p ∈ left.depths, p.2 ≤ ceiling := by
        intro p hp
        have h := hb (p.1,p.2+1) (List.mem_map.mpr ⟨p,List.mem_append_left _ hp,rfl⟩)
        omega
      have hr : ∀ p ∈ right.depths, p.2 ≤ ceiling := by
        intro p hp
        have h := hb (p.1,p.2+1) (List.mem_map.mpr ⟨p,List.mem_append_right _ hp,rfl⟩)
        omega
      simp only [Tree.mass, Tree.depths, List.map_map, List.map_append, List.sum_append]
      change (left.depths.map (fun p => 2^((ceiling+1)-(p.2+1)))).sum +
        (right.depths.map (fun p => 2^((ceiling+1)-(p.2+1)))).sum = 2^(ceiling+1)
      simp only [Nat.add_sub_add_right]
      change left.mass ceiling + right.mass ceiling = _
      rw [ihl ceiling hl, ihr ceiling hr, Nat.pow_succ]
      omega

/-- The actual length emitter's overlong-code guard establishes the bounded
ceiling required by the exact Kraft theorem for its constructed heap tree. -/
theorem accepted_tree_mass (frequencies result : List Nat) (root : Entry)
    (hb : build frequencies = some root) (he : lengths frequencies = some result) :
    root.tree.mass 58 = 2^58 := by
  unfold lengths at he
  simp only [hb] at he
  change (if root.tree.depths.any (fun p => p.2 > 58) then none else
    some ((root.tree.depths.foldl (fun a p => a.set! p.1 p.2)
      (Array.replicate (frequencies.length+1) 0)).toList)) = some result at he
  split at he
  · simp at he
  · rename_i hcap
    apply root.tree.mass_eq 58
    intro p hp
    by_cases hl : p.2 ≤ 58
    · exact hl
    · have ht : root.tree.depths.any (fun p => p.2 > 58) = true :=
        List.any_eq_true.mpr ⟨p,hp,by simp [show 58 < p.2 by omega]⟩
      exact False.elim (hcap ht)

end Exr.Piz.Frequency
