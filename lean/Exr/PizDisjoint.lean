/-
  TinyEXR - disjoint cell and odd-edge support within PIZ wavelet levels.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizWavelet

namespace Exr.Piz.Traversal

def Op.origin : Op → Point
  | .cell x y _ | .horizontal x y _ | .vertical x y _ => (x,y)

def Op.step : Op → Nat
  | .cell _ _ p | .horizontal _ _ p | .vertical _ _ p => p

/-- Row-major operations occupy different blocks, with a gap between the
last touched coordinate of one block and the next block's origin. -/
def Op.Separated (p : Nat) (a b : Op) : Prop :=
  a.origin.2+p < b.origin.2 ∨
    (a.origin.2 = b.origin.2 ∧ a.origin.1+p < b.origin.1)

theorem block_gap (p i j : Nat) (hp : 0 < p) (hij : i < j) :
    i*(2*p)+p < j*(2*p) := by
  have hm := Nat.mul_le_mul_right (2*p) (show i+1 ≤ j by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

theorem range_pairwise (n : Nat) : (List.range n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

theorem rowOps_origin (width y p : Nat) (op : Op) (ho : op ∈ rowOps width y p) :
    op.origin.2 = y ∧ op.step = p := by
  unfold rowOps at ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ho
    exact ⟨rfl,rfl⟩
  · split at ho
    · simp only [List.mem_singleton] at ho
      subst op
      exact ⟨rfl,rfl⟩
    · simp at ho

theorem rowOps_separated (width y p : Nat) (hp : 0 < p) :
    (rowOps width y p).Pairwise (Op.Separated p) := by
  rw [rowOps,List.pairwise_append]
  refine ⟨?_,?_,?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (range_pairwise (width/(2*p)))
    intro i j hij
    exact Or.inr ⟨rfl,block_gap p i j hp hij⟩
  · split <;> simp
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    split at hb
    · simp only [List.mem_singleton] at hb
      subst b
      exact Or.inr ⟨rfl,block_gap p i (width/(2*p)) hp (List.mem_range.mp hi)⟩
    · simp at hb

theorem level_steps (width height p : Nat) (op : Op) (ho : op ∈ level width height p) :
    op.step = p := by
  unfold level at ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨j,_,ho⟩ := List.mem_flatMap.mp ho
    exact (rowOps_origin width (j*(2*p)) p op ho).2
  · split at ho
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ho
      rfl
    · simp at ho

/-- The generated level is separated in its actual C row-major order,
including the right column and bottom row of an odd image. -/
theorem level_separated (width height p : Nat) (hp : 0 < p) :
    (level width height p).Pairwise (Op.Separated p) := by
  rw [level,List.pairwise_append]
  refine ⟨?_,?_,?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun j _ => rowOps_separated width (j*(2*p)) p hp,?_⟩
    refine List.Pairwise.imp ?_ (range_pairwise (height/(2*p)))
    intro i j hij a ha b hb
    have hya := (rowOps_origin width (i*(2*p)) p a ha).1
    have hyb := (rowOps_origin width (j*(2*p)) p b hb).1
    exact Or.inl (by rw [hya,hyb]; exact block_gap p i j hp hij)
  · split
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (range_pairwise (width/(2*p)))
      intro i j hij
      exact Or.inr ⟨rfl,block_gap p i j hp hij⟩
    · simp
  · intro a ha b hb
    obtain ⟨j,hj,ha⟩ := List.mem_flatMap.mp ha
    have hya := (rowOps_origin width (j*(2*p)) p a ha).1
    split at hb
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
      exact Or.inl (by rw [hya]; exact block_gap p j (height/(2*p)) hp (List.mem_range.mp hj))
    · simp at hb

theorem Op.points_rectangle (op : Op) (point : Point) (hp : point ∈ op.points) :
    op.origin.1 ≤ point.1 ∧ point.1 ≤ op.origin.1+op.step ∧
      op.origin.2 ≤ point.2 ∧ point.2 ≤ op.origin.2+op.step := by
  cases op with
  | cell x y p =>
    simp only [Op.points,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [Op.origin,Op.step]
  | horizontal x y p =>
    simp only [Op.points,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> simp [Op.origin,Op.step]
  | vertical x y p =>
    simp only [Op.points,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> simp [Op.origin,Op.step]

theorem separated_points_ne (p : Nat) (a b : Op) (ha : a.step = p) (hb : b.step = p)
    (hs : a.Separated p b) (x y : Point) (hx : x ∈ a.points) (hy : y ∈ b.points) : x ≠ y := by
  have hxa := a.points_rectangle x hx
  have hyb := b.points_rectangle y hy
  rw [ha] at hxa
  rw [hb] at hyb
  intro he
  subst y
  unfold Op.Separated at hs
  omega

/-- Distinct operations in one actual level never read or write the same
point. No validity assumption or omission of odd edges is needed. -/
theorem level_points_disjoint (width height p : Nat) (hp : 0 < p) :
    (level width height p).Pairwise (fun a b => ∀ x ∈ a.points, ∀ y ∈ b.points, x ≠ y) := by
  refine List.Pairwise.imp_of_mem ?_ (level_separated width height p hp)
  intro a b ha hb hs x hx y hy
  exact separated_points_ne p a b (level_steps width height p a ha)
    (level_steps width height p b hb) hs x y hx hy

theorem level_addresses_disjoint (base width height lanes lane p : Nat)
    (hl : lane < lanes) (hp : 0 < p) :
    (level width height p).Pairwise (fun a b => ∀ x ∈ a.points, ∀ y ∈ b.points,
      address base width lanes lane x ≠ address base width lanes lane y) := by
  refine List.Pairwise.imp_of_mem ?_ (level_points_disjoint width height p hp)
  intro a b ha hb hdis x hx y hy he
  have hxa := Op.points_bounded (level_valid width height p hp a ha) x hx
  have hyb := Op.points_bounded (level_valid width height p hp b hb) y hy
  exact hdis x hx y hy (address_injective base width lanes lane hl x y hxa.1 hyb.1 he)

end Exr.Piz.Traversal
