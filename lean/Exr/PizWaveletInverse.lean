/-
  TinyEXR - disjoint PIZ instruction commutation and traversal inversion.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizDisjoint

namespace Exr.Piz.Traversal

/-- Freeze an instruction's source-dependent writes before executing them. -/
def assignments (pair : UInt16 → UInt16 → UInt16 × UInt16)
    (cell : ((UInt16 × UInt16) × (UInt16 × UInt16)) → ((UInt16 × UInt16) × (UInt16 × UInt16))) (base width lanes lane : Nat) (op : Op) (data : Array UInt16) :
    List (Nat × UInt16) :=
  let addr := address base width lanes lane
  match op with
  | .cell x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    let c := addr (x,y+p)
    let d := addr (x+p,y+p)
    let v := cell (readCell data a b c d)
    [(a,v.1.1),(b,v.1.2),(c,v.2.1),(d,v.2.2)]
  | .horizontal x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    let v := pair data[a]! data[b]!
    [(a,v.1),(b,v.2)]
  | .vertical x y p =>
    let a := addr (x,y)
    let b := addr (x,y+p)
    let v := pair data[a]! data[b]!
    [(a,v.1),(b,v.2)]

def applyWrites (writes : List (Nat × UInt16)) (data : Array UInt16) : Array UInt16 :=
  writes.foldl (fun a w => a.set! w.1 w.2) data

theorem transform_applyWrites (pair cell) (base width lanes lane : Nat) (op : Op) (data : Array UInt16) :
    transform pair cell base width lanes lane op data =
      applyWrites (assignments pair cell base width lanes lane op data) data := by
  cases op <;> rfl

theorem assignments_addresses (pair cell) (base width lanes lane : Nat) (op : Op) (data : Array UInt16) :
    (assignments pair cell base width lanes lane op data).map Prod.fst =
      op.points.map (address base width lanes lane) := by
  cases op <;> rfl

theorem assignments_congr (pair cell) (base width lanes lane : Nat) (op : Op) (a b : Array UInt16)
    (he : ∀ point ∈ op.points, a[address base width lanes lane point]! = b[address base width lanes lane point]!) :
    assignments pair cell base width lanes lane op a = assignments pair cell base width lanes lane op b := by
  cases op with
  | cell x y p =>
    have h1 := he (x,y) (by simp [Op.points])
    have h2 := he (x+p,y) (by simp [Op.points])
    have h3 := he (x,y+p) (by simp [Op.points])
    have h4 := he (x+p,y+p) (by simp [Op.points])
    simp only [assignments,readCell,h1,h2,h3,h4]
  | horizontal x y p =>
    have h1 := he (x,y) (by simp [Op.points])
    have h2 := he (x+p,y) (by simp [Op.points])
    simp only [assignments,h1,h2]
  | vertical x y p =>
    have h1 := he (x,y) (by simp [Op.points])
    have h2 := he (x,y+p) (by simp [Op.points])
    simp only [assignments,h1,h2]

theorem set_write_comm (data : Array UInt16) (a b : Nat) (x y : UInt16) (hne : a ≠ b) :
    (data.set! a x).set! b y = (data.set! b y).set! a x :=
  Array.setIfInBounds_comm x y hne

theorem applyWrites_set_comm (writes : List (Nat × UInt16)) (data : Array UInt16)
    (i : Nat) (value : UInt16) (hn : ∀ w ∈ writes, w.1 ≠ i) :
    applyWrites writes (data.set! i value) = (applyWrites writes data).set! i value := by
  induction writes generalizing data with
  | nil => rfl
  | cons w rest ih =>
    simp only [applyWrites,List.foldl_cons]
    rw [set_write_comm data i w.1 value w.2 (Ne.symm (hn w List.mem_cons_self))]
    exact ih (data.set! w.1 w.2) (fun w hw => hn w (List.mem_cons_of_mem _ hw))

theorem applyWrites_comm (a b : List (Nat × UInt16)) (data : Array UInt16)
    (hn : ∀ x ∈ a, ∀ y ∈ b, x.1 ≠ y.1) :
    applyWrites a (applyWrites b data) = applyWrites b (applyWrites a data) := by
  induction b generalizing data with
  | nil => rfl
  | cons w rest ih =>
    change applyWrites a (applyWrites rest (data.set! w.1 w.2)) =
      applyWrites rest ((applyWrites a data).set! w.1 w.2)
    rw [ih (data.set! w.1 w.2) (fun x hx y hy => hn x hx y (List.mem_cons_of_mem _ hy)),
      applyWrites_set_comm a data w.1 w.2 (fun x hx => hn x hx w List.mem_cons_self)]

/-- Disjoint instructions commute even when they use different lifting
kernels, because neither changes the other's source values or writes. -/
theorem transform_comm (pairA cellA pairB cellB) (base width lanes lane : Nat)
    (opA opB : Op) (data : Array UInt16)
    (hd : ∀ x ∈ opA.points, ∀ y ∈ opB.points,
      address base width lanes lane x ≠ address base width lanes lane y) :
    transform pairA cellA base width lanes lane opA
      (transform pairB cellB base width lanes lane opB data) =
    transform pairB cellB base width lanes lane opB
      (transform pairA cellA base width lanes lane opA data) := by
  have hA := assignments_congr pairA cellA base width lanes lane opA
    (transform pairB cellB base width lanes lane opB data) data (by
      intro x hx
      apply transform_read_other
      intro y hy
      exact Ne.symm (hd x hx y hy))
  have hB := assignments_congr pairB cellB base width lanes lane opB
    (transform pairA cellA base width lanes lane opA data) data (by
      intro y hy
      apply transform_read_other
      intro x hx
      exact hd x hx y hy)
  conv_lhs => rw [transform_applyWrites,hA]
  conv_rhs => rw [transform_applyWrites,hB]
  rw [transform_applyWrites,transform_applyWrites]
  apply applyWrites_comm
  intro a ha b hb
  have ha' : a.1 ∈ (opA.points.map (address base width lanes lane)) := by
    rw [← assignments_addresses pairA cellA base width lanes lane opA data]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have hb' : b.1 ∈ (opB.points.map (address base width lanes lane)) := by
    rw [← assignments_addresses pairB cellB base width lanes lane opB data]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  obtain ⟨x,hx,hxa⟩ := List.mem_map.mp ha'
  obtain ⟨y,hy,hyb⟩ := List.mem_map.mp hb'
  rw [← hxa,← hyb]
  exact hd x hx y hy

theorem transform_fold_comm (pairA cellA pairB cellB) (base width lanes lane : Nat)
    (head : Op) (ops : List Op) (data : Array UInt16)
    (hd : ∀ op ∈ ops, ∀ x ∈ head.points, ∀ y ∈ op.points,
      address base width lanes lane x ≠ address base width lanes lane y) :
    transform pairA cellA base width lanes lane head
      (ops.foldl (fun a op => transform pairB cellB base width lanes lane op a) data) =
    ops.foldl (fun a op => transform pairB cellB base width lanes lane op a)
      (transform pairA cellA base width lanes lane head data) := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hd q (List.mem_cons_of_mem _ hq))]
    rw [transform_comm pairA cellA pairB cellB base width lanes lane head op data
      (hd op List.mem_cons_self)]

/-- Disjoint operations can be decoded in the same order in which they were
encoded. This matches the actual C decoder's order within each level. -/
theorem transform16_fold_same_order_inverse (base width height lanes lane : Nat) (ops : List Op)
    (data : Array UInt16) (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hv : ∀ op ∈ ops, op.Valid width height)
    (hd : ops.Pairwise (fun a b => ∀ x ∈ a.points, ∀ y ∈ b.points,
      address base width lanes lane x ≠ address base width lanes lane y)) :
    ops.foldl (fun a op => transform wdec16 (decodeCell wdec16) base width lanes lane op a)
      (ops.foldl (fun a op => transform wenc16 (encodeCell wenc16) base width lanes lane op a) data) = data := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    have hdis := List.pairwise_cons.mp hd
    simp only [List.foldl_cons]
    rw [transform_fold_comm wdec16 (decodeCell wdec16) wenc16 (encodeCell wenc16)
      base width lanes lane op rest _ hdis.1]
    rw [transform16_inverse base width height lanes lane op data hl ha (hv op List.mem_cons_self)]
    exact ih data ha (fun q hq => hv q (List.mem_cons_of_mem _ hq)) hdis.2

theorem level16_inverse (base width height lanes lane p : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hp : 0 < p) :
    (level width height p).foldl (fun a op => transform wdec16 (decodeCell wdec16) base width lanes lane op a)
      ((level width height p).foldl (fun a op => transform wenc16 (encodeCell wenc16) base width lanes lane op a) data) = data :=
  transform16_fold_same_order_inverse base width height lanes lane _ data hl ha
    (level_valid width height p hp) (level_addresses_disjoint base width height lanes lane p hl hp)

/-- One guarded full-range pass, factored only to state the multilevel
composition theorem; it executes the existing level operations unchanged. -/
def pass16 (decode : Bool) (base width height lanes lane k : Nat) (data : Array UInt16) : Array UInt16 :=
  if 2*2^k ≤ min width height then
    if decode then
      (level width height (2^k)).foldl (fun a op => transform wdec16 (decodeCell wdec16) base width lanes lane op a) data
    else
      (level width height (2^k)).foldl (fun a op => transform wenc16 (encodeCell wenc16) base width lanes lane op a) data
  else data

theorem pass16_size (decode : Bool) (base width height lanes lane k : Nat) (data : Array UInt16) :
    (pass16 decode base width height lanes lane k data).size = data.size := by
  unfold pass16
  split
  · split <;> exact transform_fold_size _ _ base width lanes lane _ data
  · rfl

theorem pass16_inverse (base width height lanes lane k : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) :
    pass16 true base width height lanes lane k (pass16 false base width height lanes lane k data) = data := by
  by_cases hk : 2*2^k ≤ min width height
  · simp only [pass16,hk,ite_true,Bool.false_eq_true,ite_false]
    exact level16_inverse base width height lanes lane (2^k) data hl ha (Nat.two_pow_pos k)
  · simp only [pass16,hk,ite_false]

theorem passes16_inverse (base width height lanes lane : Nat) (levels : List Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) :
    levels.reverse.foldl (fun a k => pass16 true base width height lanes lane k a)
      (levels.foldl (fun a k => pass16 false base width height lanes lane k a) data) = data := by
  induction levels generalizing data with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih _ (by simpa only [pass16_size] using ha)]
    exact pass16_inverse base width height lanes lane k data hl ha

/-- The complete executable full-range traversal is inverse, with the C's
actual within-level order, odd edges, strided lanes and nonzero bases. -/
theorem run16_inverse (base width height lanes lane : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) :
    run true false base width height lanes lane (run false false base width height lanes lane data) = data := by
  have hi := passes16_inverse base width height lanes lane (List.range (min width height)) data hl ha
  simpa only [run,pass16,Bool.false_eq_true,ite_false,ite_true] using hi

/-- The 14-bit level inverse needs small-range inputs only at points touched
by that level; disjointness keeps those inputs independent of other cells. -/
theorem transform14_fold_same_order_inverse (base width height lanes lane : Nat) (ops : List Op)
    (data : Array UInt16) (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hv : ∀ op ∈ ops, op.Valid width height)
    (hd : ops.Pairwise (fun a b => ∀ x ∈ a.points, ∀ y ∈ b.points,
      address base width lanes lane x ≠ address base width lanes lane y))
    (hs : ∀ op ∈ ops, ∀ point ∈ op.points, data[address base width lanes lane point]! < 16384) :
    ops.foldl (fun a op => transform wdec14 (decodeCell wdec14) base width lanes lane op a)
      (ops.foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) data) = data := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    have hdis := List.pairwise_cons.mp hd
    simp only [List.foldl_cons]
    rw [transform_fold_comm wdec14 (decodeCell wdec14) wenc14 (encodeCell wenc14)
      base width lanes lane op rest _ hdis.1]
    rw [transform14_inverse base width height lanes lane op data hl ha
      (hv op List.mem_cons_self) (hs op List.mem_cons_self)]
    exact ih data ha (fun q hq => hv q (List.mem_cons_of_mem _ hq)) hdis.2
      (fun q hq => hs q (List.mem_cons_of_mem _ hq))

theorem level14_inverse (base width height lanes lane p : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hp : 0 < p)
    (hs : ∀ op ∈ level width height p, ∀ point ∈ op.points,
      data[address base width lanes lane point]! < 16384) :
    (level width height p).foldl (fun a op => transform wdec14 (decodeCell wdec14) base width lanes lane op a)
      ((level width height p).foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) data) = data :=
  transform14_fold_same_order_inverse base width height lanes lane _ data hl ha
    (level_valid width height p hp) (level_addresses_disjoint base width height lanes lane p hl hp) hs

/-- Only low-pass outputs survive into the next multilevel pass. -/
theorem wenc14_low_bound (a b : UInt16) (ha : a < 16384) (hb : b < 16384) :
    (wenc14 a b).1 < 16384 := by
  dsimp only [wenc14,signed]
  bv_decide

theorem encodeCell14_low_bound (a b c d : UInt16)
    (ha : a < 16384) (hb : b < 16384) (hc : c < 16384) (hd : d < 16384) :
    (encodeCell wenc14 ((a,b),(c,d))).1.1 < 16384 := by
  exact wenc14_low_bound _ _ (wenc14_low_bound a b ha hb) (wenc14_low_bound c d hc hd)

end Exr.Piz.Traversal
