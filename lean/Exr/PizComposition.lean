/-
  TinyEXR - channel/lane composition of executable PIZ wavelet inverses.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizSmallRange
import Exr.PizLayout

namespace Exr.Piz.Composition
open Traversal Layout

structure Task where
  base : Nat
  width : Nat
  height : Nat
  lanes : Nat
  lane : Nat
  deriving Repr, DecidableEq

def Task.addr (task : Task) : Point → Nat := address task.base task.width task.lanes task.lane

def Task.Valid (task : Task) : Prop := task.lane < task.lanes

def Task.Contains (task : Task) (point : Point) : Prop := point.1 < task.width ∧ point.2 < task.height

def Task.Disjoint (a b : Task) : Prop :=
  ∀ x, a.Contains x → ∀ y, b.Contains y → a.addr x ≠ b.addr y

def Task.run (task : Task) (decode small : Bool) (data : Array UInt16) : Array UInt16 :=
  Traversal.run decode small task.base task.width task.height task.lanes task.lane data

/-- Instruction commutation across different channel bases, shapes or lanes. -/
theorem transform_across_comm (pairA cellA pairB cellB) (a b : Task) (opA opB : Op)
    (data : Array UInt16)
    (hd : ∀ x ∈ opA.points, ∀ y ∈ opB.points, a.addr x ≠ b.addr y) :
    transform pairA cellA a.base a.width a.lanes a.lane opA
      (transform pairB cellB b.base b.width b.lanes b.lane opB data) =
    transform pairB cellB b.base b.width b.lanes b.lane opB
      (transform pairA cellA a.base a.width a.lanes a.lane opA data) := by
  have hA := assignments_congr pairA cellA a.base a.width a.lanes a.lane opA
    (transform pairB cellB b.base b.width b.lanes b.lane opB data) data (by
      intro x hx
      apply transform_read_other
      intro y hy
      exact Ne.symm (hd x hx y hy))
  have hB := assignments_congr pairB cellB b.base b.width b.lanes b.lane opB
    (transform pairA cellA a.base a.width a.lanes a.lane opA data) data (by
      intro y hy
      apply transform_read_other
      intro x hx
      exact hd x hx y hy)
  conv_lhs => rw [transform_applyWrites,hA]
  conv_rhs => rw [transform_applyWrites,hB]
  rw [transform_applyWrites,transform_applyWrites]
  apply applyWrites_comm
  intro wa ha wb hb
  have ha' : wa.1 ∈ opA.points.map a.addr := by
    dsimp only [Task.addr]
    rw [← assignments_addresses pairA cellA a.base a.width a.lanes a.lane opA data]
    exact List.mem_map.mpr ⟨wa,ha,rfl⟩
  have hb' : wb.1 ∈ opB.points.map b.addr := by
    dsimp only [Task.addr]
    rw [← assignments_addresses pairB cellB b.base b.width b.lanes b.lane opB data]
    exact List.mem_map.mpr ⟨wb,hb,rfl⟩
  obtain ⟨x,hx,hxa⟩ := List.mem_map.mp ha'
  obtain ⟨y,hy,hyb⟩ := List.mem_map.mp hb'
  rw [← hxa,← hyb]
  exact hd x hx y hy

def operations (decode : Bool) (width height : Nat) : List Op :=
  (if decode then (List.range (min width height)).reverse else List.range (min width height)).flatMap
    (fun k => if 2*2^k ≤ min width height then level width height (2^k) else [])

def pairFor (decode small : Bool) : UInt16 → UInt16 → UInt16 × UInt16 :=
  if decode then (if small then wdec14 else wdec16) else (if small then wenc14 else wenc16)

def cellFor (decode small : Bool) :=
  if decode then decodeCell (pairFor decode small) else encodeCell (pairFor decode small)

theorem operations_valid (decode : Bool) (width height : Nat) :
    ∀ op ∈ operations decode width height, op.Valid width height := by
  intro op ho
  obtain ⟨k,_,ho⟩ := List.mem_flatMap.mp ho
  split at ho
  · exact level_valid width height (2^k) (Nat.two_pow_pos k) op ho
  · simp at ho

theorem run_eq_fold (decode small : Bool) (task : Task) (data : Array UInt16) :
    task.run decode small data =
      (operations decode task.width task.height).foldl
        (fun a op => transform (pairFor decode small) (cellFor decode small)
          task.base task.width task.lanes task.lane op a) data := by
  unfold Task.run Traversal.run operations
  rw [List.foldl_flatMap]
  dsimp only [pairFor,cellFor]
  congr 1
  funext a k
  split <;> rfl

theorem transform_across_fold_comm (pairA cellA pairB cellB) (a b : Task) (head : Op)
    (ops : List Op) (data : Array UInt16)
    (hd : ∀ op ∈ ops, ∀ x ∈ head.points, ∀ y ∈ op.points, a.addr x ≠ b.addr y) :
    transform pairA cellA a.base a.width a.lanes a.lane head
      (ops.foldl (fun data op => transform pairB cellB b.base b.width b.lanes b.lane op data) data) =
    ops.foldl (fun data op => transform pairB cellB b.base b.width b.lanes b.lane op data)
      (transform pairA cellA a.base a.width a.lanes a.lane head data) := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hd q (List.mem_cons_of_mem _ hq))]
    rw [transform_across_comm pairA cellA pairB cellB a b head op data (hd op List.mem_cons_self)]

theorem folds_across_comm (pairA cellA pairB cellB) (a b : Task) (opsA opsB : List Op)
    (data : Array UInt16)
    (hd : ∀ opA ∈ opsA, ∀ opB ∈ opsB, ∀ x ∈ opA.points, ∀ y ∈ opB.points, a.addr x ≠ b.addr y) :
    opsA.foldl (fun data op => transform pairA cellA a.base a.width a.lanes a.lane op data)
      (opsB.foldl (fun data op => transform pairB cellB b.base b.width b.lanes b.lane op data) data) =
    opsB.foldl (fun data op => transform pairB cellB b.base b.width b.lanes b.lane op data)
      (opsA.foldl (fun data op => transform pairA cellA a.base a.width a.lanes a.lane op data) data) := by
  induction opsA generalizing data with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    rw [transform_across_fold_comm pairA cellA pairB cellB a b op opsB data (hd op List.mem_cons_self)]
    exact ih _ (fun q hq => hd q (List.mem_cons_of_mem _ hq))

/-- Complete traversals commute across disjoint channels or word lanes. -/
theorem Task.run_comm (a b : Task) (decodeA smallA decodeB smallB : Bool) (data : Array UInt16)
    (hd : a.Disjoint b) :
    a.run decodeA smallA (b.run decodeB smallB data) = b.run decodeB smallB (a.run decodeA smallA data) := by
  simp only [run_eq_fold]
  apply folds_across_comm
  intro opA hA opB hB x hx y hy
  exact hd x (Op.points_bounded (operations_valid decodeA a.width a.height opA hA) x hx)
    y (Op.points_bounded (operations_valid decodeB b.width b.height opB hB) y hy)

def Task.finish (task : Task) : Nat := task.base+task.height*task.width*task.lanes

def planeTasks (base : Nat) (plane : Plane) : List Task :=
  (List.range plane.lanes).map (fun lane => ⟨base,plane.width,plane.rows.length,plane.lanes,lane⟩)

def tasksGo : Nat → List Plane → List Task
  | _,[] => []
  | base,plane::rest => planeTasks base plane ++ tasksGo (base+plane.wordCount) rest

theorem tasksGo_bounds (base : Nat) (planes : List Plane) :
    ∀ task ∈ tasksGo base planes, base ≤ task.base ∧ task.finish ≤ base+wordCount planes ∧ task.Valid := by
  induction planes generalizing base with
  | nil => simp [tasksGo]
  | cons plane rest ih =>
    intro task ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp ht
      have hl' := List.mem_range.mp hl
      simp only [Task.finish,Task.Valid,wordCount,List.map_cons,List.sum_cons,Plane.wordCount]
      omega
    · have hb := ih (base+plane.wordCount) task ht
      simp only [wordCount,List.map_cons,List.sum_cons] at *
      exact ⟨by omega,by omega,hb.2.2⟩

theorem planeTasks_disjoint (base : Nat) (plane : Plane) :
    (planeTasks base plane).Pairwise Task.Disjoint := by
  rw [planeTasks,List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (range_pairwise plane.lanes)
  intro i j hi hj hij x _ y _ he
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  change address base plane.width plane.lanes i x = address base plane.width plane.lanes j y at he
  have hp : (x.2*plane.width+x.1)*plane.lanes+i = (y.2*plane.width+y.1)*plane.lanes+j := by
    simp only [address] at he
    omega
  have hm := congrArg (fun n => n % plane.lanes) hp
  rw [Nat.mul_add_mod_of_lt hi',Nat.mul_add_mod_of_lt hj'] at hm
  omega

theorem tasksGo_disjoint (base : Nat) (planes : List Plane) :
    (tasksGo base planes).Pairwise Task.Disjoint := by
  induction planes generalizing base with
  | nil => simp [tasksGo]
  | cons plane rest ih =>
    rw [tasksGo,List.pairwise_append]
    refine ⟨planeTasks_disjoint base plane,ih (base+plane.wordCount),?_⟩
    intro a ha b hb
    obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp ha
    have hb' := tasksGo_bounds (base+plane.wordCount) rest b hb
    intro x hx y _ he
    have hu := address_bounded base plane.width plane.rows.length plane.lanes lane x hx.1 hx.2 (List.mem_range.mp hl)
    have hlo : b.base ≤ b.addr y := by simp only [Task.addr,address]; omega
    change address base plane.width plane.lanes lane x = b.addr y at he
    simp only [Plane.wordCount] at hb'
    omega

theorem waveletGo_eq_tasks (decode small : Bool) (base : Nat) (planes : List Plane) (data : Array UInt16) :
    Layout.waveletGo decode small base planes data =
      (tasksGo base planes).foldl (fun a task => task.run decode small a) data := by
  induction planes generalizing base data with
  | nil => rfl
  | cons plane rest ih =>
    simp only [Layout.waveletGo,tasksGo,List.foldl_append,ih,planeTasks,List.foldl_map,Task.run]

/-- Each generated task has the source bounds needed for its selected mode,
without requiring already-transformed neighboring tasks to remain small. -/
theorem Task.run_inverse (task : Task) (small : Bool) (data : Array UInt16)
    (hv : task.Valid) (ha : task.finish ≤ data.size)
    (hs : small = true → ∀ i, i < data.size → data[i]! < 16384) :
    task.run true small (task.run false small data) = data := by
  apply Traversal.run_inverse
  · exact hv
  · exact ha
  · intro hsmall point hx hy
    have hb := address_bounded task.base task.width task.height task.lanes task.lane point hx hy hv
    exact hs hsmall _ (Nat.lt_of_lt_of_le hb ha)

theorem Task.run_fold_comm (head : Task) (tasks : List Task) (decodeA smallA decodeB smallB : Bool)
    (data : Array UInt16) (hd : ∀ task ∈ tasks, head.Disjoint task) :
    head.run decodeA smallA (tasks.foldl (fun a task => task.run decodeB smallB a) data) =
      tasks.foldl (fun a task => task.run decodeB smallB a) (head.run decodeA smallA data) := by
  induction tasks generalizing data with
  | nil => rfl
  | cons task rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun task ht => hd task (List.mem_cons_of_mem _ ht))]
    rw [Task.run_comm head task decodeA smallA decodeB smallB data (hd task List.mem_cons_self)]

theorem tasks_inverse (tasks : List Task) (small : Bool) (data : Array UInt16)
    (hv : ∀ task ∈ tasks, task.Valid) (ha : ∀ task ∈ tasks, task.finish ≤ data.size)
    (hd : tasks.Pairwise Task.Disjoint)
    (hs : small = true → ∀ i, i < data.size → data[i]! < 16384) :
    tasks.foldl (fun a task => task.run true small a)
      (tasks.foldl (fun a task => task.run false small a) data) = data := by
  induction tasks generalizing data with
  | nil => rfl
  | cons task rest ih =>
    have hdis := List.pairwise_cons.mp hd
    simp only [List.foldl_cons]
    rw [Task.run_fold_comm task rest true small false small _ hdis.1]
    rw [Task.run_inverse task small data (hv task List.mem_cons_self) (ha task List.mem_cons_self) hs]
    exact ih data (fun t ht => hv t (List.mem_cons_of_mem _ ht))
      (fun t ht => ha t (List.mem_cons_of_mem _ ht)) hdis.2 hs

/-- Complete multi-channel and multi-lane planar wavelet composition, in the
same channel/lane order used by the C codec, for both lifting modes. -/
theorem waveletGo_inverse (small : Bool) (base : Nat) (planes : List Plane) (data : Array UInt16)
    (ha : base+wordCount planes ≤ data.size)
    (hs : small = true → ∀ i, i < data.size → data[i]! < 16384) :
    Layout.waveletGo true small base planes (Layout.waveletGo false small base planes data) = data := by
  rw [waveletGo_eq_tasks,waveletGo_eq_tasks]
  apply tasks_inverse
  · intro task ht
    exact (tasksGo_bounds base planes task ht).2.2
  · intro task ht
    exact Nat.le_trans (tasksGo_bounds base planes task ht).2.1 ha
  · exact tasksGo_disjoint base planes
  · exact hs

end Exr.Piz.Composition
