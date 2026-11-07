/-
  TinyEXR - small-range PIZ low-pass lattice invariants.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizWaveletInverse

namespace Exr.Piz.Traversal

def Grid (step : Nat) (point : Point) : Prop := step ∣ point.1 ∧ step ∣ point.2

def Op.Aligned (step : Nat) (op : Op) : Prop := op.step = step ∧ Grid (2*step) op.origin

/-- Only points of this lattice are inputs to the next lifting level. -/
def SmallGrid (base width height lanes lane step : Nat) (data : Array UInt16) : Prop :=
  ∀ point, point.1 < width → point.2 < height → Grid step point →
    data[address base width lanes lane point]! < 16384

theorem grid_coarsen (p : Nat) (point : Point) (hg : Grid (2*p) point) : Grid p point :=
  ⟨Nat.dvd_trans (Nat.dvd_mul_left p 2) hg.1, Nat.dvd_trans (Nat.dvd_mul_left p 2) hg.2⟩

theorem smallGrid_coarsen (base width height lanes lane p : Nat) (data : Array UInt16)
    (hs : SmallGrid base width height lanes lane p data) :
    SmallGrid base width height lanes lane (2*p) data :=
  fun point hx hy hg => hs point hx hy (grid_coarsen p point hg)

theorem rowOps_aligned (width j p : Nat) (op : Op) (ho : op ∈ rowOps width (j*(2*p)) p) :
    op.Aligned p := by
  unfold rowOps at ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ho
    exact ⟨rfl,Nat.dvd_mul_left _ _,Nat.dvd_mul_left _ _⟩
  · split at ho
    · simp only [List.mem_singleton] at ho
      subst op
      exact ⟨rfl,Nat.dvd_mul_left _ _,Nat.dvd_mul_left _ _⟩
    · simp at ho

theorem level_aligned (width height p : Nat) (op : Op) (ho : op ∈ level width height p) :
    op.Aligned p := by
  unfold level at ho
  rcases List.mem_append.mp ho with ho | ho
  · obtain ⟨j,_,ho⟩ := List.mem_flatMap.mp ho
    exact rowOps_aligned width j p op ho
  · split at ho
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ho
      exact ⟨rfl,Nat.dvd_mul_left _ _,Nat.dvd_mul_left _ _⟩
    · simp at ho

theorem Op.point_endpoints (op : Op) (point : Point) (hp : point ∈ op.points) :
    (point.1 = op.origin.1 ∨ point.1 = op.origin.1+op.step) ∧
      (point.2 = op.origin.2 ∨ point.2 = op.origin.2+op.step) := by
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

theorem aligned_points_grid (p : Nat) (op : Op) (ha : op.Aligned p)
    (point : Point) (hp : point ∈ op.points) : Grid p point := by
  have hg := grid_coarsen p op.origin ha.2
  have he := op.point_endpoints point hp
  rw [ha.1] at he
  constructor
  · rcases he.1 with hx | hx
    · rw [hx]; exact hg.1
    · rw [hx]; exact Nat.dvd_add hg.1 (Nat.dvd_refl p)
  · rcases he.2 with hy | hy
    · rw [hy]; exact hg.2
    · rw [hy]; exact Nat.dvd_add hg.2 (Nat.dvd_refl p)

/-- A point on the coarser lattice can only be the low-pass origin of an
aligned instruction. High-pass endpoints cannot survive into that lattice. -/
theorem aligned_coarse_origin (p : Nat) (hp : 0 < p) (op : Op) (ha : op.Aligned p)
    (point : Point) (hm : point ∈ op.points) (hg : Grid (2*p) point) : point = op.origin := by
  have hr := op.points_rectangle point hm
  rw [ha.1] at hr
  have hx := Nat.dvd_sub hg.1 ha.2.1
  have hy := Nat.dvd_sub hg.2 ha.2.2
  have hxe : point.1 = op.origin.1 := by
    by_contra hn
    have hh := Nat.le_of_dvd (by omega : 0 < point.1-op.origin.1) hx
    omega
  have hye : point.2 = op.origin.2 := by
    by_contra hn
    have hh := Nat.le_of_dvd (by omega : 0 < point.2-op.origin.2) hy
    omega
  exact Prod.ext hxe hye

theorem level_sources_small (base width height lanes lane p : Nat) (data : Array UInt16)
    (hp : 0 < p) (hs : SmallGrid base width height lanes lane p data) :
    ∀ op ∈ level width height p, ∀ point ∈ op.points,
      data[address base width lanes lane point]! < 16384 := by
  intro op ho point hm
  have hv := Op.points_bounded (level_valid width height p hp op ho) point hm
  exact hs point hv.1 hv.2 (aligned_points_grid p op (level_aligned width height p op ho) point hm)

/-- Every instruction's stored low-pass origin stays in the small range
when its source points are small. Bounds and distinctness come from geometry. -/
theorem transform14_origin_small (base width height lanes lane : Nat) (op : Op) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hv : op.Valid width height)
    (hs : ∀ point ∈ op.points, data[address base width lanes lane point]! < 16384) :
    (transform wenc14 (encodeCell wenc14) base width lanes lane op data)[address base width lanes lane op.origin]! < 16384 := by
  have hn := op_addresses_nodup base width height lanes lane hl op hv
  have hb : ∀ point ∈ op.points, address base width lanes lane point < data.size := by
    intro point hm
    have hxy := Op.points_bounded hv point hm
    exact Nat.lt_of_lt_of_le (address_bounded base width height lanes lane point hxy.1 hxy.2 hl) ha
  let addr := address base width lanes lane
  cases op with
  | cell x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    let c := addr (x,y+p)
    let d := addr (x+p,y+p)
    have hr : readCell (cellStep (encodeCell wenc14) a b c d data) a b c d =
        encodeCell wenc14 (readCell data a b c d) := by
      apply storeCell_read
      all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points,a,b,c,d,addr]
    rw [transform_cell_eq]
    change (cellStep (encodeCell wenc14) a b c d data)[a]! < 16384
    have he := congrArg (fun v => v.1.1) hr
    dsimp only [readCell] at he
    rw [he]
    apply encodeCell14_low_bound
    all_goals exact hs _ (by simp [Op.points])
  | horizontal x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    have hr : (pairStep wenc14 a b data)[a]! = (wenc14 data[a]! data[b]!).1 := by
      apply (storePair_read data a b _ ?_ ?_ ?_).1
      all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points,a,b,addr]
    rw [transform_horizontal_eq]
    change (pairStep wenc14 a b data)[a]! < 16384
    rw [hr]
    apply wenc14_low_bound
    all_goals exact hs _ (by simp [Op.points])
  | vertical x y p =>
    let a := addr (x,y)
    let b := addr (x,y+p)
    have hr : (pairStep wenc14 a b data)[a]! = (wenc14 data[a]! data[b]!).1 := by
      apply (storePair_read data a b _ ?_ ?_ ?_).1
      all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points,a,b,addr]
    rw [transform_vertical_eq]
    change (pairStep wenc14 a b data)[a]! < 16384
    rw [hr]
    apply wenc14_low_bound
    all_goals exact hs _ (by simp [Op.points])

/-- Aligned high-pass endpoints are outside the next level's lattice, so
an individual instruction preserves small values on that coarser lattice. -/
theorem transform14_coarse_grid (base width height lanes lane p : Nat) (op : Op) (data : Array UInt16)
    (hp : 0 < p) (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hv : op.Valid width height) (hal : op.Aligned p)
    (hs : ∀ point ∈ op.points, data[address base width lanes lane point]! < 16384)
    (hg : SmallGrid base width height lanes lane (2*p) data) :
    SmallGrid base width height lanes lane (2*p)
      (transform wenc14 (encodeCell wenc14) base width lanes lane op data) := by
  intro point hx hy hpoint
  by_cases hm : ∃ q ∈ op.points, address base width lanes lane q = address base width lanes lane point
  · obtain ⟨q,hq,he⟩ := hm
    have hxy := Op.points_bounded hv q hq
    have hqp := address_injective base width lanes lane hl q point hxy.1 hx he
    subst q
    have heq := aligned_coarse_origin p hp op hal point hq hpoint
    rw [heq]
    exact transform14_origin_small base width height lanes lane op data hl ha hv hs
  · rw [transform_read_other]
    · exact hg point hx hy hpoint
    · intro q hq he
      exact hm ⟨q,hq,he⟩

/-- Disjointness preserves the source of every later operation, while each
low-pass write maintains the coarse-lattice range invariant. -/
theorem transform14_fold_coarse_grid (base width height lanes lane p : Nat) (ops : List Op)
    (data : Array UInt16) (hp : 0 < p) (hl : lane < lanes)
    (ha : base+height*width*lanes ≤ data.size)
    (hv : ∀ op ∈ ops, op.Valid width height) (hal : ∀ op ∈ ops, op.Aligned p)
    (hd : ops.Pairwise (fun a b => ∀ x ∈ a.points, ∀ y ∈ b.points,
      address base width lanes lane x ≠ address base width lanes lane y))
    (hs : ∀ op ∈ ops, ∀ point ∈ op.points, data[address base width lanes lane point]! < 16384)
    (hg : SmallGrid base width height lanes lane (2*p) data) :
    SmallGrid base width height lanes lane (2*p)
      (ops.foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) data) := by
  induction ops generalizing data with
  | nil => exact hg
  | cons op rest ih =>
    have hdis := List.pairwise_cons.mp hd
    let next := transform wenc14 (encodeCell wenc14) base width lanes lane op data
    have hnext : SmallGrid base width height lanes lane (2*p) next :=
      transform14_coarse_grid base width height lanes lane p op data hp hl ha
        (hv op List.mem_cons_self) (hal op List.mem_cons_self) (hs op List.mem_cons_self) hg
    have hsrc : ∀ q ∈ rest, ∀ point ∈ q.points, next[address base width lanes lane point]! < 16384 := by
      intro q hq point hpoint
      dsimp only [next]
      rw [transform_read_other]
      · exact hs q (List.mem_cons_of_mem _ hq) point hpoint
      · intro x hx he
        exact hdis.1 q hq x hx point hpoint he
    change SmallGrid base width height lanes lane (2*p)
      (rest.foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) next)
    exact ih next (by simpa only [next,transform_size] using ha)
      (fun q hq => hv q (List.mem_cons_of_mem _ hq)) (fun q hq => hal q (List.mem_cons_of_mem _ hq))
      hdis.2 hsrc hnext

theorem level14_coarse_grid (base width height lanes lane p : Nat) (data : Array UInt16)
    (hp : 0 < p) (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : SmallGrid base width height lanes lane p data) :
    SmallGrid base width height lanes lane (2*p)
      ((level width height p).foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) data) :=
  transform14_fold_coarse_grid base width height lanes lane p _ data hp hl ha
    (level_valid width height p hp) (level_aligned width height p)
    (level_addresses_disjoint base width height lanes lane p hl hp)
    (level_sources_small base width height lanes lane p data hp hs)
    (smallGrid_coarsen base width height lanes lane p data hs)

def pass14 (decode : Bool) (base width height lanes lane k : Nat) (data : Array UInt16) : Array UInt16 :=
  if 2*2^k ≤ min width height then
    if decode then
      (level width height (2^k)).foldl (fun a op => transform wdec14 (decodeCell wdec14) base width lanes lane op a) data
    else
      (level width height (2^k)).foldl (fun a op => transform wenc14 (encodeCell wenc14) base width lanes lane op a) data
  else data

theorem pass14_size (decode : Bool) (base width height lanes lane k : Nat) (data : Array UInt16) :
    (pass14 decode base width height lanes lane k data).size = data.size := by
  unfold pass14
  split
  · split <;> exact transform_fold_size _ _ base width lanes lane _ data
  · rfl

theorem pass14_coarse_grid (base width height lanes lane k : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : SmallGrid base width height lanes lane (2^k) data) :
    SmallGrid base width height lanes lane (2^(k+1)) (pass14 false base width height lanes lane k data) := by
  have he : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [he]
  by_cases hk : 2*2^k ≤ min width height
  · simp only [pass14,hk,ite_true,Bool.false_eq_true,ite_false]
    exact level14_coarse_grid base width height lanes lane (2^k) data (Nat.two_pow_pos k) hl ha hs
  · simp only [pass14,hk,ite_false]
    exact smallGrid_coarsen base width height lanes lane (2^k) data hs

theorem pass14_inverse (base width height lanes lane k : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : SmallGrid base width height lanes lane (2^k) data) :
    pass14 true base width height lanes lane k (pass14 false base width height lanes lane k data) = data := by
  by_cases hk : 2*2^k ≤ min width height
  · simp only [pass14,hk,ite_true,Bool.false_eq_true,ite_false]
    exact level14_inverse base width height lanes lane (2^k) data hl ha (Nat.two_pow_pos k)
      (level_sources_small base width height lanes lane (2^k) data (Nat.two_pow_pos k) hs)
  · simp only [pass14,hk,ite_false]

theorem passes14_size (base width height lanes lane : Nat) (levels : List Nat) (data : Array UInt16) :
    (levels.foldl (fun a k => pass14 false base width height lanes lane k a) data).size = data.size := by
  induction levels generalizing data with
  | nil => rfl
  | cons k rest ih => simp only [List.foldl_cons,ih,pass14_size]

/-- After every encoder prefix, its next low-pass lattice remains bounded.
This establishes the range hypotheses internally for all later levels. -/
theorem passes14_grid (base width height lanes lane n : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : SmallGrid base width height lanes lane 1 data) :
    SmallGrid base width height lanes lane (2^n)
      ((List.range n).foldl (fun a k => pass14 false base width height lanes lane k a) data) := by
  induction n with
  | zero => simpa only [List.range_zero,List.foldl_nil,Nat.pow_zero] using hs
  | succ n ih =>
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact pass14_coarse_grid base width height lanes lane n _ hl
      (by simpa only [passes14_size] using ha) ih

/-- Decoder prefixes reverse encoder passes with no externally supplied
per-level range assumptions: `passes14_grid` derives them from the source. -/
theorem passes14_inverse (base width height lanes lane n : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : SmallGrid base width height lanes lane 1 data) :
    (List.range n).reverse.foldl (fun a k => pass14 true base width height lanes lane k a)
      ((List.range n).foldl (fun a k => pass14 false base width height lanes lane k a) data) = data := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [pass14_inverse base width height lanes lane n _ hl
      (by simpa only [passes14_size] using ha) (passes14_grid base width height lanes lane n data hl ha hs)]
    exact ih

/-- Complete executable small-range traversal inverse in the actual C order.
All intermediate source bounds follow from the low-pass lattice invariant. -/
theorem run14_inverse (base width height lanes lane : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : ∀ point, point.1 < width → point.2 < height → data[address base width lanes lane point]! < 16384) :
    run true true base width height lanes lane (run false true base width height lanes lane data) = data := by
  have hg : SmallGrid base width height lanes lane 1 data := fun point hx hy _ => hs point hx hy
  have hi := passes14_inverse base width height lanes lane (min width height) data hl ha hg
  simpa only [run,pass14,Bool.false_eq_true,ite_false,ite_true] using hi

/-- The mode-selected executable wavelet inverse. The small-range source
hypothesis is required precisely when the bitmap selects 14-bit lifting. -/
theorem run_inverse (small : Bool) (base width height lanes lane : Nat) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hs : small = true → ∀ point, point.1 < width → point.2 < height →
      data[address base width lanes lane point]! < 16384) :
    run true small base width height lanes lane (run false small base width height lanes lane data) = data := by
  cases small with
  | false => exact run16_inverse base width height lanes lane data hl ha
  | true => exact run14_inverse base width height lanes lane data hl ha (hs rfl)

end Exr.Piz.Traversal
