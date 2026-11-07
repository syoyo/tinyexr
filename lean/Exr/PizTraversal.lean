/-
  TinyEXR - PIZ multilevel wavelet traversal and strided memory bounds.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Piz

namespace Exr.Piz.Traversal

abbrev Point := Nat × Nat

/-- The C traversal performs a separable cell, or a pair on an odd edge. -/
inductive Op where
  | cell (x y step : Nat)
  | horizontal (x y step : Nat)
  | vertical (x y step : Nat)
  deriving Repr, DecidableEq

def Op.points : Op → List Point
  | .cell x y p => [(x,y), (x+p,y), (x,y+p), (x+p,y+p)]
  | .horizontal x y p => [(x,y), (x+p,y)]
  | .vertical x y p => [(x,y), (x,y+p)]

def Op.Valid (width height : Nat) : Op → Prop
  | .cell x y p => 0 < p ∧ x + p < width ∧ y + p < height
  | .horizontal x y p => 0 < p ∧ x + p < width ∧ y < height
  | .vertical x y p => 0 < p ∧ x < width ∧ y + p < height

theorem and_power (n k : Nat) :
    n &&& 2^k = if n.testBit k then 2^k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hb : n.testBit k = true
  · rw [ite_eq_left hb]
    by_cases hi : k = i
    · subst i
      simp [Nat.testBit_and, hb]
    · simp [Nat.testBit_and, hi]
  · rw [ite_eq_right hb]
    by_cases hi : k = i
    · subst i
      simp [Nat.testBit_and, hb]
    · simp [Nat.testBit_and, hi]

/-- The modulo edge test is equivalent to the C bit-mask test at every
power-of-two level. -/
theorem edge_test (n k : Nat) :
    (n &&& 2^k ≠ 0) ↔ 2^k ≤ n % (2 * 2^k) := by
  have hp := Nat.two_pow_pos k
  have hdiv := Nat.mod_mul_right_div_self n (2^k) 2
  rw [Nat.mul_comm (2^k) 2] at hdiv
  have hmod := Nat.mod_lt n (by omega : 0 < 2 * 2^k)
  have hlt : n % (2 * 2^k) / 2^k < 2 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hpos : 1 ≤ n % (2 * 2^k) / 2^k ↔ 2^k ≤ n % (2 * 2^k) := by
    simpa using (Nat.le_div_iff_mul_le hp (x := 1) (y := n % (2 * 2^k)))
  have he : n / 2^k % 2 = 1 ↔ 2^k ≤ n % (2 * 2^k) := by omega
  rw [and_power, Nat.testBit_eq_decide_div_mod_eq]
  by_cases ht : n / 2^k % 2 = 1
  · have hr := he.mp ht
    simp [ht, hr]
  · have hr := mt he.mpr ht
    simp [ht, hr]

/-- Full cells and the right edge within one complete pair of rows. -/
def rowOps (width y p : Nat) : List Op :=
  (List.range (width / (2*p))).map (fun i => .cell (i*(2*p)) y p) ++
    if p ≤ width % (2*p) then [.vertical ((width / (2*p))*(2*p)) y p] else []

/-- One level of wav2_encode, with step p and block step 2*p. Division
counts complete blocks; the remainder selects the same odd edge as nx & p
when p is a power of two. Cells appear in the C's row-major order. -/
def level (width height p : Nat) : List Op :=
  (List.range (height / (2*p))).flatMap (fun j => rowOps width (j*(2*p)) p) ++
    if p ≤ height % (2*p) then
      (List.range (width / (2*p))).map
        (fun i => .horizontal (i*(2*p)) ((height / (2*p))*(2*p)) p)
    else []

theorem complete_block (n p i : Nat) (hp : 0 < p) (hi : i < n / (2*p)) :
    i*(2*p) + p < n := by
  have hm := Nat.mul_le_mul_right (2*p) (show i+1 ≤ n/(2*p) by omega)
  have hn := Nat.div_mul_le_self n (2*p)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem remainder_base (n p : Nat) (hp : 0 < p) (hr : p ≤ n % (2*p)) :
    (n/(2*p))*(2*p) < n := by
  have hm := Nat.mod_add_div n (2*p)
  rw [Nat.mul_comm (2*p)] at hm
  omega

theorem rowOps_valid (w h y p : Nat) (hp : 0 < p) (hy : y+p < h) :
    ∀ op ∈ rowOps w y p, op.Valid w h := by
  intro op hm
  simp only [rowOps, List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact ⟨hp, complete_block w p i hp (List.mem_range.mp hi), hy⟩
  · split at hm
    · rename_i hr
      simp only [List.mem_singleton] at hm
      subst op
      exact ⟨hp, remainder_base w p hp hr, hy⟩
    · simp at hm

theorem level_valid (w h p : Nat) (hp : 0 < p) :
    ∀ op ∈ level w h p, op.Valid w h := by
  intro op hm
  simp only [level, List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
    exact rowOps_valid w h (j*(2*p)) p hp
      (complete_block h p j hp (List.mem_range.mp hj)) op hm
  · split at hm
    · rename_i hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
      exact ⟨hp, complete_block w p i hp (List.mem_range.mp hi), remainder_base h p hp hr⟩
    · simp at hm

/-- Levels are increasing powers of two, bounded by min(width,height).
The finite list avoids overflow and termination assumptions on a C shift loop. -/
def schedule (width height : Nat) : List Op :=
  (List.range (min width height)).flatMap (fun k =>
    if 2 * 2^k ≤ min width height then level width height (2^k) else [])

theorem schedule_valid (w h : Nat) :
    ∀ op ∈ schedule w h, op.Valid w h := by
  intro op hm
  obtain ⟨k, _, hm⟩ := List.mem_flatMap.mp hm
  split at hm
  · exact level_valid w h (2^k) (Nat.two_pow_pos k) op hm
  · simp at hm

theorem Op.points_bounded {w h : Nat} {op : Op} (hv : op.Valid w h) :
    ∀ point ∈ op.points, point.1 < w ∧ point.2 < h := by
  cases op <;> simp_all [Op.Valid, Op.points] <;> omega

/-- A lane of a planar channel: C ox=lanes and oy=width*lanes. -/
def address (base width lanes lane : Nat) (point : Point) : Nat :=
  base + (point.2*width + point.1)*lanes + lane

theorem address_bounded (base w h lanes lane : Nat) (point : Point)
    (hx : point.1 < w) (hy : point.2 < h) (hl : lane < lanes) :
    address base w lanes lane point < base + h*w*lanes := by
  have hm := Nat.mul_le_mul_right w (show point.2+1 ≤ h by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hc : point.2*w + point.1 + 1 ≤ h*w := by omega
  have hm2 := Nat.mul_le_mul_right lanes hc
  rw [Nat.add_mul, Nat.one_mul] at hm2
  unfold address
  omega

theorem schedule_addresses_bounded (base w h lanes lane : Nat) (hl : lane < lanes)
    (op : Op) (hop : op ∈ schedule w h) (point : Point) (hp : point ∈ op.points) :
    address base w lanes lane point < base + h*w*lanes := by
  have hb := Op.points_bounded (schedule_valid w h op hop) point hp
  exact address_bounded base w h lanes lane point hb.1 hb.2 hl

/-- Execute one instruction in channel-planar storage. The theorem below
bounds every read/write for a generated schedule, including both UINT/FLOAT
lanes. No bounds filter changes the traversal's semantics. -/
def transform (pair : UInt16 → UInt16 → UInt16 × UInt16)
    (cell : ((UInt16 × UInt16) × (UInt16 × UInt16)) →
      ((UInt16 × UInt16) × (UInt16 × UInt16)))
    (base width lanes lane : Nat) (op : Op) (data : Array UInt16) : Array UInt16 :=
  let addr := address base width lanes lane
  match op with
  | .cell x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    let c := addr (x,y+p)
    let d := addr (x+p,y+p)
    let v := cell ((data[a]!, data[b]!), (data[c]!, data[d]!))
    (((data.set! a v.1.1).set! b v.1.2).set! c v.2.1).set! d v.2.2
  | .horizontal x y p =>
    let a := addr (x,y)
    let b := addr (x+p,y)
    let v := pair data[a]! data[b]!
    (data.set! a v.1).set! b v.2
  | .vertical x y p =>
    let a := addr (x,y)
    let b := addr (x,y+p)
    let v := pair data[a]! data[b]!
    (data.set! a v.1).set! b v.2

theorem transform_size (pair cell) (base w lanes lane : Nat) (op : Op) (data : Array UInt16) :
    (transform pair cell base w lanes lane op data).size = data.size := by
  cases op <;> simp [transform]

def run (decode small : Bool) (base width height lanes lane : Nat)
    (data : Array UInt16) : Array UInt16 :=
  let pair := if decode then (if small then wdec14 else wdec16)
    else (if small then wenc14 else wenc16)
  let cell := if decode then decodeCell pair else encodeCell pair
  let levels := List.range (min width height)
  let levels := if decode then levels.reverse else levels
  levels.foldl (fun data k =>
    if 2 * 2^k ≤ min width height then
      (level width height (2^k)).foldl (fun data op =>
        transform pair cell base width lanes lane op data) data
    else data) data

theorem transform_fold_size (pair cell) (base w lanes lane : Nat)
    (ops : List Op) (data : Array UInt16) :
    (ops.foldl (fun a op => transform pair cell base w lanes lane op a) data).size = data.size := by
  induction ops generalizing data with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons, ih, transform_size]

theorem levels_fold_size (pair cell) (base w h lanes lane : Nat)
    (levels : List Nat) (data : Array UInt16) :
    (levels.foldl (fun data k =>
      if 2 * 2^k ≤ min w h then
        (level w h (2^k)).foldl (fun data op =>
          transform pair cell base w lanes lane op data) data
      else data) data).size = data.size := by
  induction levels generalizing data with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · exact transform_fold_size pair cell base w lanes lane _ data
    · rfl

theorem run_size (decode small : Bool) (base w h lanes lane : Nat) (data : Array UInt16) :
    (run decode small base w h lanes lane data).size = data.size :=
  levels_fold_size _ _ base w h lanes lane _ data

/-- Every instruction access is within any containing allocation. This
includes nonzero channel bases and padding beyond the channel's last lane. -/
theorem allocation_bounds (base w h lanes lane allocation : Nat)
    (hl : lane < lanes) (ha : base + h*w*lanes ≤ allocation)
    (op : Op) (hop : op ∈ schedule w h) (point : Point) (hp : point ∈ op.points) :
    address base w lanes lane point < allocation :=
  lt_of_lt_of_le (schedule_addresses_bounded base w h lanes lane hl op hop point hp) ha

theorem mem_schedule_of_level (w h k : Nat) (hk : k < min w h)
    (ha : 2 * 2^k ≤ min w h) (op : Op) (ho : op ∈ level w h (2^k)) :
    op ∈ schedule w h := by
  apply List.mem_flatMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  simpa only [ite_eq_left ha] using ho

/-- Any prefix of executed instructions retains the allocation size, so the
access bound applies to intermediate arrays as well as the initial input. -/
theorem intermediate_access_bounds (pair cell) (base w h lanes lane : Nat)
    (data : Array UInt16) (executed : List Op)
    (hl : lane < lanes) (ha : base + h*w*lanes ≤ data.size)
    (op : Op) (hop : op ∈ schedule w h) (point : Point) (hp : point ∈ op.points) :
    address base w lanes lane point <
      (executed.foldl (fun a op => transform pair cell base w lanes lane op a) data).size := by
  rw [transform_fold_size]
  exact allocation_bounds base w h lanes lane data.size hl ha op hop point hp

/-- The C's ox1/ox2/oy1/oy2 products fit the same bound as the complete
channel allocation. Taking limit=INT_MAX discharges signed multiplication
bounds for an active level; the caller must establish its allocation limit. -/
theorem stride_products_bounded (w h lanes p limit : Nat)
    (hp : 0 < p) (hx : 2*p ≤ w) (hy : 2*p ≤ h)
    (hb : h*w*lanes ≤ limit) :
    w*lanes ≤ limit ∧ lanes*p ≤ limit ∧ lanes*(2*p) ≤ limit ∧
      (w*lanes)*p ≤ limit ∧ (w*lanes)*(2*p) ≤ limit := by
  have hstride : w*lanes ≤ limit := by
    have hm := Nat.mul_le_mul_right (w*lanes) (show 1 ≤ h by omega)
    have hs : w*lanes ≤ h*w*lanes := by simpa [Nat.mul_assoc] using hm
    exact le_trans hs hb
  have hhor : lanes*(2*p) ≤ limit := calc
    lanes*(2*p) ≤ lanes*w := Nat.mul_le_mul_left lanes hx
    _ = w*lanes := Nat.mul_comm lanes w
    _ ≤ limit := hstride
  have hver : (w*lanes)*(2*p) ≤ limit := calc
    (w*lanes)*(2*p) ≤ (w*lanes)*h := Nat.mul_le_mul_left (w*lanes) hy
    _ = h*w*lanes := by ac_rfl
    _ ≤ limit := hb
  have hhor1 := Nat.mul_le_mul_left lanes (show p ≤ 2*p by omega)
  have hver1 := Nat.mul_le_mul_left (w*lanes) (show p ≤ 2*p by omega)
  exact ⟨hstride, le_trans hhor1 hhor, hhor, le_trans hver1 hver, hver⟩

end Exr.Piz.Traversal
