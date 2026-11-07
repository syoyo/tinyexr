/-
  TinyEXR - executable PIZ wavelet array-update inverse proofs.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizTraversal

namespace Exr.Piz.Traversal

/-- Row-major lane addresses are injective on valid horizontal coordinates.
The positive lane count follows from the caller's lane bound. -/
theorem address_injective (base width lanes lane : Nat) (hl : lane < lanes)
    (p q : Point) (hp : p.1 < width) (hq : q.1 < width)
    (he : address base width lanes lane p = address base width lanes lane q) : p = q := by
  have hm : (p.2*width+p.1)*lanes = (q.2*width+q.1)*lanes := by
    simp only [address] at he
    omega
  have hr := Nat.mul_right_cancel (by omega : 0 < lanes) hm
  have hx := congrArg (fun n => n % width) hr
  rw [Nat.mul_add_mod_of_lt hp, Nat.mul_add_mod_of_lt hq] at hx
  have hy := Nat.mul_right_cancel (by omega : 0 < width)
    (show p.2*width = q.2*width by omega)
  exact Prod.ext hx hy

theorem Op.points_nodup (op : Op) (width height : Nat) (hv : op.Valid width height) :
    op.points.Nodup := by
  cases op <;> simp_all [Op.Valid,Op.points] <;> omega

theorem op_addresses_nodup (base width height lanes lane : Nat) (hl : lane < lanes)
    (op : Op) (hv : op.Valid width height) :
    (op.points.map (address base width lanes lane)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (op.points_nodup width height hv)
  intro p q hp hq hne he
  exact hne (address_injective base width lanes lane hl p q
    (Op.points_bounded hv p hp).1 (Op.points_bounded hv q hq).1 he)

theorem array_ext_read (left right : Array UInt16) (hs : left.size = right.size)
    (he : ∀ i, i < left.size → left[i]! = right[i]!) : left = right := by
  apply Array.ext hs
  intro i hi hj
  exact (getElem!_pos left i hi).symm.trans ((he i hi).trans (getElem!_pos right i hj))

/-- Reading a bounded write is an explicit conditional, including reads
outside the updated pair/cell. -/
theorem read_set (data : Array UInt16) (i j : Nat) (value : UInt16) (hi : i < data.size) :
    (data.set! i value)[j]! = if i = j then value else data[j]! := by
  by_cases he : i = j
  · subst j
    simp only [ite_true, Array.getElem!_set!_self data i value hi]
  · rw [Array.getElem!_set!_ne data i j value he, ite_eq_right he]

def storePair (data : Array UInt16) (a b : Nat) (values : UInt16 × UInt16) : Array UInt16 :=
  (data.set! a values.1).set! b values.2

def pairStep (pair : UInt16 → UInt16 → UInt16 × UInt16)
    (a b : Nat) (data : Array UInt16) : Array UInt16 :=
  storePair data a b (pair data[a]! data[b]!)

@[simp] theorem storePair_size (data : Array UInt16) (a b : Nat) (values : UInt16 × UInt16) :
    (storePair data a b values).size = data.size := by simp [storePair]

theorem storePair_read (data : Array UInt16) (a b : Nat) (values : UInt16 × UInt16)
    (ha : a < data.size) (hb : b < data.size) (hne : a ≠ b) :
    (storePair data a b values)[a]! = values.1 ∧ (storePair data a b values)[b]! = values.2 := by
  constructor
  · rw [storePair, Array.getElem!_set!_ne _ b a _ (Ne.symm hne),
      Array.getElem!_set!_self _ a _ ha]
  · rw [storePair, Array.getElem!_set!_self _ b _ (by simpa only [Array.size_set!] using hb)]

theorem pairStep_inverse_at (enc dec : UInt16 → UInt16 → UInt16 × UInt16)
    (a b : Nat) (data : Array UInt16)
    (hinv : dec (enc data[a]! data[b]!).1 (enc data[a]! data[b]!).2 = (data[a]!,data[b]!))
    (ha : a < data.size) (hb : b < data.size) (hne : a ≠ b) :
    pairStep dec a b (pairStep enc a b data) = data := by
  let encoded := pairStep enc a b data
  have hr := storePair_read data a b (enc data[a]! data[b]!) ha hb hne
  have hv : dec encoded[a]! encoded[b]! = (data[a]!,data[b]!) := by
    change dec (storePair data a b (enc data[a]! data[b]!))[a]!
      (storePair data a b (enc data[a]! data[b]!))[b]! = _
    rw [hr.1,hr.2,hinv]
  change storePair encoded a b (dec encoded[a]! encoded[b]!) = data
  rw [hv]
  apply Array.ext
  · simp [encoded,pairStep]
  · intro i hi hd
    have he : (storePair encoded a b (data[a]!,data[b]!))[i]! = data[i]! := by
      by_cases hia : a = i
      · subst i
        exact (storePair_read encoded a b _ (by simpa [encoded,pairStep] using ha)
          (by simpa [encoded,pairStep] using hb) hne).1
      · by_cases hib : b = i
        · subst i
          exact (storePair_read encoded a b _ (by simpa [encoded,pairStep] using ha)
            (by simpa [encoded,pairStep] using hb) hne).2
        · dsimp only [storePair,encoded,pairStep]
          rw [Array.getElem!_set!_ne _ b i _ hib, Array.getElem!_set!_ne _ a i _ hia,
            Array.getElem!_set!_ne _ b i _ hib, Array.getElem!_set!_ne _ a i _ hia]
    simpa only [getElem!_pos (storePair encoded a b (data[a]!,data[b]!)) i hi,
      getElem!_pos data i hd] using he

theorem pairStep_inverse (enc dec : UInt16 → UInt16 → UInt16 × UInt16)
    (hinv : ∀ a b, dec (enc a b).1 (enc a b).2 = (a,b))
    (a b : Nat) (data : Array UInt16)
    (ha : a < data.size) (hb : b < data.size) (hne : a ≠ b) :
    pairStep dec a b (pairStep enc a b data) = data :=
  pairStep_inverse_at enc dec a b data (hinv _ _) ha hb hne

theorem storePair_read_other (data : Array UInt16) (a b i : Nat) (values : UInt16 × UInt16)
    (ha : a ≠ i) (hb : b ≠ i) : (storePair data a b values)[i]! = data[i]! := by
  rw [storePair, Array.getElem!_set!_ne _ b i _ hb, Array.getElem!_set!_ne _ a i _ ha]

def readCell (data : Array UInt16) (a b c d : Nat) : (UInt16 × UInt16) × (UInt16 × UInt16) :=
  ((data[a]!,data[b]!),(data[c]!,data[d]!))

def storeCell (data : Array UInt16) (a b c d : Nat)
    (values : (UInt16 × UInt16) × (UInt16 × UInt16)) : Array UInt16 :=
  storePair (storePair data a b values.1) c d values.2

def cellStep (cell : ((UInt16 × UInt16) × (UInt16 × UInt16)) →
    ((UInt16 × UInt16) × (UInt16 × UInt16))) (a b c d : Nat) (data : Array UInt16) : Array UInt16 :=
  storeCell data a b c d (cell (readCell data a b c d))

@[simp] theorem storeCell_size (data : Array UInt16) (a b c d : Nat) (values) :
    (storeCell data a b c d values).size = data.size := by simp [storeCell]

theorem storeCell_read (data : Array UInt16) (a b c d : Nat) (values)
    (ha : a < data.size) (hb : b < data.size) (hc : c < data.size) (hd : d < data.size)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    readCell (storeCell data a b c d values) a b c d = values := by
  have ht := storePair_read data a b values.1 ha hb hab
  have hb' := storePair_read (storePair data a b values.1) c d values.2
    (by simpa only [storePair_size] using hc) (by simpa only [storePair_size] using hd) hcd
  apply Prod.ext <;> apply Prod.ext
  · change (storePair (storePair data a b values.1) c d values.2)[a]! = values.1.1
    rw [storePair_read_other _ c d a _ (Ne.symm hac) (Ne.symm had),ht.1]
  · change (storePair (storePair data a b values.1) c d values.2)[b]! = values.1.2
    rw [storePair_read_other _ c d b _ (Ne.symm hbc) (Ne.symm hbd),ht.2]
  · exact hb'.1
  · exact hb'.2

theorem storeCell_read_other (data : Array UInt16) (a b c d i : Nat) (values)
    (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) (hd : d ≠ i) :
    (storeCell data a b c d values)[i]! = data[i]! := by
  rw [storeCell,storePair_read_other _ c d i _ hc hd,storePair_read_other _ a b i _ ha hb]

theorem cellStep_inverse_at (enc dec : ((UInt16 × UInt16) × (UInt16 × UInt16)) →
    ((UInt16 × UInt16) × (UInt16 × UInt16)))
    (a b c d : Nat) (data : Array UInt16)
    (hinv : dec (enc (readCell data a b c d)) = readCell data a b c d)
    (ha : a < data.size) (hb : b < data.size) (hc : c < data.size) (hd : d < data.size)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    cellStep dec a b c d (cellStep enc a b c d data) = data := by
  let encoded := cellStep enc a b c d data
  have hr := storeCell_read data a b c d (enc (readCell data a b c d)) ha hb hc hd hab hac had hbc hbd hcd
  have hv : dec (readCell encoded a b c d) = readCell data a b c d := by
    change dec (readCell (storeCell data a b c d (enc (readCell data a b c d))) a b c d) = _
    rw [hr,hinv]
  change storeCell encoded a b c d (dec (readCell encoded a b c d)) = data
  rw [hv]
  have hread := storeCell_read encoded a b c d (readCell data a b c d)
    (by simpa only [encoded,cellStep,storeCell_size] using ha) (by simpa only [encoded,cellStep,storeCell_size] using hb)
    (by simpa only [encoded,cellStep,storeCell_size] using hc) (by simpa only [encoded,cellStep,storeCell_size] using hd) hab hac had hbc hbd hcd
  apply array_ext_read
  · simp [encoded,cellStep]
  · intro i hi
    have he : (storeCell encoded a b c d (readCell data a b c d))[i]! = data[i]! := by
      by_cases hia : i = a
      · subst i
        exact congrArg (fun v => v.1.1) hread
      · by_cases hib : i = b
        · subst i
          exact congrArg (fun v => v.1.2) hread
        · by_cases hic : i = c
          · subst i
            exact congrArg (fun v => v.2.1) hread
          · by_cases hid : i = d
            · subst i
              exact congrArg (fun v => v.2.2) hread
            · rw [storeCell_read_other _ a b c d i _ (Ne.symm hia) (Ne.symm hib) (Ne.symm hic) (Ne.symm hid)]
              exact storeCell_read_other data a b c d i _ (Ne.symm hia) (Ne.symm hib) (Ne.symm hic) (Ne.symm hid)
    exact he

theorem cellStep_inverse (enc dec : ((UInt16 × UInt16) × (UInt16 × UInt16)) →
    ((UInt16 × UInt16) × (UInt16 × UInt16))) (hinv : ∀ values, dec (enc values) = values)
    (a b c d : Nat) (data : Array UInt16)
    (ha : a < data.size) (hb : b < data.size) (hc : c < data.size) (hd : d < data.size)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    cellStep dec a b c d (cellStep enc a b c d data) = data :=
  cellStep_inverse_at enc dec a b c d data (hinv _) ha hb hc hd hab hac had hbc hbd hcd

theorem transform_cell_eq (pair cell) (base width lanes lane x y p : Nat) (data : Array UInt16) :
    transform pair cell base width lanes lane (.cell x y p) data =
      cellStep cell (address base width lanes lane (x,y)) (address base width lanes lane (x+p,y))
        (address base width lanes lane (x,y+p)) (address base width lanes lane (x+p,y+p)) data := rfl

theorem transform_horizontal_eq (pair cell) (base width lanes lane x y p : Nat) (data : Array UInt16) :
    transform pair cell base width lanes lane (.horizontal x y p) data =
      pairStep pair (address base width lanes lane (x,y)) (address base width lanes lane (x+p,y)) data := rfl

theorem transform_vertical_eq (pair cell) (base width lanes lane x y p : Nat) (data : Array UInt16) :
    transform pair cell base width lanes lane (.vertical x y p) data =
      pairStep pair (address base width lanes lane (x,y)) (address base width lanes lane (x,y+p)) data := rfl

/-- The executable cell and odd-edge operations are inverse on a valid
channel allocation, with all address distinctness derived from geometry. -/
theorem transform_inverse (encPair decPair : UInt16 → UInt16 → UInt16 × UInt16)
    (encCell decCell : ((UInt16 × UInt16) × (UInt16 × UInt16)) →
      ((UInt16 × UInt16) × (UInt16 × UInt16)))
    (hp : ∀ a b, decPair (encPair a b).1 (encPair a b).2 = (a,b))
    (hc : ∀ values, decCell (encCell values) = values)
    (base width height lanes lane : Nat) (op : Op) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hv : op.Valid width height) :
    transform decPair decCell base width lanes lane op
      (transform encPair encCell base width lanes lane op data) = data := by
  have hn := op_addresses_nodup base width height lanes lane hl op hv
  have hb : ∀ point ∈ op.points, address base width lanes lane point < data.size := by
    intro point hm
    have hxy := Op.points_bounded hv point hm
    exact Nat.lt_of_lt_of_le (address_bounded base width height lanes lane point hxy.1 hxy.2 hl) ha
  cases op with
  | cell x y p =>
    rw [transform_cell_eq,transform_cell_eq]
    apply cellStep_inverse encCell decCell hc
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]
  | horizontal x y p =>
    rw [transform_horizontal_eq,transform_horizontal_eq]
    apply pairStep_inverse encPair decPair hp
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]
  | vertical x y p =>
    rw [transform_vertical_eq,transform_vertical_eq]
    apply pairStep_inverse encPair decPair hp
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]

/-- Full-range PIZ lifting has no value-range side condition. -/
theorem transform16_inverse (base width height lanes lane : Nat) (op : Op) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hv : op.Valid width height) :
    transform wdec16 (decodeCell wdec16) base width lanes lane op
      (transform wenc16 (encodeCell wenc16) base width lanes lane op data) = data :=
  transform_inverse wenc16 wdec16 (encodeCell wenc16) (decodeCell wdec16)
    wdec16_wenc16 decodeCell16_encodeCell16 base width height lanes lane op data hl ha hv

/-- The small-range operation inverse uses source bounds only at this
instruction's actual points; it does not constrain unrelated coefficients. -/
theorem transform14_inverse (base width height lanes lane : Nat) (op : Op) (data : Array UInt16)
    (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size) (hv : op.Valid width height)
    (hs : ∀ point ∈ op.points, data[address base width lanes lane point]! < 16384) :
    transform wdec14 (decodeCell wdec14) base width lanes lane op
      (transform wenc14 (encodeCell wenc14) base width lanes lane op data) = data := by
  have hn := op_addresses_nodup base width height lanes lane hl op hv
  have hb : ∀ point ∈ op.points, address base width lanes lane point < data.size := by
    intro point hm
    have hxy := Op.points_bounded hv point hm
    exact Nat.lt_of_lt_of_le (address_bounded base width height lanes lane point hxy.1 hxy.2 hl) ha
  cases op with
  | cell x y p =>
    rw [transform_cell_eq,transform_cell_eq]
    apply cellStep_inverse_at
    · apply decodeCell14_encodeCell14
      all_goals exact hs _ (by simp [Op.points])
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]
  | horizontal x y p =>
    rw [transform_horizontal_eq,transform_horizontal_eq]
    apply pairStep_inverse_at
    · apply wdec14_wenc14
      all_goals exact hs _ (by simp [Op.points])
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]
  | vertical x y p =>
    rw [transform_vertical_eq,transform_vertical_eq]
    apply pairStep_inverse_at
    · apply wdec14_wenc14
      all_goals exact hs _ (by simp [Op.points])
    all_goals first | exact hb _ (by simp [Op.points]) | simp_all [Op.points]

/-- Every bounded sequence of executable full-range instructions is undone
by its reverse. Relating the C decoder's within-level order to this reverse
requires the separate disjointness property of generated level operations. -/
theorem transform16_fold_inverse (base width height lanes lane : Nat) (ops : List Op)
    (data : Array UInt16) (hl : lane < lanes) (ha : base+height*width*lanes ≤ data.size)
    (hv : ∀ op ∈ ops, op.Valid width height) :
    ops.reverse.foldl (fun a op => transform wdec16 (decodeCell wdec16) base width lanes lane op a)
      (ops.foldl (fun a op => transform wenc16 (encodeCell wenc16) base width lanes lane op a) data) = data := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih (transform wenc16 (encodeCell wenc16) base width lanes lane op data)
      (by simpa only [transform_size] using ha) (fun op hop => hv op (List.mem_cons_of_mem _ hop))]
    exact transform16_inverse base width height lanes lane op data hl ha (hv op List.mem_cons_self)

/-- An instruction preserves every entry outside its actual points, even
when the containing buffer also holds other channels or SIMD word lanes. -/
theorem transform_read_other (pair cell) (base width lanes lane : Nat) (op : Op)
    (data : Array UInt16) (i : Nat)
    (hn : ∀ point ∈ op.points, address base width lanes lane point ≠ i) :
    (transform pair cell base width lanes lane op data)[i]! = data[i]! := by
  cases op with
  | cell x y p =>
    rw [transform_cell_eq]
    apply storeCell_read_other
    all_goals exact hn _ (by simp [Op.points])
  | horizontal x y p =>
    rw [transform_horizontal_eq]
    apply storePair_read_other
    all_goals exact hn _ (by simp [Op.points])
  | vertical x y p =>
    rw [transform_vertical_eq]
    apply storePair_read_other
    all_goals exact hn _ (by simp [Op.points])

theorem transform_fold_read_other (pair cell) (base width lanes lane : Nat)
    (ops : List Op) (data : Array UInt16) (i : Nat)
    (hn : ∀ op ∈ ops, ∀ point ∈ op.points, address base width lanes lane point ≠ i) :
    (ops.foldl (fun a op => transform pair cell base width lanes lane op a) data)[i]! = data[i]! := by
  induction ops generalizing data with
  | nil => rfl
  | cons op rest ih =>
    rw [List.foldl_cons,ih _ (fun q hq => hn q (List.mem_cons_of_mem _ hq))]
    exact transform_read_other pair cell base width lanes lane op data i (hn op List.mem_cons_self)

/-- No instruction can modify storage before or after its channel's planar
allocation. This is preservation, in addition to the existing access bounds. -/
theorem transform_outside_channel (pair cell) (base width height lanes lane : Nat)
    (op : Op) (data : Array UInt16) (i : Nat) (hl : lane < lanes) (hv : op.Valid width height)
    (hi : i < base ∨ base+height*width*lanes ≤ i) :
    (transform pair cell base width lanes lane op data)[i]! = data[i]! := by
  apply transform_read_other
  intro point hp
  have hxy := Op.points_bounded hv point hp
  have hb := address_bounded base width height lanes lane point hxy.1 hxy.2 hl
  have ha : base ≤ address base width lanes lane point := by simp only [address]; omega
  omega

theorem levels_fold_outside_channel (pair cell) (base width height lanes lane : Nat)
    (levels : List Nat) (data : Array UInt16) (i : Nat) (hl : lane < lanes)
    (hi : i < base ∨ base+height*width*lanes ≤ i) :
    (levels.foldl (fun data k =>
      if 2*2^k ≤ min width height then
        (level width height (2^k)).foldl (fun a op => transform pair cell base width lanes lane op a) data
      else data) data)[i]! = data[i]! := by
  induction levels generalizing data with
  | nil => rfl
  | cons k rest ih =>
    rw [List.foldl_cons,ih]
    split
    · apply transform_fold_read_other
      intro op hop point hp
      have hv := level_valid width height (2^k) (Nat.two_pow_pos k) op hop
      have hxy := Op.points_bounded hv point hp
      have hb := address_bounded base width height lanes lane point hxy.1 hxy.2 hl
      have ha : base ≤ address base width lanes lane point := by simp only [address]; omega
      omega
    · rfl

/-- The complete executable multilevel traversal preserves all storage
outside its channel, in both directions and both lifting modes. -/
theorem run_outside_channel (decode small : Bool) (base width height lanes lane : Nat)
    (data : Array UInt16) (i : Nat) (hl : lane < lanes)
    (hi : i < base ∨ base+height*width*lanes ≤ i) :
    (run decode small base width height lanes lane data)[i]! = data[i]! := by
  unfold run
  exact levels_fold_outside_channel _ _ base width height lanes lane _ data i hl hi

end Exr.Piz.Traversal
