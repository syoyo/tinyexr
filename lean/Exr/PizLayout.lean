/-
  TinyEXR - PIZ sampled-channel planar/canonical layout and access bounds.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizTraversal
import Exr.Size

namespace Exr.Piz.Layout

structure ChannelSpec where
  pixelType : PixelType
  xSampling : Nat
  ySampling : Nat
  deriving Repr, DecidableEq

structure Context where
  x : Int
  y : Int
  width : Nat
  lines : Nat
  channels : List ChannelSpec
  deriving Repr, DecidableEq

def Context.Valid (ctx : Context) : Prop :=
  0 < ctx.channels.length ∧ ctx.channels.length ≤ 1024 ∧
    ∀ c ∈ ctx.channels, 0 < c.xSampling ∧ 0 < c.ySampling

instance (ctx : Context) : Decidable ctx.Valid := by
  unfold Context.Valid
  infer_instance

structure Plane where
  width : Nat
  lanes : Nat
  rows : List Nat
  deriving Repr, DecidableEq

def Plane.wordCount (p : Plane) : Nat := p.rows.length*p.width*p.lanes

def Context.planes (ctx : Context) : List Plane :=
  ctx.channels.map (fun c =>
    ⟨sampledCountFast ctx.x ctx.width c.xSampling,
      if c.pixelType = .half then 1 else 2,
      (List.range ctx.lines).filter (fun row =>
        c.ySampling != 0 && (ctx.y + (row : Int)) % (c.ySampling : Int) == 0)⟩)

def wordCount (planes : List Plane) : Nat := (planes.map Plane.wordCount).sum

/-- Sorting these keys reproduces canonical line/channel/word order, while
addresses refer to the per-channel planar intermediate buffer. -/
structure Token where
  line : Nat
  channel : Nat
  word : Nat
  address : Nat
  deriving Repr, DecidableEq

def Token.before (a b : Token) : Bool :=
  if a.line = b.line then
    if a.channel = b.channel then decide (a.word ≤ b.word) else decide (a.channel < b.channel)
  else decide (a.line < b.line)

def planeTokens (base channel : Nat) (p : Plane) : List Token :=
  p.rows.zipIdx.flatMap (fun row =>
    (List.range (p.width*p.lanes)).map (fun word =>
      ⟨row.1,channel,word,base+row.2*(p.width*p.lanes)+word⟩))

def tokensGo : Nat → Nat → List Plane → List Token
  | _, _, [] => []
  | base, channel, p::rest =>
    planeTokens base channel p ++ tokensGo (base+p.wordCount) (channel+1) rest

def tokens (planes : List Plane) : List Token :=
  (tokensGo 0 0 planes).mergeSort Token.before

theorem planeTokens_size (base channel : Nat) (p : Plane) :
    (planeTokens base channel p).length = p.wordCount := by
  simp [planeTokens, Plane.wordCount, List.length_flatMap, Nat.mul_assoc]

theorem planeTokens_bounds (base channel : Nat) (p : Plane) :
    ∀ token ∈ planeTokens base channel p, base ≤ token.address ∧ token.address < base+p.wordCount := by
  intro token ht
  obtain ⟨row, hr, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp ht
  have hrow := List.snd_lt_of_mem_zipIdx hr
  simp only [Nat.add_zero] at hrow
  have hword := List.mem_range.mp hw
  have hb := Traversal.address_bounded base (p.width*p.lanes) p.rows.length 1 0
    (word,row.2) hword hrow (by decide)
  simp only [Traversal.address, Nat.mul_one, Nat.add_zero] at hb
  refine ⟨by dsimp; omega, ?_⟩
  simpa only [Plane.wordCount, Nat.mul_assoc, Nat.add_assoc] using hb

theorem tokensGo_size (base channel : Nat) (planes : List Plane) :
    (tokensGo base channel planes).length = wordCount planes := by
  induction planes generalizing base channel with
  | nil => rfl
  | cons p rest ih => simp [tokensGo, wordCount, planeTokens_size, ih]

theorem tokensGo_bounds (base channel : Nat) (planes : List Plane) :
    ∀ token ∈ tokensGo base channel planes,
      base ≤ token.address ∧ token.address < base+wordCount planes := by
  induction planes generalizing base channel with
  | nil => simp [tokensGo]
  | cons p rest ih =>
    intro token ht
    rcases List.mem_append.mp ht with ht | ht
    · have hb := planeTokens_bounds base channel p token ht
      simp only [wordCount, List.map_cons, List.sum_cons] at *
      omega
    · have hb := ih (base+p.wordCount) (channel+1) token ht
      simp only [wordCount, List.map_cons, List.sum_cons] at *
      omega

theorem tokens_size (planes : List Plane) : (tokens planes).length = wordCount planes := by
  rw [tokens, List.length_mergeSort, tokensGo_size]

theorem tokens_bounds (planes : List Plane) :
    ∀ token ∈ tokens planes, token.address < wordCount planes := by
  intro token ht
  have hp := (List.mergeSort_perm (tokensGo 0 0 planes) Token.before).mem_iff.mp ht
  have hb := tokensGo_bounds 0 0 planes token hp
  simpa using hb.2

/-- Flattening consecutive row allocations visits every address once. -/
theorem row_addresses (base width rows : Nat) :
    (List.range rows).flatMap (fun row =>
      (List.range width).map (fun word => base+row*width+word)) =
      List.range' base (rows*width) := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← List.range'_eq_map_range, List.range'_append_1]
    simp only [Nat.succ_mul]

/-- Address enumeration is independent of physical row labels, including
subsampled and negative-origin rows. Only their ranks affect storage. -/
theorem planeTokens_addresses (base channel : Nat) (p : Plane) :
    (planeTokens base channel p).map Token.address = List.range' base p.wordCount := by
  simp only [planeTokens, List.map_flatMap, List.map_map, Function.comp_def]
  have he := List.zipIdx_map_snd 0 p.rows
  have hf := congrArg (List.flatMap (fun row =>
    (List.range (p.width*p.lanes)).map (fun word => base+row*(p.width*p.lanes)+word))) he
  simp only [List.flatMap_map] at hf
  rw [hf]
  simpa only [← List.range_eq_range', Plane.wordCount, Nat.mul_assoc] using
    row_addresses base (p.width*p.lanes) p.rows.length

theorem tokensGo_addresses (base channel : Nat) (planes : List Plane) :
    (tokensGo base channel planes).map Token.address = List.range' base (wordCount planes) := by
  induction planes generalizing base channel with
  | nil => rfl
  | cons p rest ih =>
    simp only [tokensGo, List.map_append, planeTokens_addresses, ih,
      List.range'_append_1, wordCount, List.map_cons, List.sum_cons]

/-- Sorting into canonical order permutes the entire planar allocation:
no sample is duplicated, omitted, or read from padding. -/
theorem tokens_addresses_perm (planes : List Plane) :
    ((tokens planes).map Token.address).Perm (List.range (wordCount planes)) := by
  have hp := (List.mergeSort_perm (tokensGo 0 0 planes) Token.before).map Token.address
  rw [tokensGo_addresses, ← List.range_eq_range'] at hp
  exact hp

/-- Reorder all decoded planar words. No emitted word reads outside storage
when the packet's decoded word count agrees with the layout word count. -/
def canonical (planes : List Plane) (data : Array UInt16) : List UInt16 :=
  (tokens planes).map (fun token => data[token.address]!)

def planar (planes : List Plane) (data : List UInt16) : Array UInt16 :=
  ((tokens planes).zipIdx).foldl (fun out p => out.set! p.1.address (data.getD p.2 0))
    (Array.replicate (wordCount planes) 0)

theorem canonical_size (planes : List Plane) (data : Array UInt16) :
    (canonical planes data).length = wordCount planes := by
  simp only [canonical, List.length_map, tokens_size]

theorem write_fold_size {α : Type} (entries : List α) (address : α → Nat)
    (value : α → UInt16) (data : Array UInt16) :
    (entries.foldl (fun out e => out.set! (address e) (value e)) data).size = data.size := by
  induction entries generalizing data with
  | nil => rfl
  | cons e rest ih => simp only [List.foldl_cons, ih, Array.size_set!]

theorem write_fold_absent {α : Type} (entries : List α) (address : α → Nat)
    (value : α → UInt16) (data : Array UInt16) (i : Nat)
    (ha : ∀ e ∈ entries, address e ≠ i) :
    (entries.foldl (fun out e => out.set! (address e) (value e)) data)[i]! = data[i]! := by
  induction entries generalizing data with
  | nil => rfl
  | cons e rest ih =>
    rw [List.foldl_cons, ih (data.set! (address e) (value e))
      (fun x hx => ha x (List.mem_cons_of_mem e hx))]
    exact Array.getElem!_set!_ne data _ _ _ (ha e List.mem_cons_self)

/-- A scatter to distinct bounded addresses writes each source value exactly
once; later entries cannot overwrite an earlier sample. -/
theorem write_fold_mem {α : Type} (entries : List α) (address : α → Nat)
    (value : α → UInt16) (data : Array UInt16)
    (hn : (entries.map address).Nodup)
    (hb : ∀ e ∈ entries, address e < data.size)
    (entry : α) (he : entry ∈ entries) :
    (entries.foldl (fun out e => out.set! (address e) (value e)) data)[address entry]! = value entry := by
  induction entries generalizing data with
  | nil => simp at he
  | cons e rest ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp he with he | he
    · subst entry
      rw [List.foldl_cons, write_fold_absent rest address value _ (address e) (by
        intro x hx heq
        exact hnd.1 (List.mem_map.mpr ⟨x,hx,heq⟩))]
      exact Array.getElem!_set!_self data _ _ (hb e List.mem_cons_self)
    · rw [List.foldl_cons]
      exact ih (data.set! (address e) (value e)) hnd.2
        (fun x hx => by simpa only [Array.size_set!] using hb x (List.mem_cons_of_mem e hx)) he

theorem tokens_addresses_nodup (planes : List Plane) :
    ((tokens planes).map Token.address).Nodup :=
  (tokens_addresses_perm planes).nodup_iff.mpr (List.nodup_range)

theorem indexed_addresses (planes : List Plane) :
    ((tokens planes).zipIdx.map (fun p => p.1.address)) = (tokens planes).map Token.address := by
  have he := congrArg (List.map Token.address) (List.zipIdx_map_fst 0 (tokens planes))
  simpa only [List.map_map, Function.comp_def] using he

theorem planar_size (planes : List Plane) (data : List UInt16) :
    (planar planes data).size = wordCount planes := by
  rw [planar, write_fold_size, Array.size_replicate]

/-- The canonical gather inverts the actual array scatter for arbitrary
channel geometry and source words of the computed sampled size. -/
theorem canonical_planar (planes : List Plane) (data : List UInt16)
    (hs : data.length = wordCount planes) : canonical planes (planar planes data) = data := by
  apply List.ext_getElem
  · rw [canonical_size, hs]
  · intro i hi hd
    have hti : i < (tokens planes).length := by simpa only [tokens_size, canonical_size] using hi
    let token := (tokens planes)[i]
    have hm : (token,i) ∈ (tokens planes).zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hti)
    have hn : ((tokens planes).zipIdx.map (fun p => p.1.address)).Nodup := by
      rw [indexed_addresses]; exact tokens_addresses_nodup planes
    have hb : ∀ p ∈ (tokens planes).zipIdx, p.1.address < (Array.replicate (wordCount planes) (0 : UInt16)).size := by
      intro p hp
      have ht : p.1 ∈ tokens planes := by
        rw [← List.zipIdx_map_fst 0 (tokens planes)]
        exact List.mem_map.mpr ⟨p,hp,rfl⟩
      simpa only [Array.size_replicate] using tokens_bounds planes p.1 ht
    have hw := write_fold_mem (tokens planes).zipIdx (fun p => p.1.address)
      (fun p => data.getD p.2 0) (Array.replicate (wordCount planes) 0) hn hb (token,i) hm
    simpa only [canonical, List.getElem_map, planar, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hd, Option.getD_some] using hw

/-- The reverse direction holds for every planar buffer of the exact sampled
size. Together with `canonical_planar`, this establishes layout bijectivity. -/
theorem planar_canonical (planes : List Plane) (data : Array UInt16)
    (hs : data.size = wordCount planes) : planar planes (canonical planes data) = data := by
  apply Array.ext
  · rw [planar_size, hs]
  · intro i hi hd
    have hm : i ∈ (tokens planes).map Token.address :=
      (tokens_addresses_perm planes).mem_iff.mpr (List.mem_range.mpr (by omega))
    obtain ⟨token,ht,he⟩ := List.mem_map.mp hm
    obtain ⟨j,hj,hjtoken⟩ := List.mem_iff_getElem.mp ht
    have hpair : (token,j) ∈ (tokens planes).zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hj, hjtoken])
    have hn : ((tokens planes).zipIdx.map (fun p => p.1.address)).Nodup := by
      rw [indexed_addresses]; exact tokens_addresses_nodup planes
    have hb : ∀ p ∈ (tokens planes).zipIdx, p.1.address < (Array.replicate (wordCount planes) (0 : UInt16)).size := by
      intro p hp
      have ht : p.1 ∈ tokens planes := by
        rw [← List.zipIdx_map_fst 0 (tokens planes)]
        exact List.mem_map.mpr ⟨p,hp,rfl⟩
      simpa only [Array.size_replicate] using tokens_bounds planes p.1 ht
    have hw := write_fold_mem (tokens planes).zipIdx (fun p => p.1.address)
      (fun p => (canonical planes data).getD p.2 0)
      (Array.replicate (wordCount planes) 0) hn hb (token,j) hpair
    have hv : (canonical planes data).getD j 0 = data[token.address]! := by
      simp only [canonical, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, hjtoken]
    change (planar planes (canonical planes data))[token.address]! = _ at hw
    rw [hv, he] at hw
    simpa only [getElem!_pos (planar planes (canonical planes data)) i hi, getElem!_pos data i hd] using hw

theorem canonical_access (planes : List Plane) (data : Array UInt16)
    (hs : data.size = wordCount planes) (token : Token) (ht : token ∈ tokens planes) :
    token.address < data.size := by rw [hs]; exact tokens_bounds planes token ht

def waveletGo (decode small : Bool) : Nat → List Plane → Array UInt16 → Array UInt16
  | _, [], data => data
  | base, p::rest, data =>
    let next := (List.range p.lanes).foldl (fun a lane =>
      Traversal.run decode small base p.width p.rows.length p.lanes lane a) data
    waveletGo decode small (base+p.wordCount) rest next

theorem lane_fold_size (decode small : Bool) (base : Nat) (p : Plane)
    (lanes : List Nat) (data : Array UInt16) :
    (lanes.foldl (fun a lane => Traversal.run decode small base p.width p.rows.length p.lanes lane a) data).size =
      data.size := by
  induction lanes generalizing data with
  | nil => rfl
  | cons lane rest ih => simp only [List.foldl_cons, ih, Traversal.run_size]

theorem waveletGo_size (decode small : Bool) (base : Nat) (planes : List Plane) (data : Array UInt16) :
    (waveletGo decode small base planes data).size = data.size := by
  induction planes generalizing base data with
  | nil => rfl
  | cons p rest ih => simp only [waveletGo, ih, lane_fold_size]

/-- A channel's complete allocation and every later channel are disjoint
suffixes of the same buffer. This is the bound used by traversal accesses. -/
theorem head_allocation (base : Nat) (p : Plane) (rest : List Plane) :
    base+p.rows.length*p.width*p.lanes ≤ base+wordCount (p::rest) := by
  simp only [wordCount, List.map_cons, List.sum_cons, Plane.wordCount]
  omega

theorem head_wavelet_access (base : Nat) (p : Plane) (rest : List Plane)
    (lane : Nat) (hl : lane < p.lanes) (op : Traversal.Op)
    (ho : op ∈ Traversal.schedule p.width p.rows.length)
    (point : Traversal.Point) (hp : point ∈ op.points) :
    Traversal.address base p.width p.lanes lane point < base+wordCount (p::rest) :=
  Traversal.allocation_bounds base p.width p.rows.length p.lanes lane _ hl
    (head_allocation base p rest) op ho point hp

end Exr.Piz.Layout
