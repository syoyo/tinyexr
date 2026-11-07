/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Byte-size accounting for rows, blocks and parts: the intermediate
  equations that tie the layout arithmetic to concrete byte counts.

  * `rowBytes` — uncompressed bytes of one scan-line row (all channels);
  * `chunkLines` / `scanlinePayloadBytes` — per-chunk line counts sum to
    exactly the image height, so the uncompressed payload of a scan-line
    part is exactly `height * rowBytes`;
  * `packBlockBytes` / `blockStreamBytes` — B44 block stream totals
    (3 or 14 bytes per block), matching `packBlock`'s emitted length;
  * `tablesBytes` — offset-table region sizes (8 bytes per chunk), tied to
    the parser by `tablesBytes_of_parseTables` and `Parse.parseTables_end`;
  * `u32Bytes` / `u64Bytes` sizes and the 64-bit no-overflow conditions
    under which the emitters do not truncate.

  All arithmetic in the model is over `Nat`; no-overflow is stated as the
  external condition that the quantity fits in 32/64 bits.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.B44
import Mathlib.Data.Int.CardIntervalMod
import Exr.Emit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace Exr

open scoped BigOperators

/-- A neutral stand-in for dependent lookups that are never out of range. -/
private def dummyChannel : Channel := ⟨ByteArray.empty, .uint, false, 1, 1⟩
private def dummyTable : OffsetTable := ⟨[]⟩

/-- Sum of `f` over `l.map f` as a BigOperators sum over `Finset.range`.
    `d` is an arbitrary fill used to state the sum without dependent types;
    every index in range is filled from `l`. -/
theorem list_map_sum_eq_finset_sum {α : Type} (l : List α) (f : α → Nat) (d : α) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    show f a + ∑ i ∈ Finset.range l.length, f (l.getD i d)
        = ∑ i ∈ Finset.range (l.length + 1), f ((a :: l).getD i d)
    have hsum : ∑ i ∈ Finset.range l.length, f (l.getD i d)
        = ∑ k ∈ Finset.range l.length, f ((a :: l).getD (k + 1) d) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [List.getD_cons_succ]
    rw [Finset.sum_range_succ', List.getD_cons_zero, hsum]
    omega

/-! ## Row byte sizes (uncompressed pixel data) -/

/-- Uncompressed bytes of one scan-line row of `width` pixels (all channels). -/
def rowBytes (cs : List Channel) (width : Nat) : Nat :=
  (cs.map fun c => width * c.pixelType.sizeBytes).sum

/-- Per-pixel uncompressed size (all channels). -/
def pixelSize (cs : List Channel) : Nat :=
  (cs.map fun c => c.pixelType.sizeBytes).sum

theorem pixelSize_le (cs : List Channel) : pixelSize cs ≤ 4 * cs.length := by
  unfold pixelSize
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h4 : c.pixelType.sizeBytes ≤ 4 := by
      cases c.pixelType <;> simp [PixelType.sizeBytes]
    omega

theorem pixelSize_pos {cs : List Channel} (hcs : cs ≠ []) : 0 < pixelSize cs := by
  unfold pixelSize
  induction cs with
  | nil => exact absurd rfl hcs
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h2 : 0 < c.pixelType.sizeBytes := by
      cases c.pixelType <;> simp [PixelType.sizeBytes]
    omega

theorem rowBytes_cons (c : Channel) (cs : List Channel) (width : Nat) :
    rowBytes (c :: cs) width = width * c.pixelType.sizeBytes + rowBytes cs width := by
  simp [rowBytes]

theorem rowBytes_append (a b : List Channel) (width : Nat) :
    rowBytes (a ++ b) width = rowBytes a width + rowBytes b width := by
  simp [rowBytes, List.map_append, List.sum_append]

theorem rowBytes_le (cs : List Channel) (width : Nat) :
    rowBytes cs width ≤ cs.length * (width * 4) := by
  unfold rowBytes
  induction cs generalizing width with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h4 : c.pixelType.sizeBytes ≤ 4 := by
      cases c.pixelType <;> simp [PixelType.sizeBytes]
    have ih' := ih width
    have hfac : (cs.length + 1) * (width * 4) = cs.length * (width * 4) + width * 4 := by
      ring
    have h5 : width * c.pixelType.sizeBytes ≤ width * 4 :=
      Nat.mul_le_mul_left width h4
    omega

/-- One row of a non-empty channel list at positive width holds data. -/
theorem rowBytes_pos {cs : List Channel} (hcs : cs ≠ []) {width : Nat} (hw : 1 ≤ width) :
    0 < rowBytes cs width := by
  induction cs with
  | nil => exact absurd rfl hcs
  | cons c cs ih =>
    rw [rowBytes_cons]
    have h2 : 0 < c.pixelType.sizeBytes := by
      cases c.pixelType <;> simp [PixelType.sizeBytes]
    have h3 : 0 < width * c.pixelType.sizeBytes := by
      exact Nat.mul_pos hw h2
    omega

/-- BigOperators form of `rowBytes`: a sum over `Finset.range` of the channel
    index (the `getD` fill is never used: the index is in range). -/
theorem rowBytes_eq_finset_sum (cs : List Channel) (width : Nat) :
    rowBytes cs width =
      ∑ i ∈ Finset.range cs.length, width * (cs.getD i dummyChannel).pixelType.sizeBytes :=
  list_map_sum_eq_finset_sum cs (fun c => width * c.pixelType.sizeBytes) dummyChannel

/-- Per-pixel size as a BigOperators sum. -/
theorem pixelSize_eq_finset_sum (cs : List Channel) :
    pixelSize cs =
      ∑ i ∈ Finset.range cs.length, (cs.getD i dummyChannel).pixelType.sizeBytes :=
  list_map_sum_eq_finset_sum cs (fun c => c.pixelType.sizeBytes) dummyChannel

/-- `rowBytes` is `width` times `pixelSize`: the two views of a row coincide. -/
theorem rowBytes_eq_width_mul_pixelSize (cs : List Channel) (width : Nat) :
    rowBytes cs width = width * pixelSize cs := by
  unfold rowBytes pixelSize
  induction cs generalizing width with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- No row of a validated image exceeds 64 bits when the channel count and the
    width do. -/
theorem rowBytes_lt_2pow64 (cs : List Channel) (width : Nat)
    (hlen : cs.length ≤ 2 ^ 31) (hw : width < 2 ^ 31) :
    rowBytes cs width < 2 ^ 64 := by
  have h := rowBytes_le cs width
  have h1 : cs.length * (width * 4) < 2 ^ 64 := by
    have hw4 : width * 4 < 2 ^ 33 := by omega
    calc cs.length * (width * 4) ≤ 2 ^ 31 * (width * 4) :=
            Nat.mul_le_mul_right _ hlen
      _ ≤ 2 ^ 31 * (2 ^ 33 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ 64 - 2 ^ 31 := by norm_num
      _ < 2 ^ 64 := by omega
  omega

/-! ## Per-chunk accounting of scan-line parts -/

/-- Uncompressed bytes of `lines` rows of the channel list. -/
def blockPayloadBytes (cs : List Channel) (width lines : Nat) : Nat :=
  lines * rowBytes cs width

theorem blockPayloadBytes_eq_finset_sum (cs : List Channel) (width lines : Nat) :
    blockPayloadBytes cs width lines =
      ∑ _i ∈ Finset.range lines, rowBytes cs width := by
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]
  rw [blockPayloadBytes]

/-- Lines covered by chunk `i` of a scan-line part at `lpb` lines per block
    (the last chunk may be short). -/
def chunkLines (height lpb i : Nat) : Nat :=
  min lpb (height - lpb * i)

/-- Every index below `q` is a full block. -/
theorem sum_range_chunkLines_full (lpb q r n : Nat) (_hlpb : 1 ≤ lpb) (hr : r < lpb)
    (hn : n ≤ q) :
    ∑ i ∈ Finset.range n, min lpb (q * lpb + r - lpb * i) = n * lpb := by
  induction n with
  | zero => simp
  | succ n ihn =>
    have hn' : n ≤ q := by omega
    have hstep : lpb ≤ q * lpb + r - lpb * n := by
      have h1 : lpb * (n + 1) ≤ lpb * q := Nat.mul_le_mul_left lpb hn
      rw [Nat.mul_succ] at h1
      have h2 : lpb * q = q * lpb := Nat.mul_comm lpb q
      omega
    rw [Finset.sum_range_succ, ihn hn']
    have hmin : min lpb (q * lpb + r - lpb * n) = lpb := by omega
    rw [hmin]
    ring

/-- The per-chunk line counts of a scan-line part sum to exactly the image
    height: no row is dropped and none is double-counted. -/
theorem chunkLines_sum (height lpb : Nat) (hlpb : 1 ≤ lpb) :
    ∑ i ∈ Finset.range (Tiles.scanlineChunks height lpb), chunkLines height lpb i = height := by
  set q := height / lpb with hq
  set r := height % lpb with hr
  have hmod : height = q * lpb + r := by
    rw [hq, hr, Nat.mul_comm (height / lpb) lpb, Nat.div_add_mod]
  have hplt : r < lpb := Nat.mod_lt height (by omega)
  have hchunks : Tiles.scanlineChunks height lpb = q + (if r = 0 then 0 else 1) := by
    have h1 : height + lpb - 1 = (r + lpb - 1) + lpb * q := by
      have e : q * lpb = lpb * q := Nat.mul_comm q lpb
      omega
    unfold Tiles.scanlineChunks
    rw [h1, Nat.add_mul_div_left (r + lpb - 1) q hlpb]
    rcases eq_or_ne r 0 with h0 | hr0
    · rw [h0, Nat.zero_add]
      have h2 : (lpb - 1) / lpb = 0 := Nat.div_eq_of_lt (by omega)
      rw [h2]
      simp
    · rw [ite_eq_right hr0]
      have h2 : (r + lpb - 1) / lpb = 1 := by
        have hlow : 1 ≤ (r + lpb - 1) / lpb := by
          rw [Nat.le_div_iff_mul_le hlpb]
          omega
        have hhigh : (r + lpb - 1) / lpb < 2 := by
          rw [Nat.div_lt_iff_lt_mul hlpb]
          omega
        omega
      rw [h2]
      omega
  rw [hchunks, hmod]
  rcases eq_or_ne r 0 with h0 | hr0
  · rw [h0]
    have hfull0 := sum_range_chunkLines_full lpb q 0 q hlpb (by omega) (le_refl q)
    simpa [chunkLines] using hfull0
  · rw [ite_eq_right hr0]
    have hsplit := Finset.sum_range_succ (fun i => chunkLines (q * lpb + r) lpb i) q
    rw [hsplit]
    have hfull : ∑ i ∈ Finset.range q, chunkLines (q * lpb + r) lpb i = q * lpb := by
      simp only [chunkLines]
      exact sum_range_chunkLines_full lpb q r q hlpb hplt (le_refl q)
    have hlast : chunkLines (q * lpb + r) lpb q = r := by
      unfold chunkLines
      have h3 : min lpb (q * lpb + r - lpb * q) = r := by
        have e : q * lpb = lpb * q := Nat.mul_comm q lpb
        omega
      exact h3
    rw [hfull, hlast]

/-- Uncompressed payload bytes of a scan-line part: every chunk carries its
    (possibly short) rows. The equation `height * rowBytes` shows the layout
    needs no padding between rows. -/
def scanlinePayloadBytes (cs : List Channel) (width height lpb : Nat) : Nat :=
  ∑ i ∈ Finset.range (Tiles.scanlineChunks height lpb),
    blockPayloadBytes cs width (chunkLines height lpb i)

/-- The uncompressed payload of a scan-line part is exactly the image size in
    bytes. -/
theorem scanlinePayloadBytes_eq (cs : List Channel) (width height lpb : Nat) (hlpb : 1 ≤ lpb) :
    scanlinePayloadBytes cs width height lpb = height * rowBytes cs width := by
  unfold scanlinePayloadBytes blockPayloadBytes
  rw [← Finset.sum_mul, chunkLines_sum height lpb hlpb]

/-- 64-bit no-overflow for the uncompressed payload of a scan-line part. -/
theorem scanlinePayloadBytes_lt_2pow64 (cs : List Channel) (width height lpb : Nat)
    (hlpb : 1 ≤ lpb) (hlen : cs.length ≤ 2 ^ 14) (hpix : width * height < 2 ^ 46) :
    scanlinePayloadBytes cs width height lpb < 2 ^ 64 := by
  have hrow : rowBytes cs width ≤ 4 * cs.length * width := by
    calc rowBytes cs width ≤ cs.length * (width * 4) := rowBytes_le cs width
      _ = 4 * cs.length * width := by ring
  rw [scanlinePayloadBytes_eq cs width height lpb hlpb]
  rcases Nat.eq_zero_or_pos height with rfl | hh
  · simp
  · have hpix' : height * width < 2 ^ 46 := by rwa [Nat.mul_comm]
    have h4 : 4 * 2 ^ 14 * (height * width) < 4 * 2 ^ 14 * 2 ^ 46 :=
      Nat.mul_lt_mul_of_pos_left hpix' (by positivity)
    calc height * rowBytes cs width
        ≤ height * (4 * cs.length * width) := Nat.mul_le_mul_left height hrow
      _ = 4 * cs.length * (height * width) := by ring
      _ ≤ 4 * 2 ^ 14 * (height * width) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hlen)
      _ < 4 * 2 ^ 14 * 2 ^ 46 := h4
      _ = 2 ^ 62 := by norm_num
      _ < 2 ^ 64 := by norm_num

/-! ## B44 block stream byte totals -/

/-- Byte size of a sequence of packed blocks given their flat flags
    (`blockBytes`: 3 for a flat B44A block, 14 otherwise). -/
def blockStreamBytes (flags : List Bool) : Nat :=
  (flags.map B44.blockBytes).sum

/-- Stand-in used only to state the BigOperators form. -/
private def dummyFlag : Bool := false

theorem blockStreamBytes_eq_finset_sum (flags : List Bool) :
    blockStreamBytes flags =
      ∑ i ∈ Finset.range flags.length, B44.blockBytes (flags.getD i dummyFlag) :=
  list_map_sum_eq_finset_sum flags B44.blockBytes dummyFlag

theorem blockStreamBytes_le (flags : List Bool) :
    blockStreamBytes flags ≤ 14 * flags.length := by
  unfold blockStreamBytes
  induction flags with
  | nil => simp
  | cons f flags ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hf : B44.blockBytes f ≤ 14 := by
      unfold B44.blockBytes; split <;> omega
    omega

theorem blockStreamBytes_ge (flags : List Bool) :
    3 * flags.length ≤ blockStreamBytes flags := by
  unfold blockStreamBytes
  induction flags with
  | nil => simp
  | cons f flags ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hf : 3 ≤ B44.blockBytes f := by
      unfold B44.blockBytes; split <;> omega
    omega

theorem blockStreamBytes_all_flat (n : Nat) :
    blockStreamBytes (List.replicate n true) = 3 * n := by
  unfold blockStreamBytes B44.blockBytes
  simp [List.map_replicate]
  omega

theorem blockStreamBytes_all_regular (n : Nat) :
    blockStreamBytes (List.replicate n false) = 14 * n := by
  unfold blockStreamBytes B44.blockBytes
  simp [List.map_replicate]
  omega

/-- The packed block's emitted length equals `blockBytes` of its (B44A) flat
    flag — the exact analogue of the 14/3 split. -/
theorem packBlock_length_eq_blockBytes (blk : Fin 16 → UInt16) (flatfields : Bool) :
    (B44.packBlock blk flatfields).length = B44.blockBytes (B44.isFlat blk flatfields) := by
  unfold B44.packBlock B44.blockBytes
  split <;> rfl

/-- A PXR24 plane-major row stream is the sum of its planes: `bytes` planes of
    `vals.length` entries each. -/
theorem packPlanes_length_eq_finset_sum (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) :
    (Pxr24.packPlanes vals bytes).length =
      ∑ _k ∈ Finset.range bytes, vals.length := by
  rw [Pxr24.packPlanes_length vals bytes hb,
      Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]
  exact Nat.mul_comm _ _

/-! ## Offset-table region size (both parser and emitter) -/

/-- Bytes consumed by one offset table: 8 per entry. -/
def tableBytes (t : OffsetTable) : Nat :=
  8 * t.offsets.length

/-- Bytes consumed by all offset tables: 8 per chunk across all parts. -/
def tablesBytes (ts : List OffsetTable) : Nat :=
  (ts.map tableBytes).sum

theorem tablesBytes_eq_finset_sum (ts : List OffsetTable) :
    tablesBytes ts =
      ∑ i ∈ Finset.range ts.length, 8 * (ts.getD i dummyTable).offsets.length :=
  list_map_sum_eq_finset_sum ts tableBytes dummyTable

/-- Tables emitted by the parser consume exactly `8 × total chunks` bytes. -/
theorem tablesBytes_of_parseTables {b : Bytes} {parts : List Header} {i : Nat}
    {ts : List OffsetTable} {j : Nat}
    (h : Parse.parseTables b parts i = some (ts, j)) :
    tablesBytes ts = 8 * (parts.map Parse.chunkCountOf).sum := by
  induction parts generalizing i ts j with
  | nil =>
    simp only [Parse.parseTables, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h01, rfl⟩ := h
    subst h01
    simp [tablesBytes]
  | cons hd tl ih =>
    simp only [Parse.parseTables] at h
    cases ht : Parse.parseOffsetTable b (Parse.chunkCountOf hd) i with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, j₁⟩ := p
      simp only [ht] at h
      cases hr : Parse.parseTables b tl j₁ with
      | none => simp [hr] at h
      | some p₂ =>
        obtain ⟨ts', j₂⟩ := p₂
        simp only [hr] at h
        obtain ⟨_, rfl⟩ := h
        have htb : t.offsets.length = Parse.chunkCountOf hd :=
          Parse.parseOffsetTable_length ht
        have ih' := ih hr
        simp only [tablesBytes, tableBytes, List.map_cons, List.sum_cons, htb] at *
        omega

/-- The bytes the parser consumed past `i` are exactly the tables' bytes. -/
theorem parseTables_consumed_bytes {b : Bytes} {parts : List Header} {i : Nat}
    {ts : List OffsetTable} {j : Nat}
    (h : Parse.parseTables b parts i = some (ts, j)) :
    j - i = tablesBytes ts := by
  rw [Parse.parseTables_end h, tablesBytes_of_parseTables h]
  omega

/-- 64-bit no-overflow for the offset-table region. -/
theorem tablesBytes_le_2pow64 (ts : List OffsetTable)
    (hsum : (ts.map fun t => t.offsets.length).sum ≤ 2 ^ 61) :
    tablesBytes ts ≤ 2 ^ 64 := by
  have h1 : tablesBytes ts = 8 * (ts.map fun t => t.offsets.length).sum := by
    unfold tablesBytes tableBytes
    rw [list_map_sum_eq_finset_sum ts (fun t => 8 * t.offsets.length) dummyTable,
        ← Finset.mul_sum,
        ← list_map_sum_eq_finset_sum ts (fun t => t.offsets.length) dummyTable]
  omega

/-! ## Little-endian scalar field sizes (emitter side) -/

theorem putU16LE_size (v : UInt16) (acc : Bytes) : (putU16LE v acc).size = acc.size + 2 := by
  simp [putU16LE, ByteArray.size_push]

theorem putU32LE_size (v : UInt32) (acc : Bytes) : (putU32LE v acc).size = acc.size + 4 := by
  simp [putU32LE, ByteArray.size_push]

theorem putU64LE_size (v : UInt64) (acc : Bytes) : (putU64LE v acc).size = acc.size + 8 := by
  simp [putU64LE, ByteArray.size_push]

theorem u32Bytes_size (n : Nat) : (Emit.u32Bytes n).size = 4 := by
  rw [Emit.u32Bytes, putU32LE_size]
  rfl

theorem u64Bytes_size (n : Nat) : (Emit.u64Bytes n).size = 8 := by
  rw [Emit.u64Bytes, putU64LE_size]
  rfl

/-- The emitted offset-table region has exactly `8` bytes per entry. -/
theorem offsetTableBytes_size (offsets : List Nat) :
    (Emit.offsetTableBytes offsets).size = 8 * offsets.length := by
  have key : ∀ (os : List Nat) (acc : Bytes),
      (os.foldl (fun acc o => acc ++ Emit.u64Bytes o) acc).size
        = acc.size + 8 * os.length := by
    intro os
    induction os with
    | nil => intro acc; simp
    | cons o os ih =>
      intro acc
      rw [List.foldl_cons, ih _, ByteArray.size_append, u64Bytes_size, List.length_cons]
      omega
  rw [Emit.offsetTableBytes, key]
  simp

/-- A `u64Bytes` field does not truncate below `2^64` (the file-offset
    budget). -/
theorem u64Bytes_faithful (n : Nat) (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  show (OfNat.ofNat n : UInt64).toNat = n
  rw [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Above `2^64` the emitter silently truncates: this is the exact boundary
    callers must check before emitting absolute offsets. -/
theorem u64Bytes_ofNat_mod (n : Nat) : (UInt64.ofNat n).toNat = n % 2 ^ 64 := by
  show (OfNat.ofNat n : UInt64).toNat = n % 2 ^ 64
  rw [UInt64.toNat_ofNat]

/-- A `u32Bytes` field (e.g. attribute sizes) does not truncate below `2^32`. -/
theorem u32Bytes_faithful (n : Nat) (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  show (OfNat.ofNat n : UInt32).toNat = n
  rw [UInt32.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem u32Bytes_ofNat_mod (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  show (OfNat.ofNat n : UInt32).toNat = n % 2 ^ 32
  rw [UInt32.toNat_ofNat]

end Exr

namespace Exr

/-- Number of sampled x coordinates in an inclusive row extent. The finite
    enumeration also defines the empty extent and negative origins exactly. -/
def sampledCount (origin : Int) (width sampling : Nat) : Nat :=
  if sampling = 0 then 0 else
    ((List.range width).filter fun (i : Nat) => (origin + (i : Int)) % (sampling : Int) == 0).length

theorem sampledCount_le (origin : Int) (width sampling : Nat) :
    sampledCount origin width sampling ≤ width := by
  unfold sampledCount
  split
  · omega
  · exact (List.length_filter_le _ _).trans (by simp)

theorem sampledCount_one (origin : Int) (width : Nat) :
    sampledCount origin width 1 = width := by
  simp [sampledCount]

/-- Offset of the first sampled coordinate within a sampling period. -/
def sampledPhase (origin : Int) (sampling : Nat) : Nat := ((-origin) % (sampling : Int)).toNat

theorem sampledPhase_mod (origin : Int) (sampling : Nat) (hs : sampling ≠ 0) (i : Nat) :
    (origin + (i : Int)) % (sampling : Int) = 0 ↔ i ≡ sampledPhase origin sampling [MOD sampling] := by
  have spos : (0 : Int) < sampling := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hc : ((sampledPhase origin sampling : Nat) : Int) = (-origin) % (sampling : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [← Int.natCast_modEq_iff]
  change (origin + (i : Int)) % (sampling : Int) = 0 ↔
    (i : Int) % (sampling : Int) = (sampledPhase origin sampling : Int) % (sampling : Int)
  rw [hc, Int.emod_emod]
  change (origin + (i : Int)) ≡ 0 [ZMOD sampling] ↔ (i : Int) ≡ -origin [ZMOD sampling]
  constructor
  · intro h
    simpa [← Int.add_assoc] using h.add_left (-origin)
  · intro h
    simpa using h.add_left origin

def sampledCountFast (origin : Int) (width sampling : Nat) : Nat :=
  if sampling = 0 then 0 else width / sampling +
    if sampledPhase origin sampling < width % sampling then 1 else 0

theorem sampledCountFast_eq (origin : Int) (width sampling : Nat) :
    sampledCountFast origin width sampling = sampledCount origin width sampling := by
  by_cases hs : sampling = 0
  · simp [sampledCountFast, sampledCount, hs]
  · have hp : sampledPhase origin sampling < sampling := by
      have hm := Int.emod_lt_of_pos (-origin) (show (0 : Int) < sampling by exact_mod_cast Nat.pos_of_ne_zero hs)
      have hn := Int.emod_nonneg (-origin) (show (sampling : Int) ≠ 0 by exact_mod_cast hs)
      unfold sampledPhase
      omega
    have he : (fun i : Nat => ((origin + (i : Int)) % (sampling : Int) == 0)) =
        (fun i : Nat => decide (i ≡ sampledPhase origin sampling [MOD sampling])) := by
      funext i
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq, decide_eq_true_eq] using sampledPhase_mod origin sampling hs i
    rw [sampledCount, ite_eq_right hs, ← List.countP_eq_length_filter, he]
    change sampledCountFast origin width sampling = Nat.count (fun i => i ≡ sampledPhase origin sampling [MOD sampling]) width
    rw [Nat.count_modEq_card width (Nat.pos_of_ne_zero hs)]
    simp [sampledCountFast, hs, Nat.mod_eq_of_lt hp]

/-- Actual byte count of one channel at absolute row y. -/
def sampledChannelBytes (c : Channel) (origin : Int) (width : Nat) (y : Int) : Nat :=
  if y % c.ySampling.toInt = 0 then
    sampledCount origin width c.xSampling.toInt.toNat * c.pixelType.sizeBytes
  else 0

/-- Canonical scanline byte count, including channel subsampling. `rowBytes`
    is its full-resolution upper bound. -/
def sampledRowBytes (cs : List Channel) (origin : Int) (width : Nat) (y : Int) : Nat :=
  (cs.map fun c => sampledChannelBytes c origin width y).sum

theorem sampledChannelBytes_le (c : Channel) (origin : Int) (width : Nat) (y : Int) :
    sampledChannelBytes c origin width y ≤ width * c.pixelType.sizeBytes := by
  unfold sampledChannelBytes
  split
  · exact Nat.mul_le_mul_right _ (sampledCount_le origin width _)
  · omega

theorem sampledRowBytes_le (cs : List Channel) (origin : Int) (width : Nat) (y : Int) :
    sampledRowBytes cs origin width y ≤ rowBytes cs width := by
  induction cs with
  | nil => simp [sampledRowBytes, rowBytes]
  | cons c cs ih =>
    have hc := sampledChannelBytes_le c origin width y
    simp only [sampledRowBytes, rowBytes, List.map_cons, List.sum_cons] at *
    omega

/-- Sum actual row byte counts; vertical subsampling can make rows differ. -/
def sampledBlockBytes (cs : List Channel) (x y : Int) (width lines : Nat) : Nat :=
  ((List.range lines).map fun row => sampledRowBytes cs x width (y + (row : Int))).sum

/-- Executable counterpart with constant-time horizontal sample counting.
    Scanline blocks contain only the codec's bounded number of rows. -/
def sampledBlockBytesFast (cs : List Channel) (x y : Int) (width lines : Nat) : Nat :=
  ((List.range lines).map fun row =>
    (cs.map fun c => if (y + (row : Int)) % c.ySampling.toInt = 0 then
      sampledCountFast x width c.xSampling.toInt.toNat * c.pixelType.sizeBytes else 0).sum).sum

theorem sampledBlockBytesFast_eq (cs : List Channel) (x y : Int) (width lines : Nat) :
    sampledBlockBytesFast cs x y width lines = sampledBlockBytes cs x y width lines := by
  simp only [sampledBlockBytesFast, sampledBlockBytes, sampledRowBytes,
    sampledChannelBytes, sampledCountFast_eq]

theorem sampledCountFast_large : sampledCountFast (-1) 2147483647 2 = 1073741823 := by decide

theorem sampledCount_negative_origin : sampledCount (-3) 7 2 = 3 := by decide

theorem sampledCount_empty : sampledCount 0 0 2 = 0 := by decide

end Exr
