/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  PXR24 codec model (`exr_pxr24.c` / OpenEXR `internal_pxr24.c`).

  Each channel-scanline is stored as byte planes with a running delta across
  the row:

  * UINT   4 bytes/sample, lossless,
  * HALF   2 bytes/sample, lossless (16-bit domain),
  * FLOAT  3 bytes/sample, lossy: the value is first reduced to 24 bits with
           round-to-nearest (`float24`), then delta-coded.

  The model works on byte *groups* (one group per sample), which is the
  byte-plane algebra of the codec; the byte-string layer is the concatenation
  of the groups and is validated byte-exactly against the C implementation by
  the differential harness (`test/v3/codec_diff.py`).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Attribute

namespace Exr

namespace Pxr24

/-- Bytes per sample for the PXR24 intermediate row. -/
def bpc : PixelType → Nat
  | .uint => 4
  | .half => 2
  | .float => 3

theorem bpc_pos (t : PixelType) : 0 < bpc t := by
  cases t <;> decide

/-- The value mask that survives `bytes` planes. -/
def maskOf : Nat → UInt32
  | 2 => 0xffff
  | 3 => 0xffffff
  | _ => 0xffffffff

/-- Value bound compatible with the plane count (inclusive). -/
def boundOf : Nat → UInt32
  | 2 => 0xffff
  | 3 => 0xffffff
  | _ => 0xffffffff

/-! ### float24: IEEE binary32 to 24-bit with round-to-nearest -/

/-- Reduce an IEEE binary32 bit pattern to 24 bits, keeping the top three
    bytes with round-to-nearest (increment `m & 0x80`). Matches
    `float_to_float24` in `src/exr_pxr24.c`. -/
def float24 (u : UInt32) : UInt32 :=
  if (u &&& 0x7f800000) == 0x7f800000 then
    if (u &&& 0x007fffff) != 0 then
      ((u &&& 0x80000000) >>> 8) ||| ((u &&& 0x7f800000) >>> 8) |||
        (((u &&& 0x007fffff) >>> 8) |||
          (if (u &&& 0x007fffff) >>> 8 == 0 then 1 else 0))
    else
      ((u &&& 0x80000000) >>> 8) ||| ((u &&& 0x7f800000) >>> 8)
  else
    ((u &&& 0x80000000) >>> 8) |||
      (if (((u &&& 0x7f800000 ||| u &&& 0x007fffff) +
              (u &&& 0x007fffff &&& 0x80)) >>> 8) >= 0x7f8000 then
        (((u &&& 0x7f800000) ||| (u &&& 0x007fffff)) >>> 8)
       else
        (((u &&& 0x7f800000) ||| (u &&& 0x007fffff)) + (u &&& 0x007fffff &&& 0x80)) >>> 8)

/-- The 24-bit result fits in 24 bits. -/
theorem float24_lt (u : UInt32) : float24 u < 0x1000000 := by
  unfold float24
  cases h1 : (u &&& 0x7f800000) == 0x7f800000 with
  | true =>
    simp only [ite_true]
    cases h2 : (u &&& 0x007fffff) != 0 with
    | true =>
      simp only [ite_true]
      cases h3 : (u &&& 0x007fffff) >>> 8 == 0 with
      | true => simp only [ite_true]; bv_decide
      | false => simp only [Bool.false_eq_true, ite_false]; bv_decide
    | false => simp only [Bool.false_eq_true, ite_false]; bv_decide
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    by_cases h4 : (((u &&& 0x7f800000 ||| u &&& 0x007fffff) + (u &&& 0x007fffff &&& 0x80)) >>> 8 ≥ 0x7f8000)
    · simp only [h4, ite_true]; bv_decide
    · simp only [h4, ite_false]; bv_decide

/-- Re-encoding a canonical 24-bit value (stored left-aligned in a float bit
    pattern) reproduces it. The 24-bit layout is `sign | exponent (8) |
    mantissa (15)`; shifting it into a float places the exponent in bits
    23..30, so only the all-ones (Inf/NaN) exponent can reach the outer
    special-value branch, where the NaN/Inf sub-branches keep the value. -/
theorem float24_shift_stable (v : UInt32) (hv : v < 0x1000000) :
    float24 (v <<< 8) = v := by
  unfold float24
  by_cases he : (v <<< 8) &&& 0x7f800000 = 0x7f800000
  · simp only [beq_iff_eq.mpr he, ite_true]
    by_cases hm : (v <<< 8) &&& 0x007fffff = 0
    · have hb : ((v <<< 8) &&& 0x007fffff != 0) = false := by rw [hm]; rfl
      simp only [hb, Bool.false_eq_true, ite_false]
      bv_decide
    · have hb : ((v <<< 8) &&& 0x007fffff != 0) = true := by
        rw [bne_iff_ne]; exact hm
      simp only [hb, ite_true]
      by_cases hz : ((v <<< 8) &&& 0x007fffff) >>> 8 = 0
      · have hzb : (((v <<< 8) &&& 0x007fffff) >>> 8 == 0) = true := by rw [hz]; rfl
        simp only [hzb, ite_true]
        bv_decide
      · have hzb : (((v <<< 8) &&& 0x007fffff) >>> 8 == 0) = false := by
          rw [beq_eq_false_iff_ne]; exact hz
        simp only [hzb, Bool.false_eq_true, ite_false]
        bv_decide
  · have hben : (((v <<< 8) &&& 0x7f800000) == 0x7f800000) = false :=
      beq_eq_false_iff_ne.mpr he
    simp only [hben, Bool.false_eq_true, ite_false]
    by_cases hs : (((((v <<< 8) &&& (0x7f800000 : UInt32)) |||
          ((v <<< 8) &&& (0x007fffff : UInt32))) +
        (((v <<< 8) &&& (0x007fffff : UInt32)) &&& (0x80 : UInt32))) >>> 8) >=
          (0x7f8000 : UInt32)
    · simp [hs]
      bv_decide
    · simp [hs]
      bv_decide

/-- `float24` is idempotent with respect to its own decode side: encoding the
    shifted 24-bit value yields the same 24-bit value. -/
theorem float24_stable (u : UInt32) : float24 (float24 u <<< 8) = float24 u :=
  float24_shift_stable (float24 u) (float24_lt u)

/-- Infinities encode to infinities. -/
theorem float24_inf (s : UInt32) (h : s = 0 ∨ s = 0x80000000) :
    float24 (s ||| 0x7f800000) = (s >>> 8) ||| 0x7f8000 := by
  rcases h with rfl | rfl <;> unfold float24 <;> bv_decide

/-- NaNs stay NaN: the mantissa is forced non-zero. -/
theorem float24_nan_nonzero (u : UInt32) (he : u &&& 0x7f800000 = 0x7f800000)
    (hm : u &&& 0x007fffff ≠ 0) : float24 u &&& 0x7fff ≠ 0 := by
  unfold float24
  simp only [show ((u &&& 0x7f800000) == 0x7f800000) = true from beq_iff_eq.mpr he, ite_true]
  simp only [show (u &&& 0x007fffff != 0) = true from by rw [bne_iff_ne]; exact hm, ite_true]
  cases h3 : (u &&& 0x007fffff) >>> 8 == 0 with
  | true => simp only [ite_true]; bv_decide
  | false => simp only [Bool.false_eq_true, ite_false]; bv_decide

/-- Finite inputs never become infinite: the carry path saturates inside the
    finite range. -/
theorem float24_finite_not_inf (u : UInt32) (he : u &&& 0x7f800000 ≠ 0x7f800000) :
    float24 u &&& 0x7f8000 ≠ 0x7f8000 := by
  unfold float24
  simp only [show ((u &&& 0x7f800000) == 0x7f800000) = false from
    beq_eq_false_iff_ne.mpr he, Bool.false_eq_true, ite_false]
  by_cases h4 : (((u &&& 0x7f800000 ||| u &&& 0x007fffff) + (u &&& 0x007fffff &&& 0x80)) >>> 8 ≥ 0x7f8000)
  · simp only [h4, ite_true]; bv_decide
  · simp only [h4, ite_false]; bv_decide

/-! ### Byte-plane groups -/

/-- The `bytes` byte planes of one delta, most significant first. Planes are
    masked 8-bit values in a `UInt32` (the byte-string layer truncates). -/
def planes : UInt32 → Nat → List UInt32
  | d, 2 => [(d >>> 8) &&& 0xff, d &&& 0xff]
  | d, 3 => [(d >>> 16) &&& 0xff, (d >>> 8) &&& 0xff, d &&& 0xff]
  | d, _ =>
    [(d >>> 24) &&& 0xff, (d >>> 16) &&& 0xff, (d >>> 8) &&& 0xff, d &&& 0xff]

/-- Join byte planes back into a delta value. -/
def join : List UInt32 → UInt32
  | [] => 0
  | [p] => p
  | [p, q] => (p <<< 8) ||| q
  | [p, q, r] => (p <<< 16) ||| (q <<< 8) ||| r
  | p :: q :: r :: s :: _ => (p <<< 24) ||| (q <<< 16) ||| (r <<< 8) ||| s

theorem planes_length (d : UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) : (planes d bytes).length = bytes := by
  rcases hb with rfl | rfl | rfl <;> rfl

/-- Joining the plane decomposition recovers the masked delta. -/
theorem join_planes (d : UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) :
    join (planes d bytes) = d &&& maskOf bytes := by
  rcases hb with rfl | rfl | rfl
  · show ((d >>> 8) &&& 0xff) <<< 8 ||| (d &&& 0xff) = d &&& 0xffff
    bv_decide
  · show ((d >>> 16) &&& 0xff) <<< 16 ||| ((d >>> 8) &&& 0xff) <<< 8 |||
        (d &&& 0xff) = d &&& 0xffffff
    bv_decide
  · show ((d >>> 24) &&& 0xff) <<< 24 ||| ((d >>> 16) &&& 0xff) <<< 16 |||
        ((d >>> 8) &&& 0xff) <<< 8 ||| (d &&& 0xff) = d &&& 0xffffffff
    bv_decide

/-- Group-level PXR24 encoder: per-sample deltas split into byte planes. -/
def packGroupsAux (bytes : Nat) : UInt32 → List UInt32 → List (List UInt32)
  | _, [] => []
  | prev, v :: tl => planes (v - prev) bytes :: packGroupsAux bytes v tl

def packGroups (vals : List UInt32) (bytes : Nat) : List (List UInt32) :=
  packGroupsAux bytes 0 vals

/-- Group-level PXR24 decoder: running sum of joined deltas, masked to the
    plane width (the C decoder truncates to `8*bytes` bits when storing). -/
def unpackGroupsAux (nb : Nat) : UInt32 → List (List UInt32) → List UInt32
  | _, [] => []
  | prev, g :: tl =>
    let v := (prev + join g) &&& maskOf nb
    v :: unpackGroupsAux nb v tl

def unpackGroups (gs : List (List UInt32)) (nb : Nat) : List UInt32 :=
  unpackGroupsAux nb 0 gs

theorem packGroupsAux_size (bytes : Nat) (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4)
    (prev : UInt32) (vs : List UInt32) :
    (packGroupsAux bytes prev vs).map List.length = vs.map (fun _ => bytes) := by
  induction vs generalizing prev with
  | nil => rfl
  | cons v tl ih =>
    simp only [packGroupsAux, List.map_cons, ih, planes_length _ _ hb]

theorem packGroups_size (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) :
    (packGroups vals bytes).map List.length = vals.map (fun _ => bytes) :=
  packGroupsAux_size bytes hb 0 vals

/-- Round trip: decoding the encoded groups returns the original values,
    provided each value fits the plane count. -/
theorem unpackGroupsAux_packGroupsAux (nb : Nat)
    (hb : nb = 2 ∨ nb = 3 ∨ nb = 4) :
    ∀ (prev : UInt32) (vs : List UInt32),
      (∀ v ∈ vs, v ≤ boundOf nb) → prev ≤ boundOf nb →
      unpackGroupsAux nb prev (packGroupsAux nb prev vs) = vs := by
  intro prev vs
  induction vs generalizing prev with
  | nil => intro _ _; rfl
  | cons v tl ih =>
    intro hbnd hpv
    have hv : v ≤ boundOf nb := hbnd v (List.mem_cons_self ..)
    have htl : ∀ w ∈ tl, w ≤ boundOf nb := fun w hw =>
      hbnd w (List.mem_cons_of_mem _ hw)
    simp only [packGroupsAux, unpackGroupsAux]
    rw [join_planes (v - prev) nb hb]
    have hstep : (prev + (v - prev &&& maskOf nb)) &&& maskOf nb = v := by
      rcases hb with rfl | rfl | rfl
      · show (prev + (v - prev &&& 0xffff)) &&& 0xffff = v
        have h1 : prev ≤ 0xffff := by simpa [boundOf] using hpv
        have h2 : v ≤ 0xffff := by simpa [boundOf] using hv
        clear hbnd htl hpv hv
        bv_decide
      · show (prev + (v - prev &&& 0xffffff)) &&& 0xffffff = v
        have h1 : prev ≤ 0xffffff := by simpa [boundOf] using hpv
        have h2 : v ≤ 0xffffff := by simpa [boundOf] using hv
        clear hbnd htl hpv hv
        bv_decide
      · show (prev + (v - prev &&& 0xffffffff)) &&& 0xffffffff = v
        have h1 : prev ≤ 0xffffffff := by simpa [boundOf] using hpv
        have h2 : v ≤ 0xffffffff := by simpa [boundOf] using hv
        clear hbnd htl hpv hv
        bv_decide
    rw [hstep]
    exact congrArg (List.cons v) (ih v htl hv)

theorem unpackGroups_packGroups (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4)
    (hbound : ∀ v ∈ vals, v ≤ boundOf bytes) :
    unpackGroups (packGroups vals bytes) bytes = vals := by
  unfold unpackGroups packGroups
  apply unpackGroupsAux_packGroupsAux bytes hb
  · exact hbound
  · rcases hb with rfl | rfl | rfl <;> decide

/-- UINT rows: 4-plane groups round-trip exactly (lossless). -/
theorem uint_roundtrip (vals : List UInt32) :
    unpackGroups (packGroups vals 4) 4 = vals := by
  apply unpackGroups_packGroups
  · right; right; rfl
  · intro v _
    rw [UInt32.le_iff_toNat_le]
    show v.toNat ≤ 4294967295
    have h := v.toNat_lt
    have h' : v.toNat < 4294967296 := by simpa using h
    omega

/-- HALF rows: 2-plane groups round-trip exactly for 16-bit values. -/
theorem half_roundtrip (vals : List UInt32) (h16 : ∀ v ∈ vals, v.toNat < 0x10000) :
    unpackGroups (packGroups vals 2) 2 = vals := by
  apply unpackGroups_packGroups
  · left; rfl
  · intro v hv
    rw [UInt32.le_iff_toNat_le]
    show v.toNat ≤ 65535
    have := h16 v hv
    omega

/-- FLOAT rows: `float24` followed by the 3-plane lossless round trip. -/
theorem float_roundtrip (vals : List UInt32) :
    unpackGroups (packGroups (vals.map float24) 3) 3 = vals.map float24 := by
  apply unpackGroups_packGroups
  · right; left; rfl
  · intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    rw [UInt32.le_iff_toNat_le]
    show (float24 u).toNat ≤ 16777215
    have h := float24_lt u
    have h' : (float24 u).toNat < 16777216 := by
      rw [UInt32.lt_iff_toNat_lt] at h
      simpa using h
    omega

/-- The FLOAT decode side shifts the reconstructed 24-bit value into the
    float bit position. -/
def decodeFloatRow (gs : List (List UInt32)) : List UInt32 :=
  (unpackGroups gs 3).map (fun (v : UInt32) => (v &&& 0xffffff) <<< 8)

/-- Masking a 24-bit value is the identity. -/
theorem and_24bit (v : UInt32) (h : v ≤ 0xffffff) : (v &&& 0xffffff) = v := by
  bv_decide

theorem float_decode_eq (vals : List UInt32) :
    decodeFloatRow (packGroups (vals.map float24) 3) =
      (vals.map float24).map (fun (v : UInt32) => v <<< 8) := by
  unfold decodeFloatRow
  rw [float_roundtrip]
  apply List.map_congr_left
  intro v hv
  rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
  have hlt := float24_lt u
  have hle : float24 u ≤ 0xffffff := by
    rw [UInt32.le_iff_toNat_le]
    show (float24 u).toNat ≤ 16777215
    have h' : (float24 u).toNat < 16777216 := by
      rw [UInt32.lt_iff_toNat_lt] at hlt
      simpa using hlt
    omega
  rw [and_24bit (float24 u) hle]

end Pxr24


namespace Pxr24

/-! ### Row layout: plane-major stream

The C codec stores one row plane-major: for `n` deltas with `bytes` bytes
each the stream is `plane 0 (all n MSBs), plane 1, ...`. The transposition
from the per-sample groups is expressed executably below; the byte-plane
algebra itself (delta + plane split/join) is the proven part above, and the
row layout is pinned byte-exactly against the C codec by the differential
harness (`test/v3/codec_diff.c`). -/

/-- Plane-major row stream of the PXR24 groups. -/
def packPlanes (vals : List UInt32) (bytes : Nat) : List UInt32 :=
  (List.range bytes).flatMap fun k =>
    (packGroups vals bytes).map (fun g => g.getD k 0)

/-- Rebuild per-sample groups from a plane-major stream. -/
def unpackPlanesToGroups (ps : List UInt32) (count bytes : Nat) : List (List UInt32) :=
  (List.range count).map fun i =>
    (List.range bytes).map fun k => ps.getD (k * count + i) 0

/-- Decode a plane-major row stream. -/
def unpackRowPlanes (ps : List UInt32) (count bytes : Nat) :
    List UInt32 :=
  unpackGroups (unpackPlanesToGroups ps count bytes) bytes

/-- The plane-major stream has exactly `count * bytes` entries. -/
theorem packPlanes_length (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) :
    (packPlanes vals bytes).length = vals.length * bytes := by
  have hg : (packGroups vals bytes).length = vals.length := by
    have := packGroups_size vals bytes hb
    simpa using congrArg List.length this
  rcases hb with rfl | rfl | rfl <;>
    (simp [packPlanes, hg, List.range, List.range.loop]; omega)

theorem sum_range_const (n c : Nat) :
    ((List.range n).map (fun _ => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp
    rw [Nat.add_mul, Nat.one_mul]

theorem length_flatMap_range_eq {f : Nat → List UInt32} {count : Nat} (n : Nat)
    (hlen : ∀ k < n, (f k).length = count) :
    ((List.range n).flatMap f).length = n * count := by
  rw [List.length_flatMap]
  have hmap : (List.range n).map (fun k => (f k).length)
      = (List.range n).map (fun _ => count) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    exact hlen k hk
  rw [hmap, sum_range_const]

theorem getElem?_flatMap_range {f : Nat → List UInt32} {count : Nat} (n : Nat)
    (hlen : ∀ k < n, (f k).length = count) :
    ∀ k i : Nat, k < n → i < count →
      ((List.range n).flatMap f)[k * count + i]? = (f k)[i]? := by
  induction n with
  | zero =>
    intro k i hk _
    exact (Nat.not_lt_zero k hk).elim
  | succ n ih =>
    intro k i hk hi
    have hlen' : ∀ k < n, (f k).length = count := fun k hk' => hlen k (by omega)
    rw [List.range_succ, List.flatMap_append, List.getElem?_append]
    have hleftlen : (List.flatMap f (List.range n)).length = n * count :=
      length_flatMap_range_eq n hlen'
    rw [hleftlen]
    by_cases hkn : k < n
    · have hlt : k * count + i < n * count := by
        have hle : k * count + count ≤ n * count := by
          have h2 : (k + 1) * count ≤ n * count :=
            Nat.mul_le_mul_right count (by omega)
          rw [Nat.add_mul, Nat.one_mul] at h2
          exact h2
        rcases Nat.eq_zero_or_pos count with rfl | _
        · exact absurd hi (Nat.not_lt_zero i)
        · omega
      rw [ite_eq_left hlt, ih hlen' k i hkn hi]
    · have hkeq : k = n := by omega
      subst hkeq
      rw [ite_eq_right (by omega), List.flatMap_singleton]
      congr 1
      omega

theorem getD_range_reconstruct (gs : List (List UInt32)) :
    (List.range gs.length).map (fun i => gs.getD i []) = gs := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < gs.length
  · rw [List.getElem?_range hi, Option.map_some, List.getElem?_eq_getElem hi]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hi),
        List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.map_none]

theorem plane_reconstruct (gs : List (List UInt32)) (bytes : Nat)
    (hlen : ∀ g ∈ gs, g.length = bytes)
    (i : Nat) (hi : i < gs.length) :
    (List.range bytes).map (fun k =>
        ((List.range bytes).flatMap (fun k' => gs.map (fun g => g.getD k' 0))).getD
          (k * gs.length + i) 0)
      = gs.getD i [] := by
  have hgi : (gs.getD i []).length = bytes := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hlen (gs[i]) (List.getElem_mem hi)
  have hgsi : gs.getD i [] = gs[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hgi2 : (gs[i]).length = bytes := by
    rw [← hgsi]
    exact hgi
  have hlen_plane : ∀ k < bytes, (gs.map (fun g => g.getD k 0)).length = gs.length :=
    fun k _ => List.length_map _
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  by_cases hk : k < bytes
  · rw [List.getElem?_range hk, Option.map_some, hgsi]
    rw [List.getElem?_eq_getElem (by rw [hgi2]; exact hk)]
    congr 1
    rw [List.getD_eq_getElem?_getD,
      getElem?_flatMap_range bytes hlen_plane k i hk hi,
      List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
      Option.getD_some]
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [hgi2]; exact hk), Option.getD_some]
  · have hknone : (List.range bytes)[k]? = none :=
      List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hk)
    rw [hknone, Option.map_none, List.getElem?_eq_none (by rw [hgi]; exact Nat.le_of_not_lt hk)]

/-- Plane transposition involution, stated for arbitrary groups. -/
theorem unpackPlanesToGroups_flatMap (gs : List (List UInt32)) (bytes : Nat)
    (hlen : ∀ g ∈ gs, g.length = bytes) :
    unpackPlanesToGroups ((List.range bytes).flatMap (fun k => gs.map (fun g => g.getD k 0)))
      gs.length bytes = gs := by
  have hmap : (List.range gs.length).map (fun i => (List.range bytes).map (fun k =>
        ((List.range bytes).flatMap (fun k' => gs.map (fun g => g.getD k' 0))).getD
          (k * gs.length + i) 0))
      = (List.range gs.length).map (fun i => gs.getD i []) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact plane_reconstruct gs bytes hlen i hi
  unfold unpackPlanesToGroups
  rw [hmap]
  exact getD_range_reconstruct gs

/-- Plane transposition involution: unpacking the plane-major stream of a
    row rebuilds its per-sample groups exactly. -/
theorem unpackPlanesToGroups_packPlanes (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4) :
    unpackPlanesToGroups (packPlanes vals bytes) vals.length bytes = packGroups vals bytes := by
  have hgsize := packGroups_size vals bytes hb
  have hcount : (packGroups vals bytes).length = vals.length := by
    have h := congrArg List.length hgsize
    simpa [List.length_map] using h
  have hlen : ∀ g ∈ packGroups vals bytes, g.length = bytes := by
    intro g hg
    have hmem : g.length ∈ ((packGroups vals bytes).map List.length) :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    rw [hgsize] at hmem
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hmem
    exact hx.symm
  rw [← hcount]
  exact unpackPlanesToGroups_flatMap _ _ hlen

/-- Row-level round trip: decoding a packed plane-major row returns the
    original values. -/
theorem unpackRowPlanes_packPlanes (vals : List UInt32) (bytes : Nat)
    (hb : bytes = 2 ∨ bytes = 3 ∨ bytes = 4)
    (hbound : ∀ v ∈ vals, v ≤ boundOf bytes) :
    unpackRowPlanes (packPlanes vals bytes) vals.length bytes = vals := by
  unfold unpackRowPlanes
  rw [unpackPlanesToGroups_packPlanes vals bytes hb]
  exact unpackGroups_packGroups vals bytes hb hbound

/-- A normalized channel row: FLOAT values have already passed through
`float24`, so they occupy three planes; HALF and UINT use two and four. -/
structure Row where
  bytes : Nat
  values : List UInt32

/-- Bounds needed for byte-plane split/join to preserve normalized values. -/
def Row.Valid (row : Row) : Prop :=
  (row.bytes = 2 ∨ row.bytes = 3 ∨ row.bytes = 4) ∧
    ∀ v ∈ row.values, v ≤ boundOf row.bytes

def packRows (rows : List Row) : List UInt32 :=
  rows.flatMap (fun row => packPlanes row.values row.bytes)

def rowLayout (rows : List Row) : List (Nat × Nat) :=
  rows.map (fun row => (row.values.length, row.bytes))

/-- Reconstruct a block in canonical line/channel order. Empty or skipped
sampled rows are represented by count zero or omitted from the layout. -/
def unpackRows : List (Nat × Nat) → List UInt32 → List (List UInt32)
  | [], _ => []
  | (count, bytes) :: rest, stream =>
    unpackRowPlanes (stream.take (count * bytes)) count bytes ::
      unpackRows rest (stream.drop (count * bytes))

/-- Row boundaries reset the delta accumulator. Arbitrary mixed-type and
sampled row layouts compose, without assuming a rectangular channel layout.
The external DEFLATE decoder supplies this plane stream. -/
theorem unpackRows_packRows (rows : List Row) (h : ∀ row ∈ rows, row.Valid) :
    unpackRows (rowLayout rows) (packRows rows) = rows.map Row.values := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have hr := h row List.mem_cons_self
    have hl := packPlanes_length row.values row.bytes hr.1
    have ht : ∀ r ∈ rest, r.Valid := fun r hm => h r (List.mem_cons_of_mem row hm)
    simp only [rowLayout, List.map_cons, packRows, List.flatMap_cons, unpackRows]
    rw [← hl, List.take_left, List.drop_left,
      unpackRowPlanes_packPlanes row.values row.bytes hr.1 hr.2]
    exact congrArg (row.values :: ·) (ih ht)

end Pxr24

end Exr