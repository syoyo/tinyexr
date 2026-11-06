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

end Pxr24

end Exr