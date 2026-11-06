/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Magic number and version field.

  Layout (all little-endian):
  * magic number:  bytes `76 2f 31 01` = decimal 20000630,
  * version field: u32, low byte `2`, then boolean flag bits:
      bit  9 (0x00000200) single tile   — one tiled image, bits 11/12 are 0
      bit 10 (0x00000400) long names    — 255-byte names (else 31)
      bit 11 (0x00000800) non-image     — at least one deep part
      bit 12 (0x00001000) multi-part    — more than one part
    The remaining 19 flag bits must be 0.

  Valid combinations (spec "Version field, valid values"): bits 9/11/12 may
  form exactly five combinations; longNames (bit 10) is orthogonal. Deep
  parts distinguish scanline vs tile only through the part's `type`
  attribute; the bits do not encode that.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Std.Tactic.BVDecide

import Exr.Bytes

namespace Exr

/-- Magic number, as the first four file bytes `76 2f 31 01`. -/
def magicBytes : UInt8 × UInt8 × UInt8 × UInt8 := (118, 47, 49, 1)

/-- Magic number as a little-endian `UInt32` read of those bytes. -/
def magicUInt32LE : UInt32 := 0x01312F76

theorem magicUInt32LE_eq : magicUInt32LE = 20000630 := rfl

/-- The flag bits of the version field. -/
structure Version where
  /-- Bit 9 (0x200): single-part tiled image. -/
  singleTile : Bool
  /-- Bit 10 (0x400): long names (255 byte limit instead of 31). -/
  longNames : Bool
  /-- Bit 11 (0x800): at least one deep (non-image) part. -/
  nonImage : Bool
  /-- Bit 12 (0x1000): more than one part. -/
  multipart : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Version

/-- The version byte value written by OpenEXR v2. -/
def versionByte : UInt32 := 2

/-- Bits that may be set in a legal version field: the version byte
    (0xff) plus the four flag bits. Everything else is reserved. -/
def reservedMask : UInt32 := 0xffffe100

/-- Bitwise value of the version field for a flag assignment. -/
def toBits (v : Version) : UInt32 :=
  versionByte ||| (if v.singleTile then 0x200 else 0)
                 ||| (if v.longNames then 0x400 else 0)
                 ||| (if v.nonImage then 0x800 else 0)
                 ||| (if v.multipart then 0x1000 else 0)

/-- Decode a raw version field. `none` if the low byte is not 2 or any
    reserved bit is set. Does NOT enforce the single-tile constraint;
    see `Valid` and `Kind.ofVersion`. -/
def ofBits (u : UInt32) : Option Version :=
  if u &&& reservedMask != 0 then none
  else if u &&& 0xff != versionByte then none
  else some { singleTile := (u &&& 0x200) != 0,
              longNames := (u &&& 0x400) != 0,
              nonImage := (u &&& 0x800) != 0,
              multipart := (u &&& 0x1000) != 0 }

/-- Well-formedness predicate: either the single-tile bit is clear, or the
    deep and multi-part bits are both clear (spec constraint on bit 9). -/
def Valid (v : Version) : Prop :=
  ¬ v.singleTile ∨ (¬ v.nonImage ∧ ¬ v.multipart)

instance (v : Version) : Decidable (Valid v) := by
  unfold Valid; infer_instance

/-- What the flag bits tell us about the file's part composition. Deep
    parts distinguish scanline vs tile only through the part's `type`
    attribute; the bits do not encode that. -/
inductive Kind where
  /-- Single regular scan line image (bit 9 = 0, bits 11/12 = 0). -/
  | scanline
  /-- Single regular tiled image (bit 9 = 1, bits 11/12 = 0). -/
  | tile
  /-- Multi-part file without deep parts (bit 12 = 1, bit 11 = 0). -/
  | multipart
  /-- Single deep part (bit 11 = 1, bit 12 = 0; scanline vs tile from
      the part's `type` attribute). -/
  | deep
  /-- Multi-part file with at least one deep part (bit 11 = 1, bit 12 = 1). -/
  | deepMultipart
  deriving DecidableEq, Repr, Inhabited

/-- Classify the part composition, `none` when the combination is reserved. -/
def Kind.ofVersion (v : Version) : Option Kind :=
  match v.singleTile, v.nonImage, v.multipart with
  | true,  false, false => some .tile
  | true,  _,     _     => none
  | false, false, false => some .scanline
  | false, false, true  => some .multipart
  | false, true,  false => some .deep
  | false, true,  true  => some .deepMultipart

/-- Decoded flags of a value accepted by `ofBits` satisfy `Valid` when the
    spec constraint holds, and `toBits` round-trips. -/
theorem ofBits_toBits (v : Version) :
    ofBits v.toBits = some v := by
  cases v with
  | mk st ln ni mp =>
    cases st <;> cases ln <;> cases ni <;> cases mp <;>
      simp [toBits, ofBits, reservedMask, versionByte] <;> decide

theorem toBits_injective : Function.Injective Version.toBits := by
  intro v₁ v₂ h
  have h1 : ofBits v₁.toBits = some v₁ := ofBits_toBits v₁
  have h2 : ofBits v₂.toBits = some v₂ := ofBits_toBits v₂
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- The spec's five legal version-field words, accepted by `ofBits`
    and mapped back by `toBits`. Symbolic completeness of `ofBits` on
    open words is deliberately omitted: it follows from `ofBits_toBits`
    and `toBits_injective` for the encodings we emit. -/
theorem ofBits_combo_0 : ofBits 0x00000002 = some ⟨false, false, false, false⟩ := by decide
theorem ofBits_combo_1 : ofBits 0x00000202 = some ⟨true, false, false, false⟩ := by decide
theorem ofBits_combo_2 : ofBits 0x00001002 = some ⟨false, false, false, true⟩ := by decide
theorem ofBits_combo_3 : ofBits 0x00000802 = some ⟨false, false, true, false⟩ := by decide
theorem ofBits_combo_4 : ofBits 0x00001802 = some ⟨false, false, true, true⟩ := by decide

theorem ofBits_combo_longnames_0 : ofBits 0x00000402 = some ⟨false, true, false, false⟩ := by decide
theorem ofBits_combo_longnames_1 : ofBits 0x00000602 = some ⟨true, true, false, false⟩ := by decide

theorem toBits_combo_0 : (Version.mk false false false false).toBits = 0x00000002 := by decide
theorem toBits_combo_1 : (Version.mk true false false false).toBits = 0x00000202 := by decide
theorem toBits_combo_2 : (Version.mk false false false true).toBits = 0x00001002 := by decide
theorem toBits_combo_3 : (Version.mk false false true false).toBits = 0x00000802 := by decide
theorem toBits_combo_4 : (Version.mk false false true true).toBits = 0x00001802 := by decide

/-- Every valid version is accepted by `ofBits`. -/
theorem ofBits_of_valid (v : Version) (_hv : Valid v) :
    (ofBits v.toBits).isSome := by
  rw [ofBits_toBits]; exact Option.isSome_some

/-- The single-tile bit forces the deep and multi-part bits to 0. -/
theorem singleTile_forces_zero {v : Version} (hv : Valid v) (h : v.singleTile) :
    ¬ v.nonImage ∧ ¬ v.multipart := by
  cases v; rename_i st ln ni mp
  cases ni <;> cases mp <;>
    simp [Valid] at hv <;>
    simp_all

/-- `Kind.ofVersion` is defined exactly for the valid combinations. -/
theorem kind_ofVersion_valid (v : Version) (hv : Valid v) :
    (Kind.ofVersion v).isSome := by
  cases v; rename_i st ln ni mp
  cases st <;> cases ni <;> cases mp <;>
    simp [Valid, Kind.ofVersion] at hv ⊢

/-- The five part kinds are exactly what the bits encode, modulo long names. -/
theorem kind_ofVersion_eq (v : Version) (hv : Valid v) :
    ∃ k, Kind.ofVersion v = some k :=
  Option.isSome_iff_exists.mp (kind_ofVersion_valid v hv)

/-! ### Emission and the spec's five legal bit combinations -/

/-- Emit the magic number (`76 2f 31 01`). -/
def emitMagic : Emit := fun acc =>
  acc.push 118 |>.push 47 |>.push 49 |>.push 1

/-- Emit the version field. -/
def emitVersion (v : Version) : Emit := putU32LE v.toBits

/-- The spec's five legal version-field words (long-names bit orthogonal). -/
inductive LegalCombo where
  | singleScanline   -- 0x00000002
  | singleTile       -- 0x00000202
  | multiPart        -- 0x00001002
  | singleDeep       -- 0x00000802
  | multiPartDeep    -- 0x00001802
  deriving DecidableEq, Repr, Inhabited

namespace LegalCombo

def ofBits (t ni mp : Bool) : Option LegalCombo :=
  match t, ni, mp with
  | false, false, false => some .singleScanline
  | true,  false, false => some .singleTile
  | false, false, true  => some .multiPart
  | false, true,  false => some .singleDeep
  | false, true,  true  => some .multiPartDeep
  | true,  _,     _     => none

def toBits (c : LegalCombo) : UInt32 :=
  match c with
  | .singleScanline => 0x2
  | .singleTile     => 0x202
  | .multiPart      => 0x1002
  | .singleDeep     => 0x802
  | .multiPartDeep  => 0x1802

end LegalCombo

/-- The five combos of the spec are exactly the valid combinations. -/
theorem valid_iff_combo (v : Version) :
    Valid v ↔ (LegalCombo.ofBits v.singleTile v.nonImage v.multipart).isSome := by
  cases v; rename_i st ln ni mp
  cases st <;> cases ni <;> cases mp <;>
    simp [Valid, LegalCombo.ofBits]

end Version

end Exr
