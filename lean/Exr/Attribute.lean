/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Compression and pixel-type enums, channels, and lines-per-block table.

  The compression table follows the spec and OpenEXR's
  `IlmImf::Compression` ids; DWAA/DWAB are modelled (they are part of the
  container syntax) but flagged unsupported by TinyEXR v3.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Bytes
import Init.Data.Option.Lemmas
import Mathlib.Data.Nat.Bitwise

namespace Exr

/-- Pixel component type (`pixelType` attribute values). -/
inductive PixelType where
  | uint   -- 0
  | half   -- 1
  | float  -- 2
  deriving DecidableEq, Repr, Inhabited

namespace PixelType

def ofBits (u : UInt32) : Option PixelType :=
  match u with
  | 0 => some .uint
  | 1 => some .half
  | 2 => some .float
  | _ => none

def toBits (p : PixelType) : UInt32 :=
  match p with
  | .uint  => 0
  | .half  => 1
  | .float => 2

/-- Size in bytes of one sample of `p`. -/
def sizeBytes (p : PixelType) : Nat :=
  match p with
  | .uint  => 4
  | .half  => 2
  | .float => 4

theorem ofBits_toBits (p : PixelType) : ofBits p.toBits = some p := by
  cases p <;> rfl

theorem toBits_injective : Function.Injective PixelType.toBits := by
  intro a b h; cases a <;> cases b <;> first | rfl | contradiction

end PixelType

/-- Compression attribute values (OpenEXR ids). -/
inductive Compression where
  | none     --  0
  | rle      --  1
  | zips     --  2
  | zip      --  3
  | piz      --  4
  | pxr24    --  5
  | b44      --  6
  | b44a     --  7
  | dwaa     --  8 (TinyEXR v3: unsupported, container modelled only)
  | dwab     --  9 (TinyEXR v3: unsupported, container modelled only)
  | htj2k256 -- 10
  | htj2k32  -- 11
  | zstd     -- 12
  deriving DecidableEq, Repr, Inhabited

namespace Compression

def ofBits (u : UInt8) : Option Compression :=
  match u with
  | 0  => some .none
  | 1  => some .rle
  | 2  => some .zips
  | 3  => some .zip
  | 4  => some .piz
  | 5  => some .pxr24
  | 6  => some .b44
  | 7  => some .b44a
  | 8  => some .dwaa
  | 9  => some .dwab
  | 10 => some .htj2k256
  | 11 => some .htj2k32
  | 12 => some .zstd
  | _  => none

def toBits (c : Compression) : UInt8 :=
  match c with
  | .none     => 0
  | .rle      => 1
  | .zips     => 2
  | .zip      => 3
  | .piz      => 4
  | .pxr24    => 5
  | .b44      => 6
  | .b44a     => 7
  | .dwaa     => 8
  | .dwab     => 9
  | .htj2k256 => 10
  | .htj2k32  => 11
  | .zstd     => 12

theorem ofBits_toBits (c : Compression) : ofBits c.toBits = some c := by
  cases c <;> rfl

theorem toBits_injective : Function.Injective Compression.toBits := by
  intro a b h; cases a <;> cases b <;> first | rfl | contradiction

/-- Scan lines per chunk, from the spec ("Regular Scan Line Blocks"). -/
def linesPerBlock (c : Compression) : Nat :=
  match c with
  | .none     => 1
  | .rle      => 1
  | .zips     => 1
  | .zip      => 16
  | .piz      => 32
  | .pxr24    => 16
  | .b44      => 32
  | .b44a     => 32
  | .dwaa     => 32
  | .dwab     => 256
  | .htj2k256 => 256
  | .htj2k32  => 32
  | .zstd     => 32

theorem linesPerBlock_mem (c : Compression) :
    linesPerBlock c ∈ [1, 16, 32, 256] := by
  cases c <;> simp [linesPerBlock]

/-- The spec permits these compression schemes for deep data. -/
def isDeepAllowed (c : Compression) : Bool :=
  match c with
  | .none | .rle | .zips | .zip => true
  | _ => false

/-- Not lossy (for validation severity). -/
def isUnsupportedLossless (c : Compression) : Bool :=
  match c with
  | .pxr24 => false  -- lossy only for FLOAT channels
  | .b44 | .b44a => false
  | _ => true

/-- TinyEXR v3 never decodes DWAA/DWAB (intentional, see AGENTS.md). -/
def isSupportedByTinyEXR (c : Compression) : Bool :=
  match c with
  | .dwaa | .dwab => false
  | _ => true

end Compression

/-- A channel description from the `channels` (chlist) attribute. -/
structure Channel where
  /-- Channel name bytes, without the terminating NUL. -/
  name : Bytes
  pixelType : PixelType
  pLinear : Bool
  /-- Horizontal sampling (int32 in file, must be ≥ 1). -/
  xSampling : Int32
  /-- Vertical sampling (int32 in file, must be ≥ 1). -/
  ySampling : Int32
  deriving DecidableEq, Repr

namespace Channel

/-- Spec: channels are stored in increasing order of channel name. -/
def StrictlySorted (channels : List Channel) : Prop :=
  channels.Pairwise (fun a b => compare a.name.toList b.name.toList = .lt)

instance (channels : List Channel) : Decidable (StrictlySorted channels) := by
  unfold StrictlySorted; infer_instance

end Channel


/-! ## Raw attribute parsing -/

/-- One step of the cstring scanner; `fuel` bounds the iterations. -/
private def readCStringLoop (b : Bytes) (j fuel : Nat) (acc : Bytes) : Option (Bytes × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if h : j < b.size then
      if (b[j]'h == 0) then
        some (acc, j + 1)
      else
        readCStringLoop b (j + 1) fuel (acc.push (b[j]'h))
    else
      none

theorem readCStringLoop_bounds {b : Bytes} {j fuel : Nat} {acc : Bytes} {s : Bytes} {j' : Nat}
    (h : readCStringLoop b j fuel acc = some (s, j')) :
    j < j' ∧ j' ≤ b.size := by
  induction fuel generalizing j acc with
  | zero =>
    have : readCStringLoop b j 0 acc = none := rfl
    rw [this] at h
    cases h
  | succ fuel ih =>
    unfold readCStringLoop at h
    by_cases hj : j < b.size
    · by_cases hc : b[j]'hj == 0
      · simp [hj, hc] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
      · simp [hj, hc] at h
        have hj' := ih h
        omega
    · simp [hj] at h

/-- Read a NUL-terminated string starting at `i`. Total. -/
def readCString (b : Bytes) (i : Nat) : Option (Bytes × Nat) :=
  if i > b.size then none
  else
    readCStringLoop b i (b.size - i + 1) ByteArray.empty

/-- Bound on a cstring read. -/
theorem readCString_bounds {b : Bytes} {i : Nat} {s : Bytes} {j : Nat}
    (h : readCString b i = some (s, j)) :
    i < j ∧ j ≤ b.size := by
  unfold readCString at h
  split at h
  · contradiction
  · have h' := readCStringLoop_bounds h
    omega

/-- A raw attribute, as parsed from the header. -/
structure RawAttr where
  name : Bytes
  typeName : Bytes
  value : Bytes
  deriving Repr

namespace RawAttr

/-- Maximum name/type-name lengths. -/
def maxShortName : Nat := 31
def maxLongName : Nat := 255

/-- Parse one attribute at `i`. `maxLen` is the c-string length limit for
    this file (31 or 255). Layout: cstring name, cstring type, i32 size
    (must be non-negative), then `size` bytes of value. -/
def parse (b : Bytes) (maxLen : Nat) (i : Nat) : Option (RawAttr × Nat) :=
  if i > b.size then none
  else
    match readCString b i with
    | none => none
    | some (name, i₁) =>
      if ((name.size == 0 || decide (name.size > maxLen)) : Bool) then
        none
      else
        match readCString b i₁ with
        | none => none
        | some (typeName, i₂) =>
          if ((typeName.size == 0 || decide (typeName.size > maxLen)) : Bool) then
            none
          else
            match getU32LE b i₂ with
            | none => none
            | some size32 =>
              if ((size32 &&& 0x80000000 != 0) : Bool) then
                none
              else
                let sz := size32.toNat
                if ((decide (sz > b.size) || decide (i₂ + 4 + sz > b.size)) : Bool) then
                  none
                else
                  let value := b.extract (i₂ + 4) (i₂ + 4 + sz)
                  some ({ name := name, typeName := typeName, value := value }, i₂ + 4 + sz)

/-- Parse attributes up to a terminating 0x00 byte. -/
def parseAll (b : Bytes) (longNames : Bool) (i : Nat) (fuel : Nat) :
    Option (List RawAttr × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if h : i < b.size then
      if b[i]'h == 0 then
        some ([], i + 1)
      else do
        let (a, j) ← parse b (if longNames then maxLongName else maxShortName) i
        let (rest, j') ← parseAll b longNames j fuel
        some (a :: rest, j')
    else
      none

/-- If `parse` succeeds, the cursor advanced past `i` and stays in bounds. -/
theorem parse_bounds {b : Bytes} {maxLen : Nat} {i : Nat} {a : RawAttr} {j : Nat}
    (h : parse b maxLen i = some (a, j)) :
    i < j ∧ j ≤ b.size := by
  unfold parse at h
  by_cases hi : i > b.size
  · simp [hi] at h
  · simp only [hi] at h
    cases h1 : readCString b i with
    | none => simp [h1] at h
    | some p₁ =>
      obtain ⟨name, i₁⟩ := p₁
      simp only [h1] at h
      split at h <;> try contradiction
      cases h2 : readCString b i₁ with
      | none => simp [h2] at h
      | some p₂ =>
        obtain ⟨typeName, i₂⟩ := p₂
        simp only [h2] at h
        by_cases ht : (typeName.size == 0 || decide (typeName.size > maxLen)) = true
        · simp [ht] at h
        · simp [ht] at h
          cases h3 : getU32LE b i₂ with
          | none => simp [h3] at h
          | some size32 =>
            simp only [h3] at h
            have h1b := readCString_bounds h1
            have h2b := readCString_bounds h2
            have h3b := getU32LE_ibounds h3
            by_cases hf : size32 &&& 2147483648 = 0
            · simp [hf] at h
              by_cases hb : b.size < size32.toNat ∨ b.size < i₂ + 4 + size32.toNat
              · omega
              · omega
            · simp [hf] at h

theorem parseAll_terminates {b : Bytes} {longNames : Bool} {i : Nat} {fuel : Nat} {as : List RawAttr} {j : Nat}
    (h : parseAll b longNames i fuel = some (as, j)) :
    j ≤ b.size := by
  induction fuel generalizing i as j with
  | zero =>
    have : parseAll b longNames i 0 = none := rfl
    rw [this] at h
    cases h
  | succ fuel ih =>
    unfold parseAll at h
    by_cases hi : i < b.size
    · by_cases hz : b[i]'hi == 0
      · simp [hi, hz] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
      · simp [hi, hz] at h
        cases hp : parse b (if longNames then maxLongName else maxShortName) i with
        | none => simp [hp] at h
        | some p₁ =>
          obtain ⟨a, j₁⟩ := p₁
          simp only [hp, Option.bind_some] at h
          have hj₁ := parse_bounds hp
          cases hp2 : parseAll b longNames j₁ fuel with
          | none => simp [hp2] at h
          | some p₂ =>
            obtain ⟨rest, j₂⟩ := p₂
            simp only [hp2, Option.bind_some] at h
            have ih₂ := ih hp2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            omega
    · simp [hi] at h

end RawAttr

/-! ## Line order and typed attributes -/

/-- Line order attribute values. -/
inductive LineOrder where
  | increasingY
  | decreasingY
  | randomY
  deriving DecidableEq, Repr, Inhabited

namespace LineOrder

def ofBits (u : UInt8) : Option LineOrder :=
  match u with
  | 0 => some .increasingY
  | 1 => some .decreasingY
  | 2 => some .randomY
  | _ => none

def toBits (l : LineOrder) : UInt8 :=
  match l with
  | .increasingY => 0
  | .decreasingY => 1
  | .randomY     => 2

theorem ofBits_toBits (l : LineOrder) : ofBits l.toBits = some l := by
  cases l <;> rfl

end LineOrder

/-- Ordered box2i (data/display windows). -/
structure Box2i where
  minX : Int32
  minY : Int32
  maxX : Int32
  maxY : Int32
  deriving DecidableEq, Repr, Inhabited

namespace Box2i

def isEmpty (b : Box2i) : Bool :=
  decide (b.maxX < b.minX || b.maxY < b.minY)

def isFinite (_ : Box2i) : Bool := true

/-- Width in pixels (int arithmetic in int64-safe range for i32 windows). -/
def widthInt (b : Box2i) : Int := b.maxX.toInt - b.minX.toInt + 1

/-- Height in pixels (int arithmetic in int64-safe range for i32 windows). -/
def heightInt (b : Box2i) : Int := b.maxY.toInt - b.minY.toInt + 1

end Box2i

/-- IEEE binary32 classification for finite checks (chromaticities). -/
def isFiniteF32 (bits : UInt32) : Bool := (bits &&& 0x7f800000) != 0x7f800000

theorem isFiniteF32_of_bits_lt_pos (bits : UInt32) :
    isFiniteF32 bits = true ↔ (bits &&& 0x7f800000) ≠ 0x7f800000 := by
  simp [isFiniteF32]

/-- The attribute schema understood by the validator. Unknown types are
    accepted with `.unknown` (size-bounded skip). -/
inductive TypedAttr where
  | box2i (b : Box2i)
  | box2f (minX minY maxX maxY : UInt32)  -- f32 bits
  | compression (c : Compression)
  | lineOrder (o : LineOrder)
  | float (bits : UInt32)
  | double (bits : UInt64)
  | int (v : Int32)
  | v2f (a b : UInt32)
  | v3f (a b c : UInt32)
  | m33f (bits : List UInt32)
  | m44f (bits : List UInt32)
  | chromaticities (bits : List UInt32)
  | tiledesc (xSize ySize : UInt32) (levelMode roundingMode : Nat)
  | chlist (channels : List Channel)
  | string (len : Int32) (bytes : Bytes)
  | text (bytes : Bytes)
  | int32List (values : List Int32)
  | unknown (typeName : Bytes) (value : Bytes)
  deriving Repr

/-! ## Typed attribute decoders and schema table -/

namespace TypedAttr

/-- Decode a `chlist` value: sequence of channel entries followed by a single
    0x00 byte. Entries: name (cstring), pixelType (i32: 0/1/2), pLinear
    (u8: 0/1), reserved (3 bytes, must be 0), xSampling (i32 >= 1),
    ySampling (i32 >= 1). Channels must be strictly sorted by name. -/
private def decodeChlistFuel (b : Bytes) (i fuel : Nat) (acc : List Channel) :
    Option (List Channel × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match getU8? b i with
    | none => none
    | some z =>
      match z == 0 with
      | true => some (acc, i + 1)
      | false =>
        match readCString b i with
        | none => none
        | some (name, i₁) =>
          match getU32LE b i₁ with
          | none => none
          | some pt =>
            match PixelType.ofBits pt with
            | none => none
            | some pixelType =>
              match getU8? b (i₁ + 4) with
              | none => none
              | some pl =>
                match getU8? b (i₁ + 5), getU8? b (i₁ + 6), getU8? b (i₁ + 7) with
                | some r0, some r1, some r2 =>
                  match r0 != 0 || r1 != 0 || r2 != 0 with
                  | true => none
                  | false =>
                    match pl != 0 && pl != 1 with
                    | true => none
                    | false =>
                      match getU32LE b (i₁ + 8), getU32LE b (i₁ + 12) with
                      | some xs, some ys =>
                        let xS := xs.toInt32
                        let yS := ys.toInt32
                        match decide (xS ≤ 0) || decide (yS ≤ 0) with
                        | true => none
                        | false =>
                          match decodeChlistFuel b (i₁ + 16) fuel acc with
                          | none => none
                          | some (rest, j) =>
                            some ({ name := name, pixelType := pixelType,
                                    pLinear := pl == 1, xSampling := xS, ySampling := yS } :: rest, j)
                      | _, _ => none
                | _, _, _ => none

/-- Decode a complete `chlist` attribute value. -/
def decodeChlist (b : Bytes) : Option (List Channel × Nat) :=
  decodeChlistFuel b 0 (b.size + 1) []

/-- Chlist decoding stays in bounds. -/
theorem decodeChlistFuel_bounds {b : Bytes} {i fuel : Nat} {acc : List Channel}
    {cs : List Channel} {j : Nat}
    (h : decodeChlistFuel b i fuel acc = some (cs, j)) : j ≤ b.size := by
  induction fuel generalizing i acc cs j with
  | zero =>
    have : decodeChlistFuel b i 0 acc = none := rfl
    rw [this] at h
    cases h
  | succ fuel ih =>
    unfold decodeChlistFuel at h
    cases hz : getU8? b i with
    | none => simp [hz] at h
    | some z =>
      simp only [hz] at h
      cases hz0 : (z == 0) with
      | true =>
        simp [hz0] at h
        obtain ⟨_, rfl⟩ := h
        have hib : i < b.size := getU8?_isSome_lt hz
        omega
      | false =>
        simp [hz0] at h
        cases hcs : readCString b i with
        | none => simp [hcs] at h
        | some p₁ =>
          obtain ⟨name, i₁⟩ := p₁
          simp only [hcs] at h
          cases hpt : getU32LE b i₁ with
          | none => simp [hpt] at h
          | some pt =>
            simp only [hpt] at h
            cases hop : PixelType.ofBits pt with
            | none => simp [hop] at h
            | some pixelType =>
              simp only [hop] at h
              cases hpl : getU8? b (i₁ + 4) with
              | none => simp [hpl] at h
              | some pl =>
                simp only [hpl] at h
                cases hr0 : getU8? b (i₁ + 5) with
                | none => simp [hr0] at h
                | some v0 =>
                  cases hr1 : getU8? b (i₁ + 6) with
                  | none => simp [hr1] at h
                  | some v1 =>
                    cases hr2 : getU8? b (i₁ + 7) with
                    | none => simp [hr2] at h
                    | some v2 =>
                      simp only [hr0, hr1, hr2] at h
                      cases hrz : (v0 != 0 || v1 != 0 || v2 != 0) with
                      | true => simp [hrz] at h
                      | false =>
                        simp [hrz] at h
                        cases hplc : (pl != 0 && pl != 1) with
                        | true => simp [hplc] at h
                        | false =>
                          simp [hplc] at h
                          cases hxs : getU32LE b (i₁ + 8) with
                          | none => simp [hxs] at h
                          | some xs =>
                            cases hys : getU32LE b (i₁ + 12) with
                            | none => simp [hys] at h
                            | some ys =>
                              simp only [hxs, hys] at h
                              cases hsample : (decide (xs.toInt32 ≤ 0) || decide (ys.toInt32 ≤ 0)) with
                              | true => simp [hsample] at h
                              | false =>
                                simp [hsample] at h
                                cases hrec : decodeChlistFuel b (i₁ + 16) fuel acc with
                                | none => simp [hrec] at h
                                | some p₂ =>
                                  obtain ⟨rest, j⟩ := p₂
                                  simp only [hrec] at h
                                  obtain ⟨_, rfl⟩ := h
                                  have := ih hrec
                                  omega

theorem decodeChlist_bounds {b : Bytes} {cs : List Channel} {j : Nat}
    (h : decodeChlist b = some (cs, j)) : j ≤ b.size :=
  decodeChlistFuel_bounds h

end TypedAttr

namespace TypedAttr

/-- Byte-string equality against a literal. -/
def nameEq (b : Bytes) (s : String) : Bool := b == s.toUTF8

/-- Fixed-size attribute types: the exact value-byte count the schema requires.
    `none` for variable-length or unknown types. -/
def fixedSize (typeName : Bytes) : Option Nat :=
  if nameEq typeName "box2i" then some 16
  else if nameEq typeName "box2f" then some 16
  else if nameEq typeName "compression" then some 1
  else if nameEq typeName "lineOrder" then some 1
  else if nameEq typeName "float" then some 4
  else if nameEq typeName "double" then some 8
  else if nameEq typeName "int" then some 4
  else if nameEq typeName "uint" then some 4
  else if nameEq typeName "v2f" then some 8
  else if nameEq typeName "v3f" then some 12
  else if nameEq typeName "v2d" then some 16
  else if nameEq typeName "v3d" then some 24
  else if nameEq typeName "m33f" then some 36
  else if nameEq typeName "m44f" then some 64
  else if nameEq typeName "chromaticities" then some 32
  else if nameEq typeName "tiledesc" then some 9
  else if nameEq typeName "keycode" then some 28
  else if nameEq typeName "rational" then some 8
  else if nameEq typeName "envmap" then some 1
  else none

def decodeBox2i (v : Bytes) : Option Box2i :=
  if v.size == 16 then
    match getI32LE v 0, getI32LE v 4, getI32LE v 8, getI32LE v 12 with
    | some a, some b, some c, some d => some { minX := a, minY := b, maxX := c, maxY := d }
    | _, _, _, _ => none
  else none

theorem decodeBox2i_size {v : Bytes} {x : Box2i} (h : decodeBox2i v = some x) :
    v.size = 16 := by
  unfold decodeBox2i at h
  split at h
  · rename_i hc
    simpa using hc
  · contradiction

def decodeBox2f (v : Bytes) : Option (UInt32 × UInt32 × UInt32 × UInt32) :=
  if v.size == 16 then
    match getU32LE v 0, getU32LE v 4, getU32LE v 8, getU32LE v 12 with
    | some a, some b, some c, some d => some (a, b, c, d)
    | _, _, _, _ => none
  else none

theorem decodeBox2f_size {v : Bytes} {x : UInt32 × UInt32 × UInt32 × UInt32}
    (h : decodeBox2f v = some x) : v.size = 16 := by
  unfold decodeBox2f at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeCompression (v : Bytes) : Option Compression :=
  if v.size == 1 then (getU8? v 0).bind Compression.ofBits else none

theorem decodeCompression_size {v : Bytes} {c : Compression}
    (h : decodeCompression v = some c) : v.size = 1 := by
  unfold decodeCompression at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeLineOrder (v : Bytes) : Option LineOrder :=
  if v.size == 1 then (getU8? v 0).bind LineOrder.ofBits else none

theorem decodeLineOrder_size {v : Bytes} {l : LineOrder}
    (h : decodeLineOrder v = some l) : v.size = 1 := by
  unfold decodeLineOrder at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeFloatBits (v : Bytes) : Option UInt32 :=
  if v.size == 4 then getU32LE v 0 else none

theorem decodeFloatBits_size {v : Bytes} {b : UInt32}
    (h : decodeFloatBits v = some b) : v.size = 4 := by
  unfold decodeFloatBits at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeDoubleBits (v : Bytes) : Option UInt64 :=
  if v.size == 8 then getU64LE v 0 else none

theorem decodeDoubleBits_size {v : Bytes} {b : UInt64}
    (h : decodeDoubleBits v = some b) : v.size = 8 := by
  unfold decodeDoubleBits at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeInt (v : Bytes) : Option Int32 :=
  if v.size == 4 then getI32LE v 0 else none

theorem decodeInt_size {v : Bytes} {x : Int32} (h : decodeInt v = some x) :
    v.size = 4 := by
  unfold decodeInt at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeV2f (v : Bytes) : Option (UInt32 × UInt32) :=
  if v.size == 8 then
    match getU32LE v 0, getU32LE v 4 with
    | some a, some b => some (a, b)
    | _, _ => none
  else none

theorem decodeV2f_size {v : Bytes} {x : UInt32 × UInt32} (h : decodeV2f v = some x) :
    v.size = 8 := by
  unfold decodeV2f at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeV3f (v : Bytes) : Option (UInt32 × UInt32 × UInt32) :=
  if v.size == 12 then
    match getU32LE v 0, getU32LE v 4, getU32LE v 8 with
    | some a, some b, some c => some (a, b, c)
    | _, _, _ => none
  else none

theorem decodeV3f_size {v : Bytes} {x : UInt32 × UInt32 × UInt32}
    (h : decodeV3f v = some x) : v.size = 12 := by
  unfold decodeV3f at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeM44f (v : Bytes) : Option (List UInt32) :=
  if v.size == 64 then
    let rec go (i : Nat) : Option (List UInt32) :=
      match i with
      | 0 => some []
      | i + 1 => (getU32LE v (4 * i)).bind fun w => (go i).map (fun rest => w :: rest)
    go 16
  else none

theorem decodeM44f_size {v : Bytes} {xs : List UInt32} (h : decodeM44f v = some xs) :
    v.size = 64 := by
  unfold decodeM44f at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

def decodeM33f (v : Bytes) : Option (List UInt32) :=
  if v.size == 36 then
    let rec go (i : Nat) : Option (List UInt32) :=
      match i with
      | 0 => some []
      | i + 1 => (getU32LE v (4 * i)).bind fun w => (go i).map (fun rest => w :: rest)
    go 9
  else none

theorem decodeM33f_size {v : Bytes} {xs : List UInt32} (h : decodeM33f v = some xs) :
    v.size = 36 := by
  unfold decodeM33f at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

/-- All entries of a list pass `isFiniteF32`. -/
def allFiniteF32 (xs : List UInt32) : Bool := xs.all isFiniteF32

theorem allFiniteF32_sound {xs : List UInt32} {x : UInt32}
    (h : allFiniteF32 xs = true) (hx : x ∈ xs) : isFiniteF32 x = true := by
  unfold allFiniteF32 at h
  exact List.all_eq_true.mp h x hx

def decodeChromaticities (v : Bytes) : Option (List UInt32) :=
  if v.size == 32 then
    match getU32LE v 0, getU32LE v 4, getU32LE v 8, getU32LE v 12,
          getU32LE v 16, getU32LE v 20, getU32LE v 24, getU32LE v 28 with
    | some a, some b, some c, some d, some e, some f, some g, some h =>
      if allFiniteF32 [a, b, c, d, e, f, g, h] then some [a, b, c, d, e, f, g, h]
      else none
    | _, _, _, _, _, _, _, _ => none
  else none

theorem decodeChromaticities_size {v : Bytes} {xs : List UInt32}
    (h : decodeChromaticities v = some xs) : v.size = 32 := by
  unfold decodeChromaticities at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

theorem decodeChromaticities_finite {v : Bytes} {xs : List UInt32}
    (h : decodeChromaticities v = some xs) : allFiniteF32 xs = true := by
  unfold decodeChromaticities at h
  split at h
  · split at h
    · split at h <;> simp_all
    · contradiction
  · contradiction

/-- Tile level mode (`tiledesc` low nibble). -/
inductive LevelMode where
  | oneLevel
  | mipmap
  | ripmap
  deriving DecidableEq, Repr, Inhabited

/-- Tile rounding mode (`tiledesc` high nibble). -/
inductive RoundingMode where
  | roundDown
  | roundUp
  deriving DecidableEq, Repr, Inhabited

/-- Tiledesc: xSize, ySize (u32), mode byte (levelMode | roundingMode<<4). -/
structure TileDesc where
  xSize : Nat
  ySize : Nat
  levelMode : LevelMode
  roundingMode : RoundingMode
  deriving DecidableEq, Repr

def decodeTileDesc (v : Bytes) : Option TileDesc :=
  if v.size == 9 then
    match getU32LE v 0, getU32LE v 4, getU8? v 8 with
    | some xs, some ys, some mode =>
      let lm := mode.toNat &&& 0x0f
      let rm := (mode.toNat >>> 4) &&& 0x0f
      if lm ≤ 2 && rm ≤ 1 then
        some { xSize := xs.toNat, ySize := ys.toNat,
               levelMode := (if lm = 0 then .oneLevel else if lm = 1 then .mipmap else .ripmap),
               roundingMode := (if rm = 0 then .roundDown else .roundUp) }
      else none
    | _, _, _ => none
  else none

theorem decodeTileDesc_size {v : Bytes} {t : TileDesc} (h : decodeTileDesc v = some t) :
    v.size = 9 := by
  unfold decodeTileDesc at h
  split at h
  · rename_i hc; simpa using hc
  · contradiction

private theorem tileDesc_fields {v : Bytes} {t : TileDesc}
    (h : decodeTileDesc v = some t) :
    (t.xSize < 2 ^ 32 ∧ t.ySize < 2 ^ 32) := by
  unfold decodeTileDesc at h
  split at h
  · rename_i hsz
    cases hx : getU32LE v 0 with
    | none => simp [hx] at h
    | some x =>
      cases hy : getU32LE v 4 with
      | none => simp [hy] at h
      | some y =>
        cases hm : getU8? v 8 with
        | none => simp [hm] at h
        | some m =>
          simp only [hx, hy, hm] at h
          split at h
          · rename_i hcond
            obtain rfl := Option.some.inj h
            exact ⟨UInt32.toNat_lt x, UInt32.toNat_lt y⟩
          · contradiction
  · contradiction

theorem decodeTileDesc_xSize_lt {v : Bytes} {t : TileDesc}
    (h : decodeTileDesc v = some t) : t.xSize < 2 ^ 32 :=
  (tileDesc_fields h).1

theorem decodeTileDesc_ySize_lt {v : Bytes} {t : TileDesc}
    (h : decodeTileDesc v = some t) : t.ySize < 2 ^ 32 :=
  (tileDesc_fields h).2

/-- `string` and `text` values are raw characters; the attribute size gives
    the length (OpenEXR `StringAttribute::writeValueTo`). -/
def decodeString (v : Bytes) : Option Bytes := some v

def decodeText (v : Bytes) : Option Bytes := some v

/-- `int` array attribute (used e.g. by `timeCodes`). Variable length,
    all four-byte little-endian values. -/
def decodeInt32List (v : Bytes) : Option (List Int32) :=
  if v.size % 4 == 0 then
    let rec go (i n : Nat) : Option (List Int32) :=
      match n with
      | 0 => some []
      | n + 1 =>
        (getI32LE v (4 * i)).bind fun w => (go (i + 1) n).map (fun rest => w :: rest)
    go 0 (v.size / 4)
  else none

theorem decodeInt32List_size {v : Bytes} {xs : List Int32}
    (h : decodeInt32List v = some xs) : v.size % 4 = 0 := by
  unfold decodeInt32List at h
  split at h
  · rename_i hc
    simpa using hc
  · contradiction

/-- Decode a raw attribute's value according to its type name. Unknown
    types (application-defined) are accepted as `.unknown`. -/
def decodeTyped (a : RawAttr) : Option TypedAttr :=
  if nameEq a.typeName "box2i" then (decodeBox2i a.value).map .box2i
  else if nameEq a.typeName "box2f" then
    (decodeBox2f a.value).map fun (a1, b1, c1, d1) => .box2f a1 b1 c1 d1
  else if nameEq a.typeName "compression" then (decodeCompression a.value).map .compression
  else if nameEq a.typeName "lineOrder" then (decodeLineOrder a.value).map .lineOrder
  else if nameEq a.typeName "float" then (decodeFloatBits a.value).map .float
  else if nameEq a.typeName "double" then (decodeDoubleBits a.value).map .double
  else if nameEq a.typeName "int" then (decodeInt a.value).map .int
  else if nameEq a.typeName "v2f" then (decodeV2f a.value).map fun (x, y) => .v2f x y
  else if nameEq a.typeName "v3f" then
    (decodeV3f a.value).map fun (x, y, z) => .v3f x y z
  else if nameEq a.typeName "m33f" then (decodeM33f a.value).map .m33f
  else if nameEq a.typeName "m44f" then (decodeM44f a.value).map .m44f
  else if nameEq a.typeName "chromaticities" then
    (decodeChromaticities a.value).map .chromaticities
  else if nameEq a.typeName "tiledesc" then
    (decodeTileDesc a.value).map fun t => .tiledesc t.xSize.toUInt32 t.ySize.toUInt32 0 0
  else if nameEq a.typeName "channels" then
    (decodeChlist a.value).map fun (cs, _) => .chlist cs
  else if nameEq a.typeName "string" then (decodeString a.value).map fun b => .string 0 b
  else if nameEq a.typeName "text" then (decodeText a.value).map .text
  else if nameEq a.typeName "int" then (decodeInt a.value).map .int
  else some (.unknown a.typeName a.value)

end TypedAttr

/-! ### Parse / emit round trip for attribute strings -/

namespace RawAttr

/-- A byte array contains no NUL byte. -/
def NoNul (b : Bytes) : Prop := ∀ i, getU8? b i ≠ some 0

/-- The zero byte used to terminate names and headers. -/
def nulByte : Bytes := ByteArray.mk #[0]

theorem nulByte_size : nulByte.size = 1 := rfl

/-- Normalize append nesting to the right. -/
theorem app_norm {a b c d : Bytes} :
    ((a ++ b) ++ c) ++ d = a ++ (b ++ (c ++ d)) := by
  simp only [ByteArray.append_assoc]

theorem getU8?_nul_at {p rest : Bytes} :
    getU8? (p ++ (nulByte ++ rest)) p.size = some 0 := by
  rw [getU8?_append_right (a := p) (b := nulByte ++ rest) (i := p.size) (by simp)]
  have h2 : p.size - p.size = 0 := by omega
  rw [h2]
  rw [getU8?_append_left (a := nulByte) (b := rest) (i := 0) (by rw [nulByte_size]; omega)]
  rfl

theorem getU8?_left_at {p s : Bytes} {i : Nat} (h : i < s.size) :
    getU8? (p ++ (s ++ (nulByte ++ rest))) (p.size + i) = getU8? s i := by
  rw [getU8?_append_right (a := p) (b := s ++ (nulByte ++ rest)) (i := p.size + i) (by omega)]
  have h2 : p.size + i - p.size = i := by omega
  rw [h2]
  exact getU8?_append_left (a := s) (b := nulByte ++ rest) (i := i) h

/-- Reading a NUL-terminated string embedded after a prefix: the loop consumes
    exactly the string and its terminator, appending the string to the
    accumulator. The prefix may contain arbitrary bytes; only the scanned
    suffix must be NUL-free. -/
theorem readCStringLoop_emit_at_gen (p s rest : Bytes) (hn : NoNul s) :
    ∀ (i : Nat) (acc : Bytes) (fuel : Nat), i ≤ s.size → s.size - i + 1 ≤ fuel →
      readCStringLoop (p ++ (s ++ (nulByte ++ rest))) (p.size + i) fuel acc
        = some (acc ++ s.extract i s.size, p.size + s.size + 1) := by
  intro i acc fuel
  induction fuel generalizing i acc with
  | zero => intro hi hf; omega
  | succ fuel ih =>
    intro hi hf
    unfold readCStringLoop
    by_cases hlt : i < s.size
    · have hltb : p.size + i < (p ++ (s ++ (nulByte ++ rest))).size := by
        simp only [ByteArray.size_append]; omega
      have hby : (p ++ (s ++ (nulByte ++ rest)))[p.size + i]'hltb = s[i]'hlt := by
        have h1 := getU8?_left_at (p := p) (rest := rest) (i := i) hlt
        rw [getU8?_of_lt hltb, getU8?_of_lt hlt] at h1
        exact Option.some.inj h1
      have hne : (s[i]'hlt == 0) = false := by
        cases hc : (s[i]'hlt == 0) with
        | true =>
          exfalso
          have hsome : getU8? s i = some 0 := by
            rw [getU8?_of_lt hlt]; congr 1; simpa using hc
          exact hn i hsome
        | false => rfl
      rw [dite_eq_left hltb, hby, hne]
      simp only [Bool.false_eq_true, ite_false]
      have hfuel : s.size - (i + 1) + 1 ≤ fuel := by omega
      have hrec := ih (i := i + 1) (acc := acc.push (s[i]'hlt)) (by omega) hfuel
      rw [show ByteArray.size p + (i + 1) = ByteArray.size p + i + 1 by omega] at hrec
      rw [hrec]
      congr 1
      rw [ByteArray.extract_eq_extract_append_extract (a := s) (i := i) (j := i + 1)
          (k := s.size) (by omega) (by omega)]
      rw [ByteArray.extract_add_one (a := s) (i := i) (by omega)]
      rw [← ByteArray.append_assoc]
      rw [ByteArray.append_toByteArray_singleton]
    · have hie : i = s.size := by omega
      subst hie
      have hltb : p.size + s.size < (p ++ (s ++ (nulByte ++ rest))).size := by
        simp only [ByteArray.size_append, nulByte_size]; omega
      rw [dite_eq_left hltb]
      have hbeq : ((p ++ (s ++ (nulByte ++ rest)))[p.size + s.size]'hltb == 0) = true := by
        have hz := getU8?_nul_at (p := p ++ s) (rest := rest)
        have heq : (p ++ s) ++ (nulByte ++ rest) = p ++ (s ++ (nulByte ++ rest)) :=
          ByteArray.append_assoc ..
        rw [heq] at hz
        rw [ByteArray.size_append] at hz
        rw [getU8?_of_lt hltb] at hz
        have h0 : (p ++ (s ++ (nulByte ++ rest)))[p.size + s.size]'hltb = 0 :=
          Option.some.inj hz
        rw [h0]; rfl
      rw [hbeq]
      simp only [ite_true]
      congr 1
      rw [ByteArray.extract_same, ByteArray.append_empty]

/-- Reading a NUL-terminated string embedded after a prefix returns exactly
    that string. -/
theorem readCString_emit_at (p s rest : Bytes) (hn : NoNul s) :
    readCString (p ++ (s ++ (nulByte ++ rest))) p.size
      = some (s, p.size + s.size + 1) := by
  unfold readCString
  have hle : ¬ p.size > (p ++ (s ++ (nulByte ++ rest))).size := by
    simp only [ByteArray.size_append, nulByte_size]; omega
  simp only [hle, ite_false]
  have hfuel : s.size - 0 + 1 ≤ (p ++ (s ++ (nulByte ++ rest))).size - p.size + 1 := by
    simp only [ByteArray.size_append]; omega
  have hmain := readCStringLoop_emit_at_gen (p := p) (s := s) (rest := rest) hn
      (i := 0) (acc := ByteArray.empty)
      (fuel := (p ++ (s ++ (nulByte ++ rest))).size - p.size + 1)
      (by omega) hfuel
  simpa using hmain

end RawAttr

namespace RawAttr

/-- Wire encoding of a u32 value with a validity bound. -/
theorem getU32LE_u32Bytes (n : Nat) (_hn : n < 2 ^ 32) :
    getU32LE (putU32LE (UInt32.ofNat n) ByteArray.empty) 0 = some (UInt32.ofNat n) := by
  simpa using getU32LE_putU32LE (acc := ByteArray.empty) (v := UInt32.ofNat n)

theorem u32Bytes_size (n : Nat) : (putU32LE (UInt32.ofNat n) ByteArray.empty).size = 4 := by
  simp [putU32LE]

theorem u32Bytes_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n := by
  simpa using Nat.mod_eq_of_lt hn

/-- Well-formedness conditions for an attribute's wire form. -/
structure Emittable (a : RawAttr) (maxLen : Nat) : Prop where
  nameNonempty : 1 ≤ a.name.size
  nameLen : a.name.size ≤ maxLen
  nameNoNul : NoNul a.name
  typeNonempty : 1 ≤ a.typeName.size
  typeLen : a.typeName.size ≤ maxLen
  typeNoNul : NoNul a.typeName
  valueSize : a.value.size < 2 ^ 31

/-- Emitted attribute bytes (name NUL type NUL size value). -/
def wire (a : RawAttr) : Bytes :=
  a.name ++ (nulByte ++ (a.typeName ++ (nulByte ++
    (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))))

/-- Discharge a `(decide (x > n) || decide (y > n))` guard given arithmetic
    bounds. -/
theorem ite_or_decide_false {x y n : Nat} {α : Type} {A B : Option α}
    (hx : ¬ x > n) (hy : ¬ y > n) :
    (if (decide (x > n) || decide (y > n)) = true then A else B) = B := by
  simp [decide_eq_false hx, decide_eq_false hy]

/-- Parsing the emitted bytes yields the original attribute. -/
theorem parse_wire (a : RawAttr) (maxLen : Nat) (hw : Emittable a maxLen) :
    parse (wire a) maxLen 0
      = some (a, a.name.size + 1 + a.typeName.size + 1 + 4 + a.value.size) := by
  obtain ⟨hn1, hn2, hnn, ht1, ht2, htt, hv⟩ := hw
  unfold wire
  -- name
  have hname := readCString_emit_at (p := ByteArray.empty) (s := a.name)
    (rest := a.typeName ++ (nulByte ++
      (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))) hnn
  simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at hname
  unfold parse
  split <;> (try omega)
  simp only [hname]
  -- name length guard is false
  have hng : ¬ (a.name.size == 0 || decide (a.name.size > maxLen)) = true := by
    intro hc
    rcases Bool.or_eq_true .. |>.mp hc with h0 | hgt
    · have : a.name.size = 0 := by simpa using h0
      omega
    · have : a.name.size > maxLen := of_decide_eq_true hgt
      omega
  rw [ite_eq_right hng]
  -- type name
  have hassoc : a.name ++ (nulByte ++ (a.typeName ++ (nulByte ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))))
      = (a.name ++ nulByte) ++ (a.typeName ++ (nulByte ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))) :=
    (ByteArray.append_assoc (a := a.name) (b := nulByte)
      (c := a.typeName ++ (nulByte ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)))).symm
  rw [hassoc]
  have htype := readCString_emit_at (p := a.name ++ nulByte) (s := a.typeName)
    (rest := (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)) htt
  simp only [ByteArray.size_append, nulByte_size] at htype
  simp only [htype]
  have htng : ¬ (a.typeName.size == 0 || decide (a.typeName.size > maxLen)) = true := by
    intro hc
    rcases Bool.or_eq_true .. |>.mp hc with h0 | hgt
    · have : a.typeName.size = 0 := by simpa using h0
      omega
    · have : a.typeName.size > maxLen := of_decide_eq_true hgt
      omega
  rw [ite_eq_right htng]
  -- size field
  have hszoff : ((a.name ++ nulByte) ++ (a.typeName ++ (nulByte ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))))
      = ((a.name ++ nulByte) ++ (a.typeName ++ nulByte)) ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value) := by
    rw [← ByteArray.append_assoc (a := a.typeName) (b := nulByte)
      (c := putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)]
    rw [← ByteArray.append_assoc (a := a.name ++ nulByte) (b := a.typeName ++ nulByte)
      (c := putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)]
  rw [hszoff]
  have hszread : getU32LE (((a.name ++ nulByte) ++ (a.typeName ++ nulByte)) ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value))
        (a.name.size + 1 + a.typeName.size + 1)
      = some (UInt32.ofNat a.value.size) := by
    have hpre : ((a.name ++ nulByte) ++ (a.typeName ++ nulByte)).size
        = a.name.size + 1 + a.typeName.size + 1 := by
      simp only [ByteArray.size_append, nulByte_size]; omega
    rw [← hpre]
    rw [getU32LE_append_right]
    exact getU32LE_u32Bytes_append _ _
  simp only [hszread]
  -- sign bit clear (value sizes are < 2^31)
  have hsign : ¬ (UInt32.ofNat a.value.size &&& 0x80000000 != 0) = true := by
    intro hc
    have hb : (UInt32.ofNat a.value.size &&& 0x80000000) ≠ 0 := by
      simpa using hc
    have hz : (UInt32.ofNat a.value.size &&& 0x80000000) = 0 := by
      rw [← UInt32.toNat_inj]
      have h1 : (UInt32.ofNat a.value.size &&& 0x80000000).toNat
          = (UInt32.ofNat a.value.size).toNat &&& (0x80000000 : UInt32).toNat := rfl
      rw [h1, u32Bytes_toNat (by omega)]
      have h31 : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
      rw [h31, Nat.and_two_pow]
      have htb : (a.value.size.testBit 31) = false := by
        apply Nat.testBit_eq_false_of_lt
        omega
      rw [htb]
      rfl
    exact hb hz
  rw [ite_eq_right hsign]
  -- bounds guard false
  have hbnd : ¬ (decide ((UInt32.ofNat a.value.size).toNat > ((a.name ++ nulByte) ++
        (a.typeName ++ nulByte) ++ (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)).size) ||
      decide (((a.name ++ nulByte) ++ (a.typeName ++ nulByte)).size + 4 +
        (UInt32.ofNat a.value.size).toNat > ((a.name ++ nulByte) ++
        (a.typeName ++ nulByte) ++ (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)).size)) = true := by
    intro hc
    rcases Bool.or_eq_true .. |>.mp hc with hg1 | hg2
    · have h1 := of_decide_eq_true hg1
      rw [u32Bytes_toNat (by omega)] at h1
      simp only [ByteArray.size_append, nulByte_size, u32Bytes_size] at h1
      omega
    · have h2 := of_decide_eq_true hg2
      rw [u32Bytes_toNat (by omega)] at h2
      simp only [ByteArray.size_append, nulByte_size, u32Bytes_size] at h2
      omega
  -- extract the value and compare
  have hval : ((a.name ++ nulByte ++ (a.typeName ++ nulByte)) ++
        (putU32LE (UInt32.ofNat a.value.size) ByteArray.empty ++ a.value)).extract
        ((a.name ++ nulByte ++ (a.typeName ++ nulByte)).size + 4)
        ((a.name ++ nulByte ++ (a.typeName ++ nulByte)).size + 4 +
          (UInt32.ofNat a.value.size).toNat)
      = a.value := by
    rw [u32Bytes_toNat (by omega)]
    rw [← ByteArray.append_assoc]
    rw [show (a.name ++ nulByte ++ (a.typeName ++ nulByte)).size + 4
          = ((a.name ++ nulByte ++ (a.typeName ++ nulByte)) ++
              putU32LE (UInt32.ofNat a.value.size) ByteArray.empty).size by
        simp only [ByteArray.size_append, u32Bytes_size]]
    exact extract_append_right_eq
  rw [ite_or_decide_false]
  · -- main goal: success form
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · -- record identity: the extracted value is the original value
      rw [show a.name.size + 1 + a.typeName.size + 1 + 4
            = (a.name ++ nulByte ++ (a.typeName ++ nulByte)).size + 4 by
          simp only [ByteArray.size_append, nulByte_size]; omega]
      rw [hval]
    · -- cursor arithmetic
      rw [u32Bytes_toNat (by omega)]
  · -- first bounds side condition
    intro h
    rw [u32Bytes_toNat (by omega)] at h
    simp only [ByteArray.size_append, nulByte_size, u32Bytes_size] at h
    omega
  · -- second bounds side condition
    intro h
    rw [u32Bytes_toNat (by omega)] at h
    simp only [ByteArray.size_append, nulByte_size, u32Bytes_size] at h
    omega

end RawAttr
