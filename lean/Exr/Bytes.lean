/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Byte-level layer: little-endian integers, half/float bit patterns, and a
  small lemma library about `getU8?` and `ByteArray` appends/pushes.

  Design notes:
  * All readers are total; out-of-bounds reads return `none`, never panic.
  * Emitters are functions `ByteArray → ByteArray` ("difference lists"), so
    concatenation is composition and associativity is definitional.
  * Floats are modelled as raw bit patterns (`UInt16`/`UInt32`); no float
    semantics are assumed here.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Std.Tactic.BVDecide

namespace Exr

/-- Errors produced by the byte and format layers. -/
inductive Error where
  /-- Ran out of bytes mid-read. -/
  | truncated
  deriving Repr, DecidableEq, Inhabited

/-- An OpenEXR byte string is a `ByteArray`. -/
abbrev Bytes := ByteArray

instance : Repr Bytes := ⟨fun _ _ => "⟨bytes⟩"⟩

/-- Total byte read. `none` past the end of the array; never out of bounds. -/
def getU8? (b : Bytes) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some (b[i]'h) else none

@[simp] theorem getU8?_of_lt {b : Bytes} {i : Nat} (h : i < b.size) :
    getU8? b i = some (b[i]'h) := by
  simp [getU8?, h]

@[simp] theorem getU8?_of_ge {b : Bytes} {i : Nat} (h : ¬ i < b.size) :
    getU8? b i = none := by
  simp [getU8?, h]

@[simp] theorem getU8?_size (b : Bytes) : getU8? b b.size = none := by
  simp [getU8?]

/-- A successful byte read implies the index is in bounds. -/
theorem getU8?_isSome_lt {b : Bytes} {i : Nat} {v : UInt8} (h : getU8? b i = some v) :
    i < b.size := by
  by_cases hlt : i < b.size
  · exact hlt
  · rw [getU8?_of_ge hlt] at h
    cases h

theorem getU8?_eq_some_iff {b : Bytes} {i : Nat} {v : UInt8} (h : i < b.size) :
    getU8? b i = some v ↔ b[i]'h = v := by
  simp [getU8?, h]

theorem getElem_push_byte (b : Bytes) (v : UInt8) :
    (b.push v)[b.size]'(by simp only [ByteArray.size_push]; omega) = v := by
  simp [ByteArray.getElem_eq_getElem_data, ← ByteArray.size_data, Array.getElem_push_eq]

/-- Index the last byte of a singleton push; the index equation is carried
    explicitly so callers never rewrite inside a dependent `getElem` proof. -/
theorem getElem_push_of_size_eq {b : Bytes} {v : UInt8} {i : Nat} (h : i = b.size) :
    (b.push v)[i]'(h.symm ▸ by simp only [ByteArray.size_push]; omega) = v := by
  subst h; exact getElem_push_byte b v

theorem getElem_push_lt_byte {b : Bytes} {v : UInt8} {i : Nat} (h : i < b.size) :
    (b.push v)[i]'(by simp only [ByteArray.size_push]; omega) = b[i]'h := by
  simp [ByteArray.getElem_eq_getElem_data, Array.getElem_push_lt h]

theorem getU8?_push_eq (b : Bytes) (v : UInt8) :
    getU8? (b.push v) b.size = some v := by
  have h' : b.size < (b.push v).size := by simp only [ByteArray.size_push]; omega
  rw [getU8?_of_lt h', getElem_push_byte]

theorem getU8?_push_lt {b : Bytes} {v : UInt8} {i : Nat} (h : i < b.size) :
    getU8? (b.push v) i = getU8? b i := by
  have h' : i < (b.push v).size := by simp only [ByteArray.size_push]; omega
  rw [getU8?_of_lt h', getU8?_of_lt h, getElem_push_lt_byte h]

/-- Slice of `b` from `i` to `i + n` (as a fresh array). -/
def slice? (b : Bytes) (i n : Nat) : Option Bytes :=
  if i + n ≤ b.size then some (b.extract i (i + n)) else none

theorem slice?_self (b : Bytes) : slice? b 0 b.size = some b := by
  simp [slice?, ByteArray.extract_zero_size]

/-! ### Emitters (difference lists) -/

/-- An emitter extends a byte-array context by writing some bytes.
    Composition of emitters is function composition, so nesting parse
    proofs never has to reassociate appends. -/
abbrev Emit := Bytes → Bytes

namespace Emit

/-- Convenience wrapper so emitters read `Emit.seq' e₁ e₂` in writing order. -/
def seq' (e₁ : Emit) (e₂ : Emit) : Emit := e₂ ∘ e₁

@[simp] theorem seq'_def (e₁ e₂ : Emit) : seq' e₁ e₂ = e₂ ∘ e₁ := rfl

/-- The empty emitter writes nothing. -/
def empty : Emit := id

@[simp] theorem empty_def : empty = id := rfl

@[simp] theorem empty_empty : empty ByteArray.empty = ByteArray.empty := rfl

@[simp] theorem seq'_empty (e : Emit) : seq' e empty = e := rfl

@[simp] theorem empty_seq' (e : Emit) : seq' empty e = e := rfl

end Emit

/-! ### Little-endian scalar writers/readers -/

def putU8 (v : UInt8) : Emit := fun acc => acc.push v

def getU8 (b : Bytes) (i : Nat) : Option UInt8 := getU8? b i

def putU16LE (v : UInt16) : Emit := fun acc =>
  acc.push (v &&& 0xff).toUInt8
     |>.push ((v >>> 8) &&& 0xff).toUInt8

def getU16LE (b : Bytes) (i : Nat) : Option UInt16 := do
  let lo ← getU8 b i
  let hi ← getU8 b (i + 1)
  pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))

def putU32LE (v : UInt32) : Emit := fun acc =>
  acc.push (v &&& 0xff).toUInt8
     |>.push ((v >>> 8) &&& 0xff).toUInt8
     |>.push ((v >>> 16) &&& 0xff).toUInt8
     |>.push ((v >>> 24) &&& 0xff).toUInt8

def getU32LE (b : Bytes) (i : Nat) : Option UInt32 := do
  let b0 ← getU8 b i
  let b1 ← getU8 b (i + 1)
  let b2 ← getU8 b (i + 2)
  let b3 ← getU8 b (i + 3)
  pure (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24))

def putU64LE (v : UInt64) : Emit := fun acc =>
  acc.push (v &&& 0xff).toUInt8
     |>.push ((v >>> 8) &&& 0xff).toUInt8
     |>.push ((v >>> 16) &&& 0xff).toUInt8
     |>.push ((v >>> 24) &&& 0xff).toUInt8
     |>.push ((v >>> 32) &&& 0xff).toUInt8
     |>.push ((v >>> 40) &&& 0xff).toUInt8
     |>.push ((v >>> 48) &&& 0xff).toUInt8
     |>.push ((v >>> 56) &&& 0xff).toUInt8

def getU64LE (b : Bytes) (i : Nat) : Option UInt64 := do
  let b0 ← getU8 b i
  let b1 ← getU8 b (i + 1)
  let b2 ← getU8 b (i + 2)
  let b3 ← getU8 b (i + 3)
  let b4 ← getU8 b (i + 4)
  let b5 ← getU8 b (i + 5)
  let b6 ← getU8 b (i + 6)
  let b7 ← getU8 b (i + 7)
  pure (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
        (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))

/-- Signed 32-bit little-endian read (two's complement). -/
def getI32LE (b : Bytes) (i : Nat) : Option Int32 := do
  let v ← getU32LE b i
  pure v.toInt32

/-- Signed 64-bit little-endian read (two's complement). -/
def getI64LE (b : Bytes) (i : Nat) : Option Int64 := do
  let v ← getU64LE b i
  pure v.toInt64

def putI32LE (v : Int32) : Emit := putU32LE v.toUInt32

def putI64LE (v : Int64) : Emit := putU64LE v.toUInt64

/-- IEEE binary16 bits (opaque). -/
def putF16Bits (v : UInt16) : Emit := putU16LE v

def getF16Bits (b : Bytes) (i : Nat) : Option UInt16 := getU16LE b i

/-- IEEE binary32 bits (opaque). -/
def putF32Bits (v : UInt32) : Emit := putU32LE v

def getF32Bits (b : Bytes) (i : Nat) : Option UInt32 := getU32LE b i

/-- Four-byte reads stay in bounds. -/
theorem getU32LE_ibounds {b : Bytes} {i : Nat} {v : UInt32}
    (h : getU32LE b i = some v) : i + 4 ≤ b.size := by
  by_cases hi : i + 4 ≤ b.size
  · exact hi
  · exfalso
    have hi' : ¬ i + 3 < b.size := by omega
    have hnone : getU8 b (i + 3) = none := by rw [getU8, getU8?_of_ge hi']
    simp [getU32LE, hnone] at h

/-- Eight-byte reads stay in bounds. -/
theorem getU64LE_ibounds {b : Bytes} {i : Nat} {v : UInt64}
    (h : getU64LE b i = some v) : i + 8 ≤ b.size := by
  by_cases hi : i + 8 ≤ b.size
  · exact hi
  · exfalso
    have hi' : ¬ i + 7 < b.size := by omega
    have hnone : getU8 b (i + 7) = none := by rw [getU8, getU8?_of_ge hi']
    simp [getU64LE, hnone] at h

/-! ### Round-trip lemmas -/

theorem getU8_putU8 (acc : Bytes) (v : UInt8) :
    getU8 (putU8 v acc) acc.size = some v := by
  simp only [getU8, putU8, getU8?_push_eq]

theorem getU16LE_push_push (acc : Bytes) (b0 b1 : UInt8) :
    getU16LE (acc.push b0 |>.push b1) acc.size =
      some (b0.toUInt16 ||| (b1.toUInt16 <<< 8)) := by
  have h0 : acc.size < (acc.push b0 |>.push b1).size := by
    simp only [ByteArray.size_push]; omega
  have h1 : acc.size + 1 < (acc.push b0 |>.push b1).size := by
    simp only [ByteArray.size_push]; omega
  have e0 : (acc.push b0 |>.push b1)[acc.size]'h0 = b0 := by
    rw [getElem_push_lt_byte (v := b1) (i := acc.size) (h := by
      simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq rfl
  have e1 : (acc.push b0 |>.push b1)[acc.size + 1]'h1 = b1 := by
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have lo : getU8? (acc.push b0 |>.push b1) acc.size = some b0 := by
    rw [getU8?_of_lt h0, congrArg some e0]
  have hi : getU8? (acc.push b0 |>.push b1) (acc.size + 1) = some b1 := by
    rw [getU8?_of_lt h1, congrArg some e1]
  simp only [getU16LE, getU8, lo, hi]
  rfl

theorem getU32LE_push4 (acc : Bytes) (b0 b1 b2 b3 : UInt8) :
    getU32LE (acc.push b0 |>.push b1 |>.push b2 |>.push b3) acc.size =
      some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
            (b3.toUInt32 <<< 24)) := by
  have hsz : (acc.push b0 |>.push b1 |>.push b2 |>.push b3).size = acc.size + 4 := by
    simp only [ByteArray.size_push]
  have h0 : acc.size < (acc.push b0 |>.push b1 |>.push b2 |>.push b3).size := by omega
  have h1 : acc.size + 1 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3).size := by omega
  have h2 : acc.size + 2 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3).size := by omega
  have h3 : acc.size + 3 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3).size := by omega
  have e0 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3)[acc.size]'h0 = b0 := by
    rw [getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq rfl
  have e1 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3)[acc.size + 1]'h1 = b1 := by
    rw [getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e2 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3)[acc.size + 2]'h2 = b2 := by
    rw [getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e3 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3)[acc.size + 3]'h3 = b3 := by
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have c0 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3) acc.size = some b0 := by
    rw [getU8?_of_lt h0, congrArg some e0]
  have c1 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3) (acc.size + 1) = some b1 := by
    rw [getU8?_of_lt h1, congrArg some e1]
  have c2 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3) (acc.size + 2) = some b2 := by
    rw [getU8?_of_lt h2, congrArg some e2]
  have c3 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3) (acc.size + 3) = some b3 := by
    rw [getU8?_of_lt h3, congrArg some e3]
  simp only [getU32LE, getU8, c0, c1, c2, c3]
  rfl

theorem getU64LE_push8 (acc : Bytes) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    getU64LE (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
                 |>.push b6 |>.push b7) acc.size =
      some (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
            (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) |||
            (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) |||
            (b7.toUInt64 <<< 56)) := by
  have hsz : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7).size = acc.size + 8 := by
    simp only [ByteArray.size_push]
  have h0 : acc.size < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h1 : acc.size + 1 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h2 : acc.size + 2 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h3 : acc.size + 3 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h4 : acc.size + 4 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h5 : acc.size + 5 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h6 : acc.size + 6 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have h7 : acc.size + 7 < (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4
      |>.push b5 |>.push b6 |>.push b7).size := by omega
  have e0 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size]'h0 = b0 := by
    rw [getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq rfl
  have e1 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 1]'h1 = b1 := by
    rw [getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 1) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e2 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 2]'h2 = b2 := by
    rw [getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 2) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e3 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 3]'h3 = b3 := by
    rw [getElem_push_lt_byte (i := acc.size + 3) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 3) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 3) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 3) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e4 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 4]'h4 = b4 := by
    rw [getElem_push_lt_byte (i := acc.size + 4) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 4) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 4) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e5 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 5]'h5 = b5 := by
    rw [getElem_push_lt_byte (i := acc.size + 5) (h := by simp only [ByteArray.size_push]; omega),
        getElem_push_lt_byte (i := acc.size + 5) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e6 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 6]'h6 = b6 := by
    rw [getElem_push_lt_byte (i := acc.size + 6) (h := by simp only [ByteArray.size_push]; omega)]
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have e7 : (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7)[acc.size + 7]'h7 = b7 := by
    exact getElem_push_of_size_eq (by simp only [ByteArray.size_push])
  have c0 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) acc.size = some b0 := by
    rw [getU8?_of_lt h0, congrArg some e0]
  have c1 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 1) = some b1 := by
    rw [getU8?_of_lt h1, congrArg some e1]
  have c2 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 2) = some b2 := by
    rw [getU8?_of_lt h2, congrArg some e2]
  have c3 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 3) = some b3 := by
    rw [getU8?_of_lt h3, congrArg some e3]
  have c4 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 4) = some b4 := by
    rw [getU8?_of_lt h4, congrArg some e4]
  have c5 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 5) = some b5 := by
    rw [getU8?_of_lt h5, congrArg some e5]
  have c6 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 6) = some b6 := by
    rw [getU8?_of_lt h6, congrArg some e6]
  have c7 : getU8? (acc.push b0 |>.push b1 |>.push b2 |>.push b3 |>.push b4 |>.push b5
      |>.push b6 |>.push b7) (acc.size + 7) = some b7 := by
    rw [getU8?_of_lt h7, congrArg some e7]
  simp only [getU64LE, getU8, c0, c1, c2, c3, c4, c5, c6, c7]
  rfl

theorem getU16LE_putU16LE (acc : Bytes) (v : UInt16) :
    getU16LE (putU16LE v acc) acc.size = some v := by
  show getU16LE (acc.push (v &&& 0xff).toUInt8 |>.push ((v >>> 8) &&& 0xff).toUInt8) acc.size = some v
  rw [getU16LE_push_push]
  congr 1
  bv_decide

theorem getU32LE_putU32LE (acc : Bytes) (v : UInt32) :
    getU32LE (putU32LE v acc) acc.size = some v := by
  show getU32LE (acc.push (v &&& 0xff).toUInt8 |>.push ((v >>> 8) &&& 0xff).toUInt8
                  |>.push ((v >>> 16) &&& 0xff).toUInt8 |>.push ((v >>> 24) &&& 0xff).toUInt8)
                  acc.size = some v
  rw [getU32LE_push4]
  congr 1
  bv_decide

theorem getU64LE_putU64LE (acc : Bytes) (v : UInt64) :
    getU64LE (putU64LE v acc) acc.size = some v := by
  show getU64LE (acc.push (v &&& 0xff).toUInt8 |>.push ((v >>> 8) &&& 0xff).toUInt8
                  |>.push ((v >>> 16) &&& 0xff).toUInt8 |>.push ((v >>> 24) &&& 0xff).toUInt8
                  |>.push ((v >>> 32) &&& 0xff).toUInt8 |>.push ((v >>> 40) &&& 0xff).toUInt8
                  |>.push ((v >>> 48) &&& 0xff).toUInt8 |>.push ((v >>> 56) &&& 0xff).toUInt8)
                  acc.size = some v
  rw [getU64LE_push8]
  congr 1
  bv_decide

theorem getI32LE_putI32LE (acc : Bytes) (v : Int32) :
    getI32LE (putI32LE v acc) acc.size = some v := by
  simp [getI32LE, putI32LE, getU32LE_putU32LE]

theorem getI64LE_putI64LE (acc : Bytes) (v : Int64) :
    getI64LE (putI64LE v acc) acc.size = some v := by
  simp [getI64LE, putI64LE, getU64LE_putU64LE]

theorem getF16Bits_putF16Bits (acc : Bytes) (v : UInt16) :
    getF16Bits (putF16Bits v acc) acc.size = some v := by
  simp [getF16Bits, putF16Bits, getU16LE_putU16LE]

theorem getF32Bits_putF32Bits (acc : Bytes) (v : UInt32) :
    getF32Bits (putF32Bits v acc) acc.size = some v := by
  simp [getF32Bits, putF32Bits, getU32LE_putU32LE]

/-- `getU8?` on an array built by pushes only sees the pushed bytes. -/
theorem getU8?_push (b : Bytes) (v : UInt8) (i : Nat) :
    getU8? (b.push v) i = if i = b.size then some v else getU8? b i := by
  by_cases h : i = b.size
  · subst h
    rw [ite_eq_left rfl]
    exact getU8?_push_eq b v
  · by_cases hlt : i < b.size
    · have h' : i < (b.push v).size := by simp only [ByteArray.size_push]; omega
      simp [h, getU8?_of_lt h', getU8?_of_lt hlt, getElem_push_lt_byte hlt]
    · have hge : ¬ i < (b.push v).size := by simp only [ByteArray.size_push]; omega
      simp [h, getU8?_of_ge hge, getU8?_of_ge hlt]


/-! ### Append / extract lemmas used by the parse-emit round trip -/

/-- A byte read entirely inside the left operand. -/
theorem getU8?_append_left {a b : Bytes} {i : Nat} (h : i < a.size) :
    getU8? (a ++ b) i = getU8? a i := by
  have h' : i < (a ++ b).size := by
    rw [ByteArray.size_append]; omega
  rw [getU8?_of_lt h', getU8?_of_lt h]
  congr 1
  exact ByteArray.getElem_append_left (a := a) (b := b) (i := i) (by omega)

/-- A byte read that falls in the right operand. -/
theorem getU8?_append_right {a b : Bytes} {i : Nat} (h : a.size ≤ i) :
    getU8? (a ++ b) i = getU8? b (i - a.size) := by
  by_cases hlt : i < (a ++ b).size
  · have hb : i - a.size < b.size := by
      rw [ByteArray.size_append] at hlt; omega
    rw [getU8?_of_lt hlt, getU8?_of_lt hb]
    congr 1
    exact ByteArray.getElem_append_right (a := a) (b := b) (i := i) (by omega)
  · have hb : ¬ i - a.size < b.size := by
      rw [ByteArray.size_append] at hlt; omega
    rw [getU8?_of_ge hlt, getU8?_of_ge hb]

/-- A 32-bit read starting exactly at the right operand of an append. -/
theorem getU32LE_append_right {a b : Bytes} :
    getU32LE (a ++ b) a.size = getU32LE b 0 := by
  have e0 : getU8? (a ++ b) a.size = getU8? b 0 := by
    rw [getU8?_append_right (a := a) (b := b) (i := a.size) (by omega)]
    congr 1
    omega
  have e1 : getU8? (a ++ b) (a.size + 1) = getU8? b 1 := by
    rw [getU8?_append_right (a := a) (b := b) (i := a.size + 1) (by omega)]
    congr 1
    omega
  have e2 : getU8? (a ++ b) (a.size + 2) = getU8? b 2 := by
    rw [getU8?_append_right (a := a) (b := b) (i := a.size + 2) (by omega)]
    congr 1
    omega
  have e3 : getU8? (a ++ b) (a.size + 3) = getU8? b 3 := by
    rw [getU8?_append_right (a := a) (b := b) (i := a.size + 3) (by omega)]
    congr 1
    omega
  unfold getU32LE
  simp only [getU8]
  rw [e0, e1, e2, e3]

/-- A 32-bit read of a 4-byte LE field followed by other bytes. -/
theorem getU32LE_u32Bytes_append (x : UInt32) (v : Bytes) :
    getU32LE (putU32LE x ByteArray.empty ++ v) 0 = some x := by
  have e : ∀ k, k < 4 →
      getU8? (putU32LE x ByteArray.empty ++ v) k
        = getU8? (putU32LE x ByteArray.empty) k := by
    intro k hk
    rw [getU8?_append_left (a := putU32LE x ByteArray.empty) (b := v) (i := k) (by
      simp only [putU32LE, ByteArray.size_push]; omega)]
  unfold getU32LE
  simp only [getU8, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  exact getU32LE_putU32LE (acc := ByteArray.empty) x

/-- Extracting `0 .. i+1` is the prefix up to `i` plus byte `i`. -/
theorem extract_zero_succ {a : Bytes} {i : Nat} (hi : i + 1 ≤ a.size) :
    a.extract 0 (i + 1) = (a.extract 0 i).push (a[i]'(by omega)) := by
  rw [ByteArray.extract_eq_extract_append_extract (i := 0) (j := i) (k := i + 1) (by omega) (by omega)]
  rw [ByteArray.extract_add_one (by omega)]
  rw [ByteArray.append_toByteArray_singleton]

/-- Extracting a suffix that starts at `a.size` gives the right operand. -/
theorem extract_append_right_eq {a b : Bytes} :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  exact ByteArray.extract_append_eq_right (i := a.size) (j := a.size + b.size)
    (by omega) (by omega)

end Exr