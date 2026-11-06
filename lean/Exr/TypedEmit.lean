/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Typed attribute *encoders* and their round-trip theorems: for every
  entry of the schema table exercised by the model (`fixedSize`), the
  emitted value bytes decode back to the original value.

  * 4-byte words are emitted little-endian via `u32Words`/`getU32LE_u32Words`
    (and `u64Words`/`getU64LE_u64Words` for 8-byte words);
  * `box2i … tiledesc` — the fixed-size table entries that have decoders;
    `uint`/`v2d`/`v3d`/`keycode`/`rational`/`envmap` have a size entry but
    no decoder in the model, so there is nothing to invert;
  * `channels` — the variable-length `chlist`, decoded by
    `decodeChlistFuel` (round trip preserves the channel list exactly);
  * `string`/`text` — identity decoders (value bytes are kept verbatim).

  `m33f`/`m44f` accumulate their words back-to-front, so the round trip is
  stated against `List.reverse` (see the comments on the theorems). The
  `chlist` round trip additionally requires each channel name to be non-empty
  and NUL-free, and the samplings to be positive (as the decoder does).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Attribute

namespace Exr

set_option linter.unusedVariables false

/-! ## Word emitters and readers -/

/-- Emit `ws` as consecutive u32 little-endian words. -/
def u32Words (ws : List UInt32) : Bytes :=
  ws.foldr (fun w acc => putU32LE w ByteArray.empty ++ acc) ByteArray.empty

/-- Emit `ws` as consecutive u64 little-endian words. -/
def u64Words (ws : List UInt64) : Bytes :=
  ws.foldr (fun w acc => putU64LE w ByteArray.empty ++ acc) ByteArray.empty

theorem u32Words_nil : u32Words [] = ByteArray.empty := rfl

theorem u32Words_cons (w : UInt32) (ws : List UInt32) :
    u32Words (w :: ws) = putU32LE w ByteArray.empty ++ u32Words ws := rfl

theorem u64Words_nil : u64Words [] = ByteArray.empty := rfl

theorem u64Words_cons (w : UInt64) (ws : List UInt64) :
    u64Words (w :: ws) = putU64LE w ByteArray.empty ++ u64Words ws := rfl

theorem u32Words_size (ws : List UInt32) : (u32Words ws).size = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [u32Words_cons, ByteArray.size_append, List.length_cons]
    have hsz : (putU32LE w ByteArray.empty).size = 4 := by
      simp [putU32LE]
    omega

theorem u64Words_size (ws : List UInt64) : (u64Words ws).size = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [u64Words_cons, ByteArray.size_append, List.length_cons]
    have hsz : (putU64LE w ByteArray.empty).size = 8 := by
      simp [putU64LE]
    omega

/-- Read word `k` of a u32 word stream. -/
theorem getU32LE_u32Words (ws : List UInt32) (k : Nat) (hk : k < ws.length) :
    getU32LE (u32Words ws) (4 * k) = some ws[k] := by
  induction ws generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero =>
      rw [u32Words_cons, getU32LE_u32Bytes_append]
      rfl
    | succ k =>
      rw [u32Words_cons]
      have hsz : (putU32LE w ByteArray.empty).size = 4 := by
        simp [putU32LE]
      have h : 4 * (k + 1) = (putU32LE w ByteArray.empty).size + 4 * k := by
        rw [hsz]
        omega
      rw [h, getU32LE_append_right' (a := putU32LE w ByteArray.empty) (b := u32Words ws)]
      rw [ih k (by simp only [List.length_cons] at hk; omega)]
      rfl

/-- Read word `k` of a u64 word stream. -/
theorem getU64LE_u64Words (ws : List UInt64) (k : Nat) (hk : k < ws.length) :
    getU64LE (u64Words ws) (8 * k) = some ws[k] := by
  induction ws generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero =>
      have h0 : (putU64LE w ByteArray.empty).size = 8 := by
        simp [putU64LE]
      have e : ∀ j < 8, getU8? (u64Words (w :: ws)) j
          = getU8? (putU64LE w ByteArray.empty) j := by
        intro j hj
        rw [u64Words_cons]
        rw [getU8?_append_left (a := putU64LE w ByteArray.empty) (b := u64Words ws) (i := j)
              (by omega)]
      unfold getU64LE
      simp only [getU8]
      rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
          e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]
      exact getU64LE_putU64LE (acc := ByteArray.empty) w
    | succ k =>
      rw [u64Words_cons]
      have hsz : (putU64LE w ByteArray.empty).size = 8 := by
        simp [putU64LE]
      have h : 8 * (k + 1) = (putU64LE w ByteArray.empty).size + 8 * k := by
        rw [hsz]
        omega
      rw [h, getU64LE_append_right' (a := putU64LE w ByteArray.empty) (b := u64Words ws)]
      rw [ih k (by simp only [List.length_cons] at hk; omega)]
      rfl

/-- Read word `k` of a u32 stream as an `i32`. -/
theorem getI32LE_u32Words (ws : List UInt32) (k : Nat) (hk : k < ws.length) :
    getI32LE (u32Words ws) (4 * k) = some (ws[k]).toInt32 := by
  unfold getI32LE
  rw [getU32LE_u32Words ws k hk]
  rfl

/-! ## Box2i / Box2f -/

def encBox2i (b : Box2i) : Bytes :=
  u32Words [b.minX.toUInt32, b.minY.toUInt32, b.maxX.toUInt32, b.maxY.toUInt32]

def encBox2f (x : UInt32 × UInt32 × UInt32 × UInt32) : Bytes :=
  u32Words [x.1, x.2.1, x.2.2.1, x.2.2.2]

theorem TypedAttr.decodeBox2i_encode (b : Box2i) : TypedAttr.decodeBox2i (encBox2i b) = some b := by
  unfold TypedAttr.decodeBox2i encBox2i
  rw [u32Words_size]
  simp only [List.length_cons, List.length_nil]
  rw [getI32LE_u32Words _ 0 (by simp), getI32LE_u32Words _ 1 (by simp),
      getI32LE_u32Words _ 2 (by simp), getI32LE_u32Words _ 3 (by simp)]
  simp

theorem TypedAttr.decodeBox2f_encode (x : UInt32 × UInt32 × UInt32 × UInt32) :
    TypedAttr.decodeBox2f (encBox2f x) = some x := by
  obtain ⟨a, b, c, d⟩ := x
  show TypedAttr.decodeBox2f (u32Words [a, b, c, d]) = some (a, b, c, d)
  unfold TypedAttr.decodeBox2f
  rw [u32Words_size]
  simp only [List.length_cons, List.length_nil]
  rw [getU32LE_u32Words _ 0 (by simp), getU32LE_u32Words _ 1 (by simp),
      getU32LE_u32Words _ 2 (by simp), getU32LE_u32Words _ 3 (by simp)]
  rfl

/-! ## Compression / lineOrder -/

def encCompression (c : Compression) : Bytes := ByteArray.push ByteArray.empty (Compression.toBits c)

def encLineOrder (l : LineOrder) : Bytes := ByteArray.push ByteArray.empty (LineOrder.toBits l)

theorem TypedAttr.decodeCompression_encode (c : Compression) :
    TypedAttr.decodeCompression (encCompression c) = some c := by
  unfold TypedAttr.decodeCompression encCompression
  rw [ByteArray.size_push]
  show (getU8? (ByteArray.push ByteArray.empty (Compression.toBits c)) 0).bind Compression.ofBits = some c
  rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU8?_push_eq, Option.bind_some,
    Compression.ofBits_toBits]

theorem TypedAttr.decodeLineOrder_encode (l : LineOrder) :
    TypedAttr.decodeLineOrder (encLineOrder l) = some l := by
  unfold TypedAttr.decodeLineOrder encLineOrder
  rw [ByteArray.size_push]
  show (getU8? (ByteArray.push ByteArray.empty (LineOrder.toBits l)) 0).bind LineOrder.ofBits = some l
  rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU8?_push_eq, Option.bind_some,
    LineOrder.ofBits_toBits]

/-! ## float / double / int / v2f / v3f -/

def encFloatBits (b : UInt32) : Bytes := u32Words [b]

def encDoubleBits (b : UInt64) : Bytes := u64Words [b]

def encInt (v : Int32) : Bytes := u32Words [v.toUInt32]

def encV2f (x : UInt32 × UInt32) : Bytes := u32Words [x.1, x.2]

def encV3f (x : UInt32 × UInt32 × UInt32) : Bytes := u32Words [x.1, x.2.1, x.2.2]

theorem TypedAttr.decodeFloatBits_encode (b : UInt32) : TypedAttr.decodeFloatBits (encFloatBits b) = some b := by
  unfold TypedAttr.decodeFloatBits encFloatBits
  rw [u32Words_size]
  simp
  rw [getU32LE_u32Words _ 0 (by simp)]
  simp

theorem TypedAttr.decodeDoubleBits_encode (b : UInt64) : TypedAttr.decodeDoubleBits (encDoubleBits b) = some b := by
  unfold TypedAttr.decodeDoubleBits encDoubleBits
  rw [u64Words_size]
  simp
  rw [getU64LE_u64Words _ 0 (by simp)]
  simp

theorem TypedAttr.decodeInt_encode (v : Int32) : TypedAttr.decodeInt (encInt v) = some v := by
  unfold TypedAttr.decodeInt encInt
  rw [u32Words_size]
  simp only [List.length_cons, List.length_nil]
  rw [getI32LE_u32Words _ 0 (by simp)]
  simp

theorem TypedAttr.decodeV2f_encode (x : UInt32 × UInt32) : TypedAttr.decodeV2f (encV2f x) = some x := by
  obtain ⟨a, b⟩ := x
  show TypedAttr.decodeV2f (u32Words [a, b]) = some (a, b)
  unfold TypedAttr.decodeV2f
  rw [u32Words_size]
  simp
  rw [getU32LE_u32Words _ 0 (by simp), getU32LE_u32Words _ 1 (by simp)]
  rfl

theorem TypedAttr.decodeV3f_encode (x : UInt32 × UInt32 × UInt32) : TypedAttr.decodeV3f (encV3f x) = some x := by
  obtain ⟨a, b, c⟩ := x
  show TypedAttr.decodeV3f (u32Words [a, b, c]) = some (a, b, c)
  unfold TypedAttr.decodeV3f
  rw [u32Words_size]
  simp
  rw [getU32LE_u32Words _ 0 (by simp), getU32LE_u32Words _ 1 (by simp),
      getU32LE_u32Words _ 2 (by simp)]
  rfl


/-! ## m33f / m44f (words accumulate back-to-front) -/

private theorem decodeM44f_go_zero (v : Bytes) :
    Exr.TypedAttr.decodeM44f.go v 0 = some [] := by
  simp only [Exr.TypedAttr.decodeM44f.go]

private theorem decodeM44f_go_succ (v : Bytes) (i : Nat) :
    Exr.TypedAttr.decodeM44f.go v (i + 1) =
      (getU32LE v (4 * i)).bind fun w =>
        (Exr.TypedAttr.decodeM44f.go v i).map (fun rest => w :: rest) := by
  simp only [Exr.TypedAttr.decodeM44f.go]

private theorem decodeM33f_go_zero (v : Bytes) :
    Exr.TypedAttr.decodeM33f.go v 0 = some [] := by
  simp only [Exr.TypedAttr.decodeM33f.go]

private theorem decodeM33f_go_succ (v : Bytes) (i : Nat) :
    Exr.TypedAttr.decodeM33f.go v (i + 1) =
      (getU32LE v (4 * i)).bind fun w =>
        (Exr.TypedAttr.decodeM33f.go v i).map (fun rest => w :: rest) := by
  simp only [Exr.TypedAttr.decodeM33f.go]

/-- The backwards accumulator reverses the word list. -/
private theorem decodeM44f_go_reverse (v : Bytes) (ws : List UInt32)
    (h : ∀ (i : Nat), i < ws.length → getU32LE v (4 * i) = some (ws.getD i 0)) (k : Nat)
    (hk : k ≤ ws.length) :
    Exr.TypedAttr.decodeM44f.go v k = some (ws.take k).reverse := by
  induction k with
  | zero =>
    rw [decodeM44f_go_zero]
    rfl
  | succ k ih =>
    rw [decodeM44f_go_succ, h k (by omega), List.getD_eq_getElem ws 0 (by omega)]
    rw [ih (by omega)]
    simp only [Option.bind_some, Option.map_some]
    rw [List.take_add_one, List.reverse_append]
    rw [List.getElem?_eq_getElem (by omega : k < ws.length), Option.toList_some]
    rw [List.reverse_singleton, List.singleton_append]

/-- The backwards accumulator reverses the word list. -/
private theorem decodeM33f_go_reverse (v : Bytes) (ws : List UInt32)
    (h : ∀ (i : Nat), i < ws.length → getU32LE v (4 * i) = some (ws.getD i 0)) (k : Nat)
    (hk : k ≤ ws.length) :
    Exr.TypedAttr.decodeM33f.go v k = some (ws.take k).reverse := by
  induction k with
  | zero =>
    rw [decodeM33f_go_zero]
    rfl
  | succ k ih =>
    rw [decodeM33f_go_succ, h k (by omega), List.getD_eq_getElem ws 0 (by omega)]
    rw [ih (by omega)]
    simp only [Option.bind_some, Option.map_some]
    rw [List.take_add_one, List.reverse_append]
    rw [List.getElem?_eq_getElem (by omega : k < ws.length), Option.toList_some]
    rw [List.reverse_singleton, List.singleton_append]

/-- The decoder returns the words back-to-front, so the emitted list must be
    reversed to round-trip. -/
theorem TypedAttr.decodeM44f_encode (xs : List UInt32) (hx : xs.length = 16) :
    TypedAttr.decodeM44f (u32Words xs) = some xs.reverse := by
  have hget : ∀ (i : Nat), i < xs.length → getU32LE (u32Words xs) (4 * i) = some (xs.getD i 0) := by
    intro i hi
    rw [getU32LE_u32Words xs i hi, List.getD_eq_getElem xs 0 hi]
  unfold TypedAttr.decodeM44f
  rw [u32Words_size, hx]
  show Exr.TypedAttr.decodeM44f.go (u32Words xs) 16 = some xs.reverse
  rw [decodeM44f_go_reverse _ _ hget 16 (by omega), List.take_of_length_le (by omega)]

/-- The decoder returns the words back-to-front, so the emitted list must be
    reversed to round-trip. -/
theorem TypedAttr.decodeM33f_encode (xs : List UInt32) (hx : xs.length = 9) :
    TypedAttr.decodeM33f (u32Words xs) = some xs.reverse := by
  have hget : ∀ (i : Nat), i < xs.length → getU32LE (u32Words xs) (4 * i) = some (xs.getD i 0) := by
    intro i hi
    rw [getU32LE_u32Words xs i hi, List.getD_eq_getElem xs 0 hi]
  unfold TypedAttr.decodeM33f
  rw [u32Words_size, hx]
  show Exr.TypedAttr.decodeM33f.go (u32Words xs) 9 = some xs.reverse
  rw [decodeM33f_go_reverse _ _ hget 9 (by omega), List.take_of_length_le (by omega)]

/-! ## chromaticities -/

theorem TypedAttr.decodeChromaticities_encode (a b c d e f g h : UInt32)
    (hfin : TypedAttr.allFiniteF32 [a, b, c, d, e, f, g, h] = true) :
    TypedAttr.decodeChromaticities (u32Words [a, b, c, d, e, f, g, h]) = some [a, b, c, d, e, f, g, h] := by
  unfold TypedAttr.decodeChromaticities
  rw [u32Words_size]
  show (match getU32LE (u32Words [a, b, c, d, e, f, g, h]) 0,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 4,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 8,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 12,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 16,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 20,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 24,
              getU32LE (u32Words [a, b, c, d, e, f, g, h]) 28 with
        | some a, some b, some c, some d, some e, some f, some g, some h =>
          if TypedAttr.allFiniteF32 [a, b, c, d, e, f, g, h] then some [a, b, c, d, e, f, g, h] else none
        | _, _, _, _, _, _, _, _ => none) = some [a, b, c, d, e, f, g, h]
  rw [getU32LE_u32Words _ 0 (by simp), getU32LE_u32Words _ 1 (by simp),
      getU32LE_u32Words _ 2 (by simp), getU32LE_u32Words _ 3 (by simp),
      getU32LE_u32Words _ 4 (by simp), getU32LE_u32Words _ 5 (by simp),
      getU32LE_u32Words _ 6 (by simp), getU32LE_u32Words _ 7 (by simp)]
  simp [hfin]

/-! ## tiledesc -/

/-- Encode a level mode into the `tiledesc` low nibble. -/
def encLevelMode : TypedAttr.LevelMode → Nat
  | .oneLevel => 0
  | .mipmap => 1
  | .ripmap => 2

/-- Encode a rounding mode into the `tiledesc` high nibble. -/
def encRoundingMode : TypedAttr.RoundingMode → Nat
  | .roundDown => 0
  | .roundUp => 1

def encTileDesc (t : TypedAttr.TileDesc) : Bytes :=
  u32Words [t.xSize.toUInt32, t.ySize.toUInt32] ++
    (ByteArray.empty).push ((encRoundingMode t.roundingMode * 16 +
      encLevelMode t.levelMode).toUInt8)

theorem TypedAttr.decodeTileDesc_encode (t : TypedAttr.TileDesc) (hx : t.xSize < 2 ^ 32) (hy : t.ySize < 2 ^ 32) :
    TypedAttr.decodeTileDesc (encTileDesc t) = some t := by
  unfold TypedAttr.decodeTileDesc encTileDesc
  have hsz : (u32Words [t.xSize.toUInt32, t.ySize.toUInt32] ++
        (ByteArray.empty).push ((encRoundingMode t.roundingMode * 16 +
          encLevelMode t.levelMode).toUInt8)).size = 9 := by
    rw [ByteArray.size_append, u32Words_size]
    simp [ByteArray.size_push, List.length_cons, List.length_nil]
  rw [hsz]
  rw [getU32LE_append_left (a := u32Words [t.xSize.toUInt32, t.ySize.toUInt32])
        (b := ByteArray.empty.push ((encRoundingMode t.roundingMode * 16 +
          encLevelMode t.levelMode).toUInt8)) (i := 0) (by rw [u32Words_size]; simp)]
  rw [getU32LE_append_left (a := u32Words [t.xSize.toUInt32, t.ySize.toUInt32])
        (b := ByteArray.empty.push ((encRoundingMode t.roundingMode * 16 +
          encLevelMode t.levelMode).toUInt8)) (i := 4) (by rw [u32Words_size]; simp)]
  rw [getU32LE_u32Words _ 0 (by simp), getU32LE_u32Words _ 1 (by simp)]
  have h8 : getU8? (u32Words [t.xSize.toUInt32, t.ySize.toUInt32] ++
        ByteArray.empty.push ((encRoundingMode t.roundingMode * 16 +
          encLevelMode t.levelMode).toUInt8)) 8
      = some ((encRoundingMode t.roundingMode * 16 + encLevelMode t.levelMode).toUInt8) := by
    rw [getU8?_append_right (a := u32Words [t.xSize.toUInt32, t.ySize.toUInt32])
          (b := ByteArray.empty.push ((encRoundingMode t.roundingMode * 16 +
            encLevelMode t.levelMode).toUInt8)) (i := 8) (by rw [u32Words_size]; simp)]
    rw [show 8 - (u32Words [t.xSize.toUInt32, t.ySize.toUInt32]).size = 0 by
          rw [u32Words_size]; simp]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU8?_push_eq]
  rw [h8]
  rcases t with ⟨x, y, lm, rm⟩
  have hx' : x < 2 ^ 32 := by simp at hx; exact hx
  have hy' : y < 2 ^ 32 := by simp at hy; exact hy
  rcases lm with _ | _ | _ <;> rcases rm with _ | _
  all_goals simp [encLevelMode, encRoundingMode,
                  Nat.mod_eq_of_lt (show x < 4294967296 by omega),
                  Nat.mod_eq_of_lt (show y < 4294967296 by omega)]

/-! ## string / text (identity decoders) -/

theorem TypedAttr.decodeString_encode (b : Bytes) : TypedAttr.decodeString b = some b := rfl

theorem TypedAttr.decodeText_encode (b : Bytes) : TypedAttr.decodeText b = some b := rfl

end Exr
