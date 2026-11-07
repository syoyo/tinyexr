/-
  TinyEXR - Lean 4 formalization of PIZ range reduction and wavelet lifting.

  Models the OpenEXR-derived kernels in src/exr_piz.c. Companion PizTraversal,
  PizHeap, PizBits/Table, PizCodebook/Entropy and PizPacket modules compose the
  image traversal, frequency construction and Huffman packet layers.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.Attribute

namespace Exr.Piz

/-- Signed 16-bit sample widened before the 14-bit lifting arithmetic. -/
def signed (a : UInt16) : Int32 := a.toInt16.toInt32

def wenc14 (a b : UInt16) : UInt16 × UInt16 :=
  (((signed a + signed b) >>> 1).toUInt32.toUInt16, (signed a - signed b).toUInt32.toUInt16)

def wdec14 (l h : UInt16) : UInt16 × UInt16 :=
  let hi := signed h
  let a := signed l + (hi &&& (1 : Int32)) + (hi >>> 1)
  (a.toUInt32.toUInt16, (a - hi).toUInt32.toUInt16)

/-- The small-range branch is selected only below 2^14. -/
theorem wdec14_wenc14 (a b : UInt16) (ha : a < 16384) (hb : b < 16384) :
    wdec14 (wenc14 a b).1 (wenc14 a b).2 = (a, b) := by
  apply Prod.ext <;> dsimp only [wdec14, wenc14, signed] <;> bv_decide

/-- Full-range modular lifting, including the offset and negative-difference
correction used by the C encoder. All intermediate sums fit UInt32. -/
def wenc16 (a b : UInt16) : UInt16 × UInt16 :=
  let ao := (a.toUInt32 + 32768) &&& 65535
  let bb := b.toUInt32
  let m := (ao + bb) >>> 1
  let d := ao - bb
  ((if ao < bb then (m + 32768) &&& 65535 else m).toUInt16, d.toUInt16)

def wdec16 (l h : UInt16) : UInt16 × UInt16 :=
  let b := (l.toUInt32 - (h.toUInt32 >>> 1)) &&& 65535
  let a := (h.toUInt32 + b - 32768) &&& 65535
  (a.toUInt16, b.toUInt16)

theorem wdec16_wenc16 (a b : UInt16) :
    wdec16 (wenc16 a b).1 (wenc16 a b).2 = (a, b) := by
  apply Prod.ext <;> dsimp only [wdec16, wenc16] <;> bv_decide

/-- One separable 2×2 lifting cell, in row-major order. -/
def encodeCell (enc : UInt16 → UInt16 → UInt16 × UInt16)
    (x : (UInt16 × UInt16) × (UInt16 × UInt16)) :=
  let top := enc x.1.1 x.1.2
  let bot := enc x.2.1 x.2.2
  let left := enc top.1 bot.1
  let right := enc top.2 bot.2
  ((left.1, right.1), (left.2, right.2))

def decodeCell (dec : UInt16 → UInt16 → UInt16 × UInt16)
    (x : (UInt16 × UInt16) × (UInt16 × UInt16)) :=
  let left := dec x.1.1 x.2.1
  let right := dec x.1.2 x.2.2
  let top := dec left.1 right.1
  let bot := dec left.2 right.2
  ((top.1, top.2), (bot.1, bot.2))

theorem decodeCell_encodeCell (enc dec : UInt16 → UInt16 → UInt16 × UInt16)
    (hinv : ∀ a b, dec (enc a b).1 (enc a b).2 = (a, b))
    (x : (UInt16 × UInt16) × (UInt16 × UInt16)) :
    decodeCell dec (encodeCell enc x) = x := by
  simp only [decodeCell, encodeCell, hinv]

theorem decodeCell16_encodeCell16 (x : (UInt16 × UInt16) × (UInt16 × UInt16)) :
    decodeCell wdec16 (encodeCell wenc16 x) = x :=
  decodeCell_encodeCell wenc16 wdec16 wdec16_wenc16 x

theorem decodeCell14_encodeCell14 (a b c d : UInt16)
    (ha : a < 16384) (hb : b < 16384) (hc : c < 16384) (hd : d < 16384) :
    decodeCell wdec14 (encodeCell wenc14 ((a, b), (c, d))) = ((a, b), (c, d)) := by
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp only [decodeCell, encodeCell, wdec14, wenc14, signed] <;> bv_decide

/-- A lifting pass updates two distinct positions and preserves all others.
The function representation keeps image bounds separate from algebra. -/
def applyPair (enc : UInt16 → UInt16 → UInt16 × UInt16) (i j : Nat)
    (values : Nat → UInt16) : Nat → UInt16 :=
  fun k => if k = i then (enc (values i) (values j)).1
    else if k = j then (enc (values i) (values j)).2 else values k

theorem applyPair_inverse (enc dec : UInt16 → UInt16 → UInt16 × UInt16)
    (hi : ∀ a b, dec (enc a b).1 (enc a b).2 = (a, b))
    (i j : Nat) (hij : i ≠ j) (values : Nat → UInt16) :
    applyPair dec i j (applyPair enc i j values) = values := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [applyPair, Ne.symm hij, hi]
  · by_cases hkj : k = j
    · subst k
      simp [applyPair, Ne.symm hij, hi]
    · simp [applyPair, hki, hkj]

def encodeSchedule (enc : UInt16 → UInt16 → UInt16 × UInt16) :
    List (Nat × Nat) → (Nat → UInt16) → (Nat → UInt16)
  | [], values => values
  | (i, j) :: rest, values => encodeSchedule enc rest (applyPair enc i j values)

def decodeSchedule (dec : UInt16 → UInt16 → UInt16 × UInt16) :
    List (Nat × Nat) → (Nat → UInt16) → (Nat → UInt16)
  | [], values => values
  | (i, j) :: rest, values => applyPair dec i j (decodeSchedule dec rest values)

/-- Composition over any multilevel schedule of distinct-position pairs.
This proves lifting algebra; deriving the image traversal schedule and its
memory bounds remains a separate obligation. -/
theorem decodeSchedule_encodeSchedule (enc dec : UInt16 → UInt16 → UInt16 × UInt16)
    (hi : ∀ a b, dec (enc a b).1 (enc a b).2 = (a, b))
    (schedule : List (Nat × Nat)) (hs : ∀ p ∈ schedule, p.1 ≠ p.2)
    (values : Nat → UInt16) :
    decodeSchedule dec schedule (encodeSchedule enc schedule values) = values := by
  induction schedule generalizing values with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨i, j⟩
    simp only [encodeSchedule, decodeSchedule]
    rw [ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))]
    exact applyPair_inverse enc dec hi i j (hs _ List.mem_cons_self) values

theorem decodeSchedule16_encodeSchedule16 (schedule : List (Nat × Nat))
    (hs : ∀ p ∈ schedule, p.1 ≠ p.2) (values : Nat → UInt16) :
    decodeSchedule wdec16 schedule (encodeSchedule wenc16 schedule values) = values :=
  decodeSchedule_encodeSchedule wenc16 wdec16 wdec16_wenc16 schedule hs values

/-- The inverse range LUT consists of zero followed by all nonzero values
whose bitmap bit is set, in increasing order. Padding entries decode to zero. -/
def alphabet (bitmap : List UInt8) : List Nat :=
  0 :: ((List.range 65535).map (· + 1)).filter (fun v =>
    ((bitmap.getD (v / 8) 0 >>> UInt8.ofNat (v % 8)) &&& 1) == 1)

def forward (values : List Nat) (v : Nat) : Nat := if v ∈ values then values.idxOf v else 0

def reverse (values : List Nat) (rank : Nat) : Nat := values.getD rank 0

theorem reverse_forward (values : List Nat) (v : Nat) (hv : v ∈ values) :
    reverse values (forward values v) = v := by
  simp only [reverse, forward, ite_eq_left hv, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hv)]
  simp only [List.getElem_idxOf, Option.getD_some]

theorem alphabet_zero (bitmap : List UInt8) : 0 ∈ alphabet bitmap := by
  simp [alphabet]

theorem range_roundtrip (bitmap : List UInt8) (v : Nat) (hv : v ∈ alphabet bitmap) :
    reverse (alphabet bitmap) (forward (alphabet bitmap) v) = v :=
  reverse_forward _ _ hv

theorem alphabet_length_le (bitmap : List UInt8) : (alphabet bitmap).length ≤ 65536 := by
  have h := List.length_filter_le (fun (v : Nat) =>
    ((bitmap.getD (v / 8) 0 >>> UInt8.ofNat (v % 8)) &&& 1) == 1)
    ((List.range 65535).map (· + 1))
  simp only [List.length_map, List.length_range] at h
  simp only [alphabet, List.length_cons]
  omega

theorem forward_lt (bitmap : List UInt8) (v : Nat) :
    forward (alphabet bitmap) v < 65536 := by
  by_cases hv : v ∈ alphabet bitmap
  · have hi := List.idxOf_lt_length_iff.mpr hv
    have hl := alphabet_length_le bitmap
    simp only [forward, ite_eq_left hv]
    omega
  · simp [forward, hv]

/-- Counts of code lengths, including absent symbols (length zero). -/
def lengthCount (lengths : List Nat) (depth : Nat) : Nat :=
  (lengths.filter (· == depth)).length

/-- The OpenEXR canonical recurrence runs from depth 58 down to 1, rather
than the more usual ascending canonical-code assignment. -/
def codeStart (lengths : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (codeStart lengths k + lengthCount lengths (58 - k)) / 2

/-- Packed code-table word, low six bits length, upper bits code. Symbol
order breaks ties between equal lengths. Zero-length entries remain zero. -/
def canonicalWord (lengths : List Nat) (i : Nat) : Nat :=
  let depth := lengths.getD i 0
  if depth = 0 then 0 else
    (codeStart lengths (58 - depth) + lengthCount (lengths.take i) depth) * 64 + depth

def canonicalTable (lengths : List Nat) : List Nat :=
  (List.range lengths.length).map (canonicalWord lengths)

/-- Skip canonical-word computation for absent symbols. Reading the depth
from the enumeration avoids a linear list lookup for every absent entry. -/
def sparseTable (lengths : List Nat) : List Nat :=
  lengths.zipIdx.map (fun p => if p.1 = 0 then 0 else canonicalWord lengths p.2)

/-- Kernel-checked compilation optimization; the logical canonical-table
constructor remains the reference definition used throughout the proofs. -/
@[csimp] theorem canonicalTable_sparse : canonicalTable = sparseTable := by
  funext lengths
  apply List.ext_getElem?
  intro i
  by_cases hi : i < lengths.length
  · have hget := List.getElem?_eq_getElem hi
    simp only [canonicalTable, sparseTable, List.getElem?_map,
      List.getElem?_zipIdx, List.getElem?_range hi, hget, Option.map_some]
    by_cases hz : lengths[i] = 0
    · simp [canonicalWord, List.getD_eq_getElem?_getD, hget, hz]
    · simp [hz]
  · have hn : lengths.length ≤ i := by omega
    simp [canonicalTable, sparseTable, hn]

theorem canonicalWord_length (lengths : List Nat) (i : Nat)
    (h : lengths.getD i 0 < 64) :
    canonicalWord lengths i % 64 = lengths.getD i 0 := by
  dsimp only [canonicalWord]
  split
  · rename_i hz
    exact hz.symm
  · omega

/-! ## Huffman symbol-stream inversion

A prefix tree makes the required codebook condition explicit. Canonical
assignment is executable above; the theorem below applies to any assigned
codes that follow paths to leaves of the same tree. -/
namespace Huffman

inductive Tree where
  | leaf (symbol : Nat)
  | branch (left right : Tree)
  deriving Repr

inductive Path : Tree → Nat → List Bool → Prop where
  | leaf (symbol : Nat) : Path (.leaf symbol) symbol []
  | left {l r symbol bits} : Path l symbol bits → Path (.branch l r) symbol (false :: bits)
  | right {l r symbol bits} : Path r symbol bits → Path (.branch l r) symbol (true :: bits)

def decodeOne : Tree → List Bool → Option (Nat × List Bool)
  | .leaf symbol, bits => some (symbol, bits)
  | .branch l _, false :: bits => decodeOne l bits
  | .branch _ r, true :: bits => decodeOne r bits
  | .branch _ _, [] => none

theorem decodeOne_path {tree : Tree} {symbol : Nat} {bits : List Bool}
    (h : Path tree symbol bits) (suffix : List Bool) :
    decodeOne tree (bits ++ suffix) = some (symbol, suffix) := by
  induction h with
  | leaf symbol => rfl
  | left _ ih => exact ih
  | right _ ih => exact ih

/-- The requested output count bounds decoding, including a singleton tree. -/
def decodeN (tree : Tree) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
    let (symbol, rest) ← decodeOne tree bits
    let (symbols, tail) ← decodeN tree n rest
    pure (symbol :: symbols, tail)

theorem decodeN_paths (tree : Tree) (symbols : List Nat) (paths : List (List Bool))
    (h : List.Forall₂ (fun symbol bits => Path tree symbol bits) symbols paths)
    (suffix : List Bool) :
    decodeN tree symbols.length (paths.flatten ++ suffix) = some (symbols, suffix) := by
  induction h with
  | nil => rfl
  | @cons symbol bits symbols paths hp _ ih =>
    simp only [List.length_cons, List.flatten_cons, List.append_assoc, decodeN,
      decodeOne_path hp]
    change (do
      let result ← decodeN tree symbols.length (paths.flatten ++ suffix)
      pure (symbol :: result.1, result.2)) = some (symbol :: symbols, suffix)
    rw [ih]
    rfl

/-- MSB-first bit order, shared by table lengths, symbols, and RLE counts. -/
def codeBits (depth value : Nat) : List Bool :=
  (List.range depth).map (fun i => (value / 2 ^ (depth - i - 1)) % 2 == 1)

def packBitsGo : Nat → List Bool → List UInt8
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bits =>
    UInt8.ofNat ((bits.take 8).foldl (fun acc b => acc * 2 + if b then 1 else 0) 0
      * 2 ^ (8 - (bits.take 8).length)) :: packBitsGo fuel (bits.drop 8)

def packBits (bits : List Bool) : List UInt8 := packBitsGo bits.length bits

/-- Wire bits for a zero-length-table run. The caller bounds runs at 261,
matching the eight-bit long-run extension and its base of six. -/
def zeroRunBits (count : Nat) : List Bool :=
  if count ≥ 6 then codeBits 6 63 ++ codeBits 8 (count - 6)
  else if count ≥ 2 then codeBits 6 (59 + count - 2)
  else codeBits 6 0

/-- Length-table RLE, with explicit decreasing fuel for hostile input. -/
def tableBitsGo : Nat → List Nat → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, depth :: rest =>
    if depth = 0 then
      let extra := min 260 (rest.takeWhile (· == 0)).length
      zeroRunBits (extra + 1) ++ tableBitsGo fuel (rest.drop extra)
    else codeBits 6 depth ++ tableBitsGo fuel rest

def tableBytes (lengths : List Nat) : List UInt8 :=
  packBits (tableBitsGo lengths.length lengths)

/-- One symbol run, including the PIZ run marker when shorter than literals.
`extra` is the number of repeats after the first value, at most 255. -/
def runBits (symbolCode runCode : Nat) (extra : Nat) : List Bool :=
  let symbol := codeBits (symbolCode % 64) (symbolCode / 64)
  if symbolCode % 64 + runCode % 64 + 8 < symbolCode % 64 * extra then
    symbol ++ codeBits (runCode % 64) (runCode / 64) ++ codeBits 8 extra
  else (List.replicate (extra + 1) symbol).flatten

/-- PIZ's entropy encoder groups at most 256 identical samples per run. -/
def payloadBitsGo (table : List Nat) (runCode : Nat) : Nat → List Nat → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, symbol :: rest =>
    let extra := min 255 (rest.takeWhile (· == symbol)).length
    runBits (table.getD symbol 0) runCode extra ++
      payloadBitsGo table runCode fuel (rest.drop extra)

def payloadBits (lengths symbols : List Nat) (runSymbol : Nat) : List Bool :=
  let table := canonicalTable lengths
  payloadBitsGo table (table.getD runSymbol 0) symbols.length symbols

end Huffman

end Exr.Piz
