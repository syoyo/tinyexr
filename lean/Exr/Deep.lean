/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Deep data payload model (OpenEXR deep scan-line and deep tile chunks).

  A deep chunk's payload, after the 28/32-byte chunk header
  (`ChunkLayout.headerSize`, in `Exr/File.lean`), holds:

  * a *packed offset table*: one 4-byte cumulative sample count per pixel
    of the chunk's scan-lines, in scan-line-major order;
  * *packed sample data*: for each channel, the chunk's samples stacked
    channel-major.

  This module models the cumulative-count algebra (the count table and the
  cumulative table are exact inverses — the C reader's
  `cnt = cum - prev` chain), the encoder validity check (the C reader
  rejects negative counts), and the unpacked-size accounting:
  the unpacked offset-table size and the unpacked sample size
  (`total × pixelSize`, tied to the chunk's `totals` field by the last
  cumulative count).

  Sample bytes themselves are codec output and are modelled as opaque bytes;
  only their sizes are accounted here.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Size

namespace Exr

namespace Deep

/-- Cumulative-count table construction: prefix sums of per-pixel counts. -/
def cumCountsGo (prev : Int32) : List Int32 → List Int32
  | [] => []
  | c :: cs => (prev + c) :: cumCountsGo (prev + c) cs

def cumCounts (cs : List Int32) : List Int32 := cumCountsGo 0 cs

/-- Inverse: recover per-pixel counts from cumulative counts (the C reader's
    `cnt = cum - prev` chain). -/
def diffCountsGo (prev : Int32) : List Int32 → List Int32
  | [] => []
  | c :: cs => (c - prev) :: diffCountsGo c cs

def diffCounts (cs : List Int32) : List Int32 := diffCountsGo 0 cs

theorem add_sub_cancel' (a b : Int32) : (a + b) - a = b := by
  rw [Int32.add_comm a b]
  exact Int32.add_sub_cancel b a

theorem add_sub' (a b : Int32) : a + (b - a) = b := by
  rw [Int32.add_comm a (b - a)]
  exact Int32.sub_add_cancel b a

theorem diffCounts_cumCountsGo (prev : Int32) (cs : List Int32) :
    diffCountsGo prev (cumCountsGo prev cs) = cs := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih =>
    show ((prev + c) - prev) :: diffCountsGo (prev + c) (cumCountsGo (prev + c) cs) = c :: cs
    rw [add_sub_cancel' prev c]
    exact congrArg (List.cons c) (ih (prev := prev + c))

theorem diffCounts_cumCounts (cs : List Int32) :
    diffCounts (cumCounts cs) = cs :=
  diffCounts_cumCountsGo 0 cs

theorem cumCounts_diffCountsGo (prev : Int32) (cs : List Int32) :
    cumCountsGo prev (diffCountsGo prev cs) = cs := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih =>
    show (prev + (c - prev)) :: cumCountsGo (prev + (c - prev)) (diffCountsGo c cs) = c :: cs
    rw [add_sub' prev c]
    exact congrArg (List.cons c) (ih (prev := c))

theorem cumCounts_diffCounts (cs : List Int32) :
    cumCounts (diffCounts cs) = cs :=
  cumCounts_diffCountsGo 0 cs

/-- Total number of samples in a count table. -/
def totalOf (cs : List Int32) : Int32 := cs.foldl (· + ·) 0

theorem foldl_add_eq (cs : List Int32) (a : Int32) :
    cs.foldl (· + ·) a = a + cs.foldl (· + ·) 0 := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a := a + c), ih (a := 0 + c),
      Int32.zero_add, Int32.add_assoc]

theorem totalOf_cons (c : Int32) (cs : List Int32) :
    totalOf (c :: cs) = c + totalOf cs := by
  unfold totalOf
  rw [List.foldl_cons, foldl_add_eq, Int32.zero_add]

/-- The last cumulative count is the chunk's total (`totals[ci] = prev` in the
    C reader): the final accumulator equals the running total. -/
theorem cumCountsGo_last (prev : Int32) (cs : List Int32) :
    (cumCountsGo prev cs).getLast?.getD prev = prev + totalOf cs := by
  induction cs generalizing prev with
  | nil =>
    show ([] : List Int32).getLast?.getD prev = prev + totalOf []
    simp [totalOf, Int32.add_zero]
  | cons c cs ih =>
    show ((prev + c) :: cumCountsGo (prev + c) cs).getLast?.getD prev
        = prev + totalOf (c :: cs)
    rw [List.getLast?_cons, ih (prev := prev + c), totalOf_cons, Int32.add_assoc]
    rfl

theorem cumCounts_last (cs : List Int32) :
    (cumCounts cs).getLast?.getD 0 = totalOf cs := by
  have h := cumCountsGo_last 0 cs
  rw [Int32.zero_add] at h
  exact h

/-- Validity of a cumulative table: every count is non-negative (the C
    reader's `cnt < 0` rejection). -/
def validTable (cs : List Int32) : Prop :=
  ∀ c ∈ diffCounts cs, 0 ≤ c

theorem cumCounts_valid {cs : List Int32} (hnonneg : ∀ c ∈ cs, 0 ≤ c) :
    validTable (cumCounts cs) := by
  unfold validTable
  rw [diffCounts_cumCounts]
  exact hnonneg

/-- Uncompressed bytes of a deep chunk's packed offset table:
    one 4-byte cumulative count per pixel in the chunk's scan-lines. -/
def offsetTableBytes (width nlines : Nat) : Nat :=
  width * nlines * 4

theorem offsetTableBytes_eq (width nlines : Nat) :
    offsetTableBytes width nlines = 4 * (width * nlines) := by
  unfold offsetTableBytes
  rw [Nat.mul_comm]

/-- A deep chunk's header fields, after the shared `ChunkLayout` chunk
    header: `packedOffsetTableSize`, `packedSampleSize` and
    `unpackedSampleSize` in bytes. -/
structure DeepChunk where
  nlines : Nat
  totalSamples : Nat
  packedOffsetTableSize : Nat
  packedSampleSize : Nat
  unpackedSampleSize : Nat

namespace DeepChunk

/-- Uncompressed sample bytes of a chunk: `total × pixelSize`, the C check
    `usds == total * sample_size`. -/
def sampleBytes (totalSamples : Nat) (cs : List Channel) : Nat :=
  totalSamples * pixelSize cs

/-- On-disk chunk size: shared chunk header plus the two compressed payload
    regions. -/
def onDiskBytes (c : DeepChunk) (layout : ChunkLayout) : Nat :=
  layout.headerSize + c.packedOffsetTableSize + c.packedSampleSize

/-- A deep chunk is well-formed for a part of `width`, channel list `cs` and
    per-pixel count table `counts` when the table covers exactly the chunk's
    pixels, its total matches the chunk's sample count, and the unpacked
    sample size matches the channel sizes. -/
def WellFormed (c : DeepChunk) (width : Nat) (cs : List Channel)
    (counts : List Int32) : Prop :=
  counts.length = width * c.nlines ∧
  (totalOf counts).toInt = (c.totalSamples : Int) ∧
  c.unpackedSampleSize = sampleBytes c.totalSamples cs

theorem WellFormed.offsetTableSize {c : DeepChunk} {width : Nat}
    {cs : List Channel} {counts : List Int32} (h : c.WellFormed width cs counts) :
    offsetTableBytes width c.nlines = 4 * counts.length := by
  rw [offsetTableBytes_eq, h.1]

theorem WellFormed.sampleSize {c : DeepChunk} {width : Nat}
    {cs : List Channel} {counts : List Int32} (h : c.WellFormed width cs counts) :
    c.unpackedSampleSize = c.totalSamples * pixelSize cs :=
  h.2.2

end DeepChunk

end Deep

end Exr
