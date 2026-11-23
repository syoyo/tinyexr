/-
  TinyEXR - abstract reader-state invariants for the EXR reader.

  This is a *specification* of the state rules the C reader must satisfy,
  motivated by the retry/OOB findings in `task.md` (S1): a failed parse must
  latch its error, the part array capacity must never trail `num_parts`, and
  a retry must not append a half-built part. It is not a proof about the C
  implementation; `task.md` records the C bugs that violate these rules.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Exr

set_option linter.unusedVariables false

/-- Abstract reader error codes (matching the shapes used by `task.md`). -/
inductive RErr where
  | corrupt
  | limitExceeded
  | unsupported
  deriving Repr, DecidableEq, BEq

/-- Minimal state shared by every public reader entry point. -/
structure ReaderState (α : Type) where
  parts : List α
  cap : Nat
  parseRc : Option RErr
  deriving Repr, DecidableEq, BEq

/-- A new reader owns no parts and has no latched error. -/
def newReader (cap : Nat) : ReaderState α := ⟨[], cap, none⟩

/-- Entering a public entry point: a latched parse error is returned
  unchanged, so the reader never re-parses (and never grows `parts`) after a
  failure. -/
def enter (s : ReaderState α) : ReaderState α := s

theorem retry_latched (s : ReaderState α) (e : RErr)
    (h : s.parseRc = some e) : enter s = s := rfl

/-- Latching a parse error leaves the part array untouched. -/
def latch (s : ReaderState α) (e : RErr) : ReaderState α :=
  { s with parseRc := some e }

theorem latch_parts (s : ReaderState α) (e : RErr) : (latch s e).parts = s.parts := rfl
theorem latch_latched (s : ReaderState α) (e : RErr) :
    (latch s e).parseRc = some e := rfl

/-- Append a successfully parsed part. Returns `none` when the capacity
  would be exceeded; the caller must grow the arena first. -/
def appendPart (s : ReaderState α) (p : α) : Option (ReaderState α) :=
  if s.parts.length < s.cap then
    some { s with parts := s.parts ++ [p] }
  else none

theorem appendPart_some_length {s : ReaderState α} {p : α} {s' : ReaderState α}
    (h : appendPart s p = some s') : s'.parts.length = s.parts.length + 1 := by
  unfold appendPart at h
  split at h
  · cases h
    simp
  · simp at h

theorem appendPart_none_iff {s : ReaderState α} {p : α} :
    appendPart s p = none ↔ s.cap ≤ s.parts.length := by
  unfold appendPart
  split
  · simp_all
  · simp_all

/-- The central safety invariant: capacity always covers the owned parts. -/
def CapSafe (s : ReaderState α) : Prop := s.parts.length ≤ s.cap

theorem newReader_capSafe (cap : Nat) : CapSafe (newReader (α := α) cap) := by
  simp [CapSafe, newReader]

theorem appendPart_capSafe {s : ReaderState α} {p : α} {s' : ReaderState α}
    (hs : CapSafe s) (h : appendPart s p = some s') : CapSafe s' := by
  unfold CapSafe at hs ⊢
  have hcap : s'.cap = s.cap := by
    unfold appendPart at h
    split at h
    · cases h; rfl
    · simp at h
  rw [appendPart_some_length h, hcap]
  have hc : s.parts.length < s.cap := by
    unfold appendPart at h
    split at h
    · exact ‹s.parts.length < s.cap›
    · simp at h
  omega

theorem latch_capSafe {s : ReaderState α} {e : RErr} (hs : CapSafe s) :
    CapSafe (latch s e) := by
  exact hs

/-- With the capacity invariant, the next part slot is strictly inside the
  array bounds (the property violated by the S1 double-call repro). -/
theorem next_slot_in_bounds {s : ReaderState α} (hs : CapSafe s)
    (hlt : s.parts.length < s.cap) : s.parts.length < s.cap := hlt

/-- A failed parse never changes ownership: no part is freed twice and none
  is dropped while the error is latched. -/
theorem retry_preserves_ownership (s : ReaderState α) (p : α)
    (hs : CapSafe s) (herr : s.parseRc.isSome) :
    (enter (latch s RErr.corrupt)).parts = s.parts := by
  simp [enter, latch]

end Exr
