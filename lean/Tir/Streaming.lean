/-
  TinyEXR - abstract streaming state machine for tir.

  Models the ring-buffer bookkeeping in `tir__push_row` / `tir__pull_row`:
  a push may not evict a source row still needed by the next pull; a pull
  succeeds exactly when all rows in its window are resident. The pixel math
  itself is covered by `Tir.Kernels`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tir

set_option linter.unusedVariables false

inductive StreamRc where
  | ok | wouldBlock | error
  deriving Repr, DecidableEq, BEq

/-- Ring slot contents: `-1` means empty. -/
structure StreamState where
  ringSrcY : List Int      -- length == ringCap
  ringCap : Nat
  imageHeight : Nat
  rowsPushed : Nat
  curDst : Nat
  lastPending : Bool
  deriving Repr

def newStream (cap height : Nat) : StreamState :=
  ⟨List.replicate cap (-1), cap, height, 0, 0, false⟩

def slotIndex (y : Int) (cap : Nat) : Nat := (y % (cap : Int)).toNat

/-- Resident rows (non-empty slots). -/
def resident (s : StreamState) : List Nat :=
  (s.ringSrcY.filter (fun y => y >= 0)).map (fun y => y.toNat)

theorem resident_length_le {s : StreamState} (hlen : s.ringSrcY.length = s.ringCap) :
    (resident s).length ≤ s.ringCap := by
  unfold resident
  have h := List.length_filter_le (p := fun y : Int => y >= 0) s.ringSrcY
  rw [List.length_map]
  omega

def pushBlocked (s : StreamState) (fin guard : Nat) : Bool :=
  let k := slotIndex (fin : Int) s.ringCap
  let old := s.ringSrcY.getD k (-1)
  old >= 0 && old >= (guard : Int) && s.ringCap < s.imageHeight

def pushRow (s : StreamState) (srcY fin guard : Nat) : StreamRc × StreamState :=
  if srcY != s.rowsPushed || s.ringCap <= 0 then (.error, s)
  else if pushBlocked s fin guard then (.wouldBlock, s)
  else
    let k := slotIndex (fin : Int) s.ringCap
    let ring := s.ringSrcY.set k (fin : Int)
    (.ok, { s with ringSrcY := ring, rowsPushed := srcY + 1 })

theorem push_preserves_occupancy (s : StreamState) (y fin guard : Nat)
    (hlen : s.ringSrcY.length = s.ringCap) {rc r'} (h : pushRow s y fin guard = (rc, r')) :
    (resident r').length ≤ r'.ringCap := by
  unfold pushRow at h
  split at h
  · cases h
    exact resident_length_le hlen
  · split at h
    · cases h
      exact resident_length_le hlen
    · cases h
      apply resident_length_le
      simp [hlen]

/-- A pull consumes `needed` resident rows and advances the destination. -/
def pullRow (s : StreamState) (needed : List Nat) : StreamRc × StreamState :=
  if needed.all (fun y => s.ringSrcY.contains (y : Int)) then
    (.ok, { s with curDst := s.curDst + 1 })
  else (.wouldBlock, s)

theorem pull_no_deadlock (s : StreamState) (needed : List Nat)
    (hall : needed.all (fun y => s.ringSrcY.contains (y : Int))) :
    (pullRow s needed).1 == .ok := by
  unfold pullRow
  rw [hall]
  rfl

theorem pull_progress (s : StreamState) (needed : List Nat)
    {rc r'} (h : pullRow s needed = (rc, r')) (hok : rc == .ok) :
    r'.curDst == s.curDst + 1 := by
  unfold pullRow at h
  split at h
  · cases h
    simp
  · cases h
    contradiction

end Tir
