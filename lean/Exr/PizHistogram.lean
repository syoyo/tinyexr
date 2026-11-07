/-
  TinyEXR - executable symbol histogram and entropy-source validity.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizFrequencySource

namespace Exr.Piz.Frequency

def increment (counts : Array Nat) (symbol : Nat) : Array Nat := counts.set! symbol (counts[symbol]!+1)

def countSymbols (symbols : List Nat) (size : Nat) : Array Nat :=
  symbols.foldl increment (Array.replicate size 0)

@[simp] theorem increment_size (counts : Array Nat) (symbol : Nat) :
    (increment counts symbol).size = counts.size := by simp [increment]

theorem countFold_size (symbols : List Nat) (counts : Array Nat) :
    (symbols.foldl increment counts).size = counts.size := by
  induction symbols generalizing counts with
  | nil => rfl
  | cons symbol rest ih => simp only [List.foldl_cons,ih,increment_size]

@[simp] theorem countSymbols_size (symbols : List Nat) (size : Nat) :
    (countSymbols symbols size).size = size := by rw [countSymbols,countFold_size,Array.size_replicate]

theorem increment_positive (counts : Array Nat) (symbol : Nat) (hi : symbol < counts.size) :
    0 < (increment counts symbol)[symbol]! := by
  rw [increment,Array.getElem!_set!_self _ _ _ hi]
  omega

theorem increment_preserves (counts : Array Nat) (symbol i : Nat) (hi : i < counts.size)
    (hp : 0 < counts[i]!) : 0 < (increment counts symbol)[i]! := by
  by_cases he : symbol = i
  · subst symbol; exact increment_positive counts i hi
  · rw [increment,Array.getElem!_set!_ne _ _ _ _ he]
    exact hp

theorem countFold_preserves (symbols : List Nat) (counts : Array Nat) (i : Nat)
    (hi : i < counts.size) (hp : 0 < counts[i]!) : 0 < (symbols.foldl increment counts)[i]! := by
  induction symbols generalizing counts with
  | nil => exact hp
  | cons symbol rest ih =>
    exact ih (increment counts symbol) (by simpa only [increment_size] using hi)
      (increment_preserves counts symbol i hi hp)

theorem countFold_covers (symbols : List Nat) (counts : Array Nat)
    (hb : ∀ symbol ∈ symbols, symbol < counts.size) :
    ∀ symbol ∈ symbols, 0 < (symbols.foldl increment counts)[symbol]! := by
  induction symbols generalizing counts with
  | nil => simp
  | cons next rest ih =>
    intro symbol hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst symbol
      exact countFold_preserves rest (increment counts next) next
        (by simpa only [increment_size] using hb next List.mem_cons_self)
        (increment_positive counts next (hb next List.mem_cons_self))
    · exact ih (increment counts next)
        (fun symbol hs => by simpa only [increment_size] using hb symbol (List.mem_cons_of_mem _ hs)) symbol hs

theorem countFold_absent (symbols : List Nat) (counts : Array Nat) (i : Nat)
    (hn : ∀ symbol ∈ symbols, symbol ≠ i) : (symbols.foldl increment counts)[i]! = counts[i]! := by
  induction symbols generalizing counts with
  | nil => rfl
  | cons symbol rest ih =>
    rw [List.foldl_cons,ih _ (fun s hs => hn s (List.mem_cons_of_mem _ hs)),increment,
      Array.getElem!_set!_ne _ _ _ _ (hn symbol List.mem_cons_self)]

theorem countSymbols_positive (symbols : List Nat) (size : Nat)
    (hb : ∀ symbol ∈ symbols, symbol < size) :
    ∀ symbol ∈ symbols, 0 < (countSymbols symbols size)[symbol]! :=
  countFold_covers symbols _ (by simpa only [Array.size_replicate] using hb)

theorem countSymbols_source (symbols : List Nat) (size : Nat)
    (hb : ∀ symbol ∈ symbols, symbol < size) :
    ∀ symbol ∈ symbols, symbol < (countSymbols symbols size).toList.length ∧
      (countSymbols symbols size).toList.getD symbol 0 ≠ 0 := by
  intro symbol hs
  have hi : symbol < (countSymbols symbols size).size := by rw [countSymbols_size]; exact hb symbol hs
  refine ⟨by simpa only [Array.length_toList] using hi,?_⟩
  rw [natArray_list_getD _ symbol hi]
  have hp := countSymbols_positive symbols size hb symbol hs
  omega

/-- The final histogram slot is active when allocation ends at the largest
source symbol, so heap preparation does not trim away or move the marker. -/
theorem countSymbols_last_nonzero (symbols : List Nat) (largest : Nat)
    (hb : ∀ symbol ∈ symbols, symbol ≤ largest) (hm : largest ∈ symbols) :
    (countSymbols symbols (largest+1)).toList.reverse.head? ≠ some 0 := by
  let counts := countSymbols symbols (largest+1)
  have hi : largest < counts.size := by rw [countSymbols_size]; omega
  have hp : 0 < counts[largest]! := countSymbols_positive symbols _ (fun s hs => by have := hb s hs; omega) largest hm
  rw [List.head?_reverse,List.getLast?_eq_getElem?,Array.length_toList,countSymbols_size]
  rw [show largest+1-1 = largest by omega,List.getElem?_eq_getElem (by simpa only [Array.length_toList,countSymbols_size] using Nat.lt_succ_self largest)]
  intro he
  have hz := Option.some.inj he
  change counts[largest] = 0 at hz
  rw [getElem!_pos counts largest hi] at hp
  omega

/-- All source and RLE-marker length conditions are now consequences of the
actual symbol histogram and a successful frequency-table emission. -/
theorem histogram_source_valid (symbols result : List Nat) (largest : Nat)
    (hb : ∀ symbol ∈ symbols, symbol ≤ largest) (hm : largest ∈ symbols)
    (he : lengths (countSymbols symbols (largest+1)).toList = some result) :
    Entropy.SourceValid result (largest+1) symbols := by
  have hsource := countSymbols_source symbols (largest+1) (fun s hs => by have := hb s hs; omega)
  have hr := lengths_source_valid _ result symbols he (countSymbols_last_nonzero symbols largest hb hm) hsource
  simpa only [Array.length_toList,countSymbols_size] using hr

theorem countSymbols_below_zero (symbols : List Nat) (size first : Nat)
    (hf : first ≤ size) (hs : ∀ symbol ∈ symbols, first ≤ symbol) :
    ∀ i, i < first → (countSymbols symbols size).toList.getD i 0 = 0 := by
  intro i hi
  have hib : i < (countSymbols symbols size).size := by rw [countSymbols_size]; omega
  rw [natArray_list_getD _ i hib]
  unfold countSymbols
  rw [countFold_absent symbols _ i (by intro symbol hm; have := hs symbol hm; omega)]
  rw [getElem!_pos (Array.replicate size 0) i (by simp only [Array.size_replicate]; omega)]
  simp

theorem histogram_sliced_source_valid (symbols result : List Nat) (largest first : Nat)
    (hb : ∀ symbol ∈ symbols, symbol ≤ largest) (hm : largest ∈ symbols)
    (hf : first ≤ largest+1) (hfirst : ∀ symbol ∈ symbols, first ≤ symbol)
    (he : lengths (countSymbols symbols (largest+1)).toList = some result) :
    Entropy.SourceValid (List.replicate first 0 ++ result.drop first) (largest+1) symbols := by
  have hsource := countSymbols_source symbols (largest+1) (fun s hs => by have := hb s hs; omega)
  have hsize : (countSymbols symbols (largest+1)).toList.length = largest+1 := by simp
  have hr := lengths_sliced_source_valid _ result symbols he
    (countSymbols_last_nonzero symbols largest hb hm) hsource first (by omega)
    (countSymbols_below_zero symbols (largest+1) first hf hfirst)
  simpa only [hsize] using hr

theorem foldMax_spec (symbols : List Nat) (initial : Nat) :
    initial ≤ symbols.foldl max initial ∧
      (∀ symbol ∈ symbols, symbol ≤ symbols.foldl max initial) ∧
      (symbols.foldl max initial = initial ∨ symbols.foldl max initial ∈ symbols) := by
  induction symbols generalizing initial with
  | nil => simp
  | cons symbol rest ih =>
    have hr := ih (max initial symbol)
    change initial ≤ rest.foldl max (max initial symbol) ∧ _
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) hr.1,?_,?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with hs | hs
      · subst s; exact Nat.le_trans (Nat.le_max_right _ _) hr.1
      · exact hr.2.1 s hs
    · rcases hr.2.2 with he | hm
      · by_cases hle : initial ≤ symbol
        · right
          rw [List.foldl_cons,he,Nat.max_eq_right hle]
          exact List.mem_cons_self
        · left
          rw [List.foldl_cons,he,Nat.max_eq_left (by omega)]
      · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem foldMax_zero_mem (symbols : List Nat) (hn : symbols ≠ []) : symbols.foldl max 0 ∈ symbols := by
  have hb := foldMax_spec symbols 0
  rcases hb.2.2 with he | hm
  · have hh := hb.2.1 (symbols.head hn) (List.head_mem hn)
    have hz : symbols.head hn = symbols.foldl max 0 := by omega
    exact hz ▸ List.head_mem hn
  · exact hm

theorem foldMin_bounds (symbols : List Nat) (initial : Nat) :
    symbols.foldl min initial ≤ initial ∧ ∀ symbol ∈ symbols, symbols.foldl min initial ≤ symbol := by
  induction symbols generalizing initial with
  | nil => simp
  | cons symbol rest ih =>
    have hr := ih (min initial symbol)
    change rest.foldl min (min initial symbol) ≤ initial ∧ _
    refine ⟨Nat.le_trans hr.1 (Nat.min_le_left _ _),?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst s; exact Nat.le_trans hr.1 (Nat.min_le_right _ _)
    · exact hr.2 s hs

/-- For the exact minimum/maximum and histogram computation used by the
packet generator, every accepted length table satisfies entropy-source
validity after restoring its omitted zero prefix. -/
theorem generated_source_valid (symbols result : List Nat) (hn : symbols ≠ [])
    (he : lengths (countSymbols symbols (symbols.foldl max 0+1)).toList = some result) :
    Entropy.SourceValid (List.replicate (symbols.foldl min 65536) 0 ++ result.drop (symbols.foldl min 65536))
      (symbols.foldl max 0+1) symbols := by
  have hm := foldMax_zero_mem symbols hn
  have hmin := (foldMin_bounds symbols 65536).2
  apply histogram_sliced_source_valid symbols result (symbols.foldl max 0) (symbols.foldl min 65536)
    (foldMax_spec symbols 0).2.1 hm
  · have hh := hmin _ hm
    omega
  · exact hmin
  · exact he

end Exr.Piz.Frequency
