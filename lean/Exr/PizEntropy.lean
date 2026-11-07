/-
  TinyEXR - PIZ Huffman symbol/repeat parsing and payload composition.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizCodebook

namespace Exr.Piz.Entropy

inductive Event where
  | literal (symbol : Nat)
  | run (count : Nat)
  deriving Repr, DecidableEq

def Event.bits (lengths : List Nat) (marker : Nat) : Event → List Bool
  | .literal symbol => Codebook.wordBits ((canonicalTable lengths).getD symbol 0)
  | .run count => Codebook.wordBits ((canonicalTable lengths).getD marker 0) ++ Huffman.codeBits 8 count

def Event.Valid (lengths : List Nat) (marker : Nat) : Event → Prop
  | .literal symbol => symbol < marker ∧ symbol < lengths.length ∧
      0 < lengths.getD symbol 0 ∧ lengths.getD symbol 0 < 59
  | .run count => count < 256 ∧ marker < lengths.length ∧
      0 < lengths.getD marker 0 ∧ lengths.getD marker 0 < 59

def readEvent (trie : Codebook.Trie) (marker : Nat) (bits : List Bool) :
    Option (Event × List Bool) := do
  let (symbol,rest) ← Codebook.decode trie bits
  if symbol = marker then
    let (count,tail) ← Bits.read 8 rest
    pure (.run count,tail)
  else if symbol < marker then pure (.literal symbol,rest) else none

/-- The run marker requires an already decoded predecessor, including when
its count is zero. Expansion is bounded by the caller's remaining output. -/
def expand (previous : Option Nat) : Event → Option (List Nat × Option Nat)
  | .literal symbol => some ([symbol],some symbol)
  | .run count => do
    let symbol ← previous
    pure (List.replicate count symbol,previous)

def expandEvents (previous : Option Nat) : List Event → Option (List Nat × Option Nat)
  | [] => some ([],previous)
  | event::rest => do
    let (values,next) ← expand previous event
    let (tail,last) ← expandEvents next rest
    pure (values ++ tail,last)

theorem readEvent_bits (lengths : List Nat) (marker : Nat) (trie : Codebook.Trie)
    (hb : Codebook.build lengths = some trie) (event : Event) (hv : event.Valid lengths marker)
    (suffix : List Bool) :
    readEvent trie marker (event.bits lengths marker ++ suffix) = some (event,suffix) := by
  cases event with
  | literal symbol =>
    have hr := Codebook.decode_canonical lengths trie hb symbol hv.2.1 hv.2.2.1 (Nat.lt_trans hv.2.2.2 (by decide)) suffix
    simp only [Event.bits, readEvent]
    rw [hr]
    simp [Nat.ne_of_lt hv.1, hv.1]
  | run count =>
    have hr := Codebook.decode_canonical lengths trie hb marker hv.2.1 hv.2.2.1 (Nat.lt_trans hv.2.2.2 (by decide))
      (Huffman.codeBits 8 count ++ suffix)
    have hc := Bits.read_codeBits 8 count suffix hv.1
    simp only [Event.bits, List.append_assoc, readEvent]
    rw [hr]
    simp [hc]

theorem Event.bits_pos (lengths : List Nat) (marker : Nat) (event : Event)
    (hv : event.Valid lengths marker) : 0 < (event.bits lengths marker).length := by
  cases event with
  | literal symbol =>
    have hw := canonicalWord_length lengths symbol (Nat.lt_trans hv.2.2.2 (by decide))
    rw [Event.bits, Codebook.canonicalTable_getD lengths symbol hv.2.1,
      Codebook.wordBits, Bits.codeBits_length, hw]
    exact hv.2.2.1
  | run count => simp [Event.bits, Bits.codeBits_length]

/-- Parse until the declared bit stream ends. Zero-repeat tokens may appear
after the output is full, matching C; literal overflow is always rejected. -/
def decodeGo (trie : Codebook.Trie) (marker : Nat) :
    Nat → Nat → Option Nat → List Bool → Option (List Nat × Option Nat)
  | _, remaining, previous, [] => if remaining = 0 then some ([],previous) else none
  | 0, _, _, _::_ => none
  | fuel+1, remaining, previous, bits => do
    let (event,tail) ← readEvent trie marker bits
    let (values,next) ← expand previous event
    if values.length ≤ remaining then
      let (rest,last) ← decodeGo trie marker fuel (remaining-values.length) next tail
      pure (values ++ rest,last)
    else none

def decode (lengths : List Nat) (marker count : Nat) (bits : List Bool) : Option (List Nat) := do
  let trie ← Codebook.build lengths
  let (values,_) ← decodeGo trie marker bits.length count none bits
  pure values

/-- A supplied event stream is decoded by the actual checked canonical
codebook, with no independent path/tree assumptions. -/
theorem decodeGo_events (lengths : List Nat) (marker : Nat) (trie : Codebook.Trie)
    (hb : Codebook.build lengths = some trie)
    (events : List Event) (hv : ∀ e ∈ events, e.Valid lengths marker)
    (previous : Option Nat) (values : List Nat) (last : Option Nat)
    (he : expandEvents previous events = some (values,last))
    (fuel : Nat) (hf : events.length ≤ fuel) :
    decodeGo trie marker fuel values.length previous (events.flatMap (Event.bits lengths marker)) =
      some (values,last) := by
  induction events generalizing fuel previous values last with
  | nil =>
    have hp : ([],previous) = (values,last) := Option.some.inj he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    simp [decodeGo]
  | cons event rest ih =>
    have hvalid := hv event List.mem_cons_self
    have hrest : ∀ e ∈ rest, e.Valid lengths marker := fun e hm => hv e (List.mem_cons_of_mem event hm)
    cases hx : expand previous event with
    | none => simp [expandEvents, hx] at he
    | some pair =>
      rcases pair with ⟨head,next⟩
      cases hy : expandEvents next rest with
      | none => simp [expandEvents, hx, hy] at he
      | some pair =>
        rcases pair with ⟨tail,final⟩
        have hp : (head ++ tail,final) = (values,last) := by simpa [expandEvents, hx, hy] using he
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
        obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1, by simp only [List.length_cons] at hf; omega⟩
        have hfr : rest.length ≤ f := by simp only [List.length_cons] at hf; omega
        have hbits : event.bits lengths marker ++ rest.flatMap (Event.bits lengths marker) ≠ [] := by
          have hp := Event.bits_pos lengths marker event hvalid
          intro hz
          have hzlen := congrArg List.length hz
          simp only [List.length_append, List.length_nil] at hzlen
          omega
        simp only [List.flatMap_cons, List.length_append]
        rw [decodeGo]
        have hs := readEvent_bits lengths marker trie hb event hvalid (rest.flatMap (Event.bits lengths marker))
        rw [hs]
        change (do
          let result ← expand previous event
          if result.1.length ≤ head.length + tail.length then
            (do
              let parsed ← decodeGo trie marker f (head.length + tail.length-result.1.length)
                result.2 (rest.flatMap (Event.bits lengths marker))
              pure (result.1 ++ parsed.1,parsed.2)) else none) = _
        rw [hx]
        change (if head.length ≤ head.length + tail.length then
          (do
            let parsed ← decodeGo trie marker f (head.length + tail.length-head.length)
              next (rest.flatMap (Event.bits lengths marker))
            pure (head ++ parsed.1,parsed.2)) else none) = _
        rw [ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ih hrest next tail final hy f hfr]
        rfl
        exact hbits

theorem events_bits_length (lengths : List Nat) (marker : Nat) (events : List Event)
    (hv : ∀ e ∈ events, e.Valid lengths marker) :
    events.length ≤ (events.flatMap (Event.bits lengths marker)).length := by
  induction events with
  | nil => simp
  | cons event rest ih =>
    have hp := Event.bits_pos lengths marker event (hv event List.mem_cons_self)
    have ht := ih (fun e hm => hv e (List.mem_cons_of_mem event hm))
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

theorem decode_events (lengths : List Nat) (marker : Nat) (trie : Codebook.Trie)
    (hb : Codebook.build lengths = some trie) (events : List Event)
    (hv : ∀ e ∈ events, e.Valid lengths marker) (values : List Nat) (last : Option Nat)
    (he : expandEvents none events = some (values,last)) :
    decode lengths marker values.length (events.flatMap (Event.bits lengths marker)) = some values := by
  have hr := decodeGo_events lengths marker trie hb events hv none values last he _
    (events_bits_length lengths marker events hv)
  unfold decode
  rw [hb]
  change (do
    let result ← decodeGo trie marker (events.flatMap (Event.bits lengths marker)).length values.length none
      (events.flatMap (Event.bits lengths marker))
    pure result.1) = _
  rw [hr]
  rfl

def runEvents (lengths : List Nat) (marker symbol extra : Nat) : List Event :=
  let table := canonicalTable lengths
  let s := table.getD symbol 0
  let r := table.getD marker 0
  if s%64 + r%64 + 8 < s%64 * extra then [.literal symbol,.run extra]
  else List.replicate (extra+1) (.literal symbol)

theorem runEvents_bits (lengths : List Nat) (marker symbol extra : Nat) :
    (runEvents lengths marker symbol extra).flatMap (Event.bits lengths marker) =
      Huffman.runBits ((canonicalTable lengths).getD symbol 0)
        ((canonicalTable lengths).getD marker 0) extra := by
  dsimp only [runEvents, Huffman.runBits]
  split
  · simp [Event.bits, Codebook.wordBits, List.append_assoc]
  · simp [Event.bits, Codebook.wordBits, List.flatMap_replicate]

theorem runEvents_valid (lengths : List Nat) (marker symbol extra : Nat)
    (hs : Event.Valid lengths marker (.literal symbol))
    (hr : Event.Valid lengths marker (.run extra)) :
    ∀ e ∈ runEvents lengths marker symbol extra, e.Valid lengths marker := by
  dsimp only [runEvents]
  split
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hs
    · exact hr
  · intro e he
    have heq : e = .literal symbol := (List.mem_replicate.mp he).2
    rw [heq]
    exact hs

theorem expand_literals (symbol n : Nat) (previous : Option Nat) :
    expandEvents previous (List.replicate (n+1) (.literal symbol)) =
      some (List.replicate (n+1) symbol,some symbol) := by
  induction n generalizing previous with
  | zero => simp [List.replicate_succ, expandEvents, expand]
  | succ n ih =>
    rw [show List.replicate (n+1+1) (Event.literal symbol) =
      .literal symbol :: List.replicate (n+1) (Event.literal symbol) from List.replicate_succ]
    rw [expandEvents, expand]
    change (do
      let result ← expandEvents (some symbol) (List.replicate (n+1) (.literal symbol))
      pure (symbol::result.1,result.2)) = _
    rw [ih]
    simp [List.replicate_succ]

theorem expand_runEvents (lengths : List Nat) (marker symbol extra : Nat) (previous : Option Nat) :
    expandEvents previous (runEvents lengths marker symbol extra) =
      some (List.replicate (extra+1) symbol,some symbol) := by
  dsimp only [runEvents]
  split
  · simp [expandEvents, expand, List.replicate_succ]
  · exact expand_literals symbol extra previous

theorem expandEvents_append (front tail : List Event) (previous : Option Nat) :
    expandEvents previous (front ++ tail) = (do
      let head ← expandEvents previous front
      let rest ← expandEvents head.2 tail
      pure (head.1 ++ rest.1,rest.2)) := by
  induction front generalizing previous with
  | nil =>
    cases he : expandEvents previous tail <;> simp [expandEvents, he]
  | cons event front ih =>
    simp only [List.cons_append, expandEvents]
    cases hx : expand previous event with
    | none => rfl
    | some pair =>
      rcases pair with ⟨values,next⟩
      change (do
        let parsed ← expandEvents next (front ++ tail)
        pure (values ++ parsed.1,parsed.2)) =
        (do
          let head ← (do
            let middle ← expandEvents next front
            pure (values ++ middle.1,middle.2))
          let rest ← expandEvents head.2 tail
          pure (head.1 ++ rest.1,rest.2))
      rw [ih]
      cases hy : expandEvents next front with
      | none => simp
      | some pair =>
        rcases pair with ⟨middle,last⟩
        cases hz : expandEvents last tail <;> simp [hz, List.append_assoc]

def eventsGo (lengths : List Nat) (marker : Nat) : Nat → List Nat → List Event
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, symbol::rest =>
    let extra := min 255 (rest.takeWhile (· == symbol)).length
    runEvents lengths marker symbol extra ++ eventsGo lengths marker fuel (rest.drop extra)

theorem eventsGo_bits (lengths : List Nat) (marker fuel : Nat) (samples : List Nat) :
    (eventsGo lengths marker fuel samples).flatMap (Event.bits lengths marker) =
      Huffman.payloadBitsGo (canonicalTable lengths) ((canonicalTable lengths).getD marker 0) fuel samples := by
  induction fuel generalizing samples with
  | zero => rfl
  | succ fuel ih =>
    cases samples with
    | nil => rfl
    | cons symbol rest =>
      simp only [eventsGo, List.flatMap_append, runEvents_bits, ih, Huffman.payloadBitsGo]

/-- All source symbols are active, distinct from the RLE marker. -/
def Active (lengths : List Nat) (marker symbol : Nat) : Prop :=
  Event.Valid lengths marker (.literal symbol)

def MarkerValid (lengths : List Nat) (marker : Nat) : Prop :=
  marker < lengths.length ∧ 0 < lengths.getD marker 0 ∧ lengths.getD marker 0 < 59

theorem eventsGo_valid (lengths : List Nat) (marker fuel : Nat) (samples : List Nat)
    (hm : MarkerValid lengths marker) (hs : ∀ s ∈ samples, Active lengths marker s) :
    ∀ e ∈ eventsGo lengths marker fuel samples, e.Valid lengths marker := by
  induction fuel generalizing samples with
  | zero => simp [eventsGo]
  | succ fuel ih =>
    cases samples with
    | nil => simp [eventsGo]
    | cons symbol rest =>
      simp only [eventsGo, List.mem_append]
      intro e he
      rcases he with he | he
      · apply runEvents_valid lengths marker symbol _ (hs symbol List.mem_cons_self) ?_ e he
        refine ⟨?_,hm⟩
        have hb := Nat.min_le_left 255 (rest.takeWhile (· == symbol)).length
        omega
      · apply ih (rest.drop (min 255 (rest.takeWhile (· == symbol)).length))
          (fun s h => hs s (List.mem_cons_of_mem symbol (List.mem_of_mem_drop h))) e he

private theorem takeWhile_symbol (samples : List Nat) (symbol : Nat) :
    samples.takeWhile (· == symbol) = List.replicate (samples.takeWhile (· == symbol)).length symbol := by
  induction samples with
  | nil => rfl
  | cons s rest ih =>
    by_cases he : s = symbol
    · subst s
      simpa [List.takeWhile_cons, List.replicate_succ] using congrArg (symbol :: ·) ih
    · simp [he]

private theorem take_symbol_prefix (samples : List Nat) (symbol count : Nat)
    (hc : count ≤ (samples.takeWhile (· == symbol)).length) :
    samples.take count = List.replicate count symbol := by
  have hp : samples = samples.takeWhile (· == symbol) ++ samples.dropWhile (· == symbol) :=
    List.takeWhile_append_dropWhile.symm
  calc
    samples.take count = (samples.takeWhile (· == symbol) ++ samples.dropWhile (· == symbol)).take count :=
      congrArg (List.take count) hp
    _ = (samples.takeWhile (· == symbol)).take count := List.take_append_of_le_length hc
    _ = List.replicate count symbol := by
      rw [takeWhile_symbol, List.take_replicate, Nat.min_eq_left hc]

theorem expand_eventsGo (lengths : List Nat) (marker fuel : Nat) (samples : List Nat)
    (hf : samples.length ≤ fuel) (previous : Option Nat) :
    ∃ last, expandEvents previous (eventsGo lengths marker fuel samples) = some (samples,last) := by
  induction fuel generalizing samples previous with
  | zero =>
    have he : samples = [] := List.length_eq_zero_iff.mp (by omega)
    subst samples
    exact ⟨previous,rfl⟩
  | succ fuel ih =>
    cases samples with
    | nil => exact ⟨previous,rfl⟩
    | cons symbol rest =>
      let extra := min 255 (rest.takeWhile (· == symbol)).length
      have hd : (rest.drop extra).length ≤ fuel := by
        simp only [List.length_cons] at hf
        rw [List.length_drop]
        omega
      obtain ⟨last,ht⟩ := ih (rest.drop extra) hd (some symbol)
      refine ⟨last, ?_⟩
      rw [eventsGo, expandEvents_append, expand_runEvents]
      change (do
        let parsed ← expandEvents (some symbol) (eventsGo lengths marker fuel (rest.drop extra))
        pure (List.replicate (extra+1) symbol ++ parsed.1, parsed.2)) = _
      rw [ht]
      have hp : rest.take extra = List.replicate extra symbol :=
        take_symbol_prefix rest symbol extra (Nat.min_le_right _ _)
      change some (List.replicate (extra+1) symbol ++ rest.drop extra,last) = some (symbol::rest,last)
      simp only [List.replicate_succ, List.cons_append, ← hp, List.take_append_drop]

def SourceValid (lengths : List Nat) (marker : Nat) (samples : List Nat) : Prop :=
  MarkerValid lengths marker ∧ ∀ s ∈ samples, Active lengths marker s

/-- Complete entropy encode/decode inverse for the actual greedy PIZ
symbol/RLE writer and a successfully checked canonical table. -/
theorem decode_payloadBits (lengths : List Nat) (marker : Nat) (samples : List Nat)
    (trie : Codebook.Trie) (hb : Codebook.build lengths = some trie)
    (hv : SourceValid lengths marker samples) :
    decode lengths marker samples.length (Huffman.payloadBits lengths samples marker) = some samples := by
  obtain ⟨last,he⟩ := expand_eventsGo lengths marker samples.length samples (Nat.le_refl _) none
  have hr := decode_events lengths marker trie hb (eventsGo lengths marker samples.length samples)
    (eventsGo_valid lengths marker samples.length samples hv.1 hv.2) samples last he
  rw [eventsGo_bits] at hr
  exact hr

def Event.InRange (marker : Nat) : Event → Prop
  | .literal symbol => symbol < marker
  | .run count => count < 256

theorem readEvent_range (trie : Codebook.Trie) (marker : Nat) (bits : List Bool)
    (event : Event) (suffix : List Bool) (he : readEvent trie marker bits = some (event,suffix)) :
    event.InRange marker := by
  cases hd : Codebook.decode trie bits with
  | none => simp [readEvent, hd] at he
  | some pair =>
    rcases pair with ⟨symbol,rest⟩
    by_cases hm : symbol = marker
    · cases hb : Bits.read 8 rest with
      | none => simp [readEvent, hd, hm, hb] at he
      | some pair =>
        rcases pair with ⟨count,tail⟩
        have hp : (Event.run count,tail) = (event,suffix) := by simpa [readEvent, hd, hm, hb] using he
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
        exact (Bits.read_bounds 8 rest count tail hb).2.2
    · by_cases hl : symbol < marker
      · have hp : (Event.literal symbol,rest) = (event,suffix) := by simpa [readEvent, hd, hm, hl] using he
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
        exact hl
      · simp [readEvent, hd, hm, hl] at he

theorem expand_range (marker : Nat) (previous : Option Nat) (event : Event)
    (hp : ∀ p ∈ previous, p < marker) (he : event.InRange marker)
    (values : List Nat) (next : Option Nat) (hx : expand previous event = some (values,next)) :
    (∀ v ∈ values, v < marker) ∧ (∀ p ∈ next, p < marker) := by
  cases event with
  | literal symbol =>
    have hpair : ([symbol],some symbol) = (values,next) := Option.some.inj hx
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hpair
    have hs : symbol < marker := he
    simpa using hs
  | run count =>
    cases previous with
    | none => simp [expand] at hx
    | some symbol =>
      have hpair : (List.replicate count symbol,some symbol) = (values,next) := Option.some.inj hx
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hpair
      have hs := hp symbol (by simp)
      constructor
      · intro v hv
        have hv := (List.mem_replicate.mp hv).2
        simpa [hv] using hs
      · simpa using hs

/-- Successful entropy parsing fills exactly its output budget and never
emits the RLE marker or a value outside the sample alphabet. -/
theorem decodeGo_sound (trie : Codebook.Trie) (marker fuel remaining : Nat)
    (previous : Option Nat) (hp : ∀ p ∈ previous, p < marker)
    (bits : List Bool) (values : List Nat) (last : Option Nat)
    (hr : decodeGo trie marker fuel remaining previous bits = some (values,last)) :
    values.length = remaining ∧ (∀ v ∈ values, v < marker) ∧ (∀ p ∈ last, p < marker) := by
  induction fuel generalizing remaining previous bits values last with
  | zero =>
    cases bits with
    | nil =>
      by_cases hn : remaining = 0
      · have he : ([],previous) = (values,last) := by simpa [decodeGo, hn] using hr
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        simpa [hn] using hp
      · simp [decodeGo, hn] at hr
    | cons b rest => simp [decodeGo] at hr
  | succ fuel ih =>
    cases bits with
    | nil =>
      by_cases hn : remaining = 0
      · have he : ([],previous) = (values,last) := by simpa [decodeGo, hn] using hr
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        simpa [hn] using hp
      · simp [decodeGo, hn] at hr
    | cons b rest =>
      cases he : readEvent trie marker (b::rest) with
      | none => simp [decodeGo, he] at hr
      | some pair =>
        rcases pair with ⟨event,tail⟩
        cases hx : expand previous event with
        | none => simp [decodeGo, he, hx] at hr
        | some pair =>
          rcases pair with ⟨head,next⟩
          have hex := expand_range marker previous event hp (readEvent_range _ _ _ _ _ he) head next hx
          by_cases hf : head.length ≤ remaining
          · cases hs : decodeGo trie marker fuel (remaining-head.length) next tail with
            | none => simp [decodeGo, he, hx, hf, hs] at hr
            | some pair =>
              rcases pair with ⟨endValues,endPrev⟩
              have ht : (head ++ endValues,endPrev) = (values,last) := by
                simpa [decodeGo, he, hx, hf, hs] using hr
              obtain ⟨rfl,rfl⟩ := Prod.mk.inj ht
              have hi := ih _ next hex.2 tail endValues endPrev hs
              refine ⟨?_,?_,hi.2.2⟩
              · rw [List.length_append]
                omega
              · intro v hv
                rcases List.mem_append.mp hv with hv | hv
                · exact hex.1 v hv
                · exact hi.2.1 v hv
          · simp [decodeGo, he, hx, hf] at hr

theorem decode_sound (lengths : List Nat) (marker count : Nat) (bits : List Bool)
    (values : List Nat) (hd : decode lengths marker count bits = some values) :
    values.length = count ∧ ∀ v ∈ values, v < marker := by
  cases hb : Codebook.build lengths with
  | none => simp [decode, hb] at hd
  | some trie =>
    cases hr : decodeGo trie marker bits.length count none bits with
    | none => simp [decode, hb, hr] at hd
    | some pair =>
      rcases pair with ⟨out,last⟩
      have he : out = values := by simpa [decode, hb, hr] using hd
      subst values
      have hs := decodeGo_sound trie marker bits.length count none (by simp) bits out last hr
      exact ⟨hs.1,hs.2.1⟩

end Exr.Piz.Entropy
