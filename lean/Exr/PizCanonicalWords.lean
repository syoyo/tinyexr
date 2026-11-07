/-
  TinyEXR - representable and prefix-free descending canonical PIZ words.
  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Exr.PizCanonicalMass

namespace Exr.Piz.Canonical

theorem lengthCount_append (a b : List Nat) (depth : Nat) :
    lengthCount (a ++ b) depth = lengthCount a depth+lengthCount b depth := by
  simp [lengthCount,List.filter_append]

theorem depth_mem (lengths : List Nat) (i : Nat) (hi : i < lengths.length) : lengths.getD i 0 ∈ lengths := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem depth_eq_getElem (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    lengths.getD i 0 = lengths[i] := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]

theorem lengthCount_before_lt (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    lengthCount (lengths.take i) (lengths.getD i 0) < lengthCount lengths (lengths.getD i 0) := by
  have he : lengths = lengths.take i ++ lengths[i]::lengths.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hc := lengthCount_append (lengths.take i) (lengths[i]::lengths.drop (i+1)) (lengths.getD i 0)
  rw [← he,lengthCount_cons,← depth_eq_getElem lengths i hi] at hc
  simp only [ite_true] at hc
  omega

theorem start_count_bound (lengths : List Nat) (hc : Complete lengths) (depth : Nat)
    (hp : 0 < depth) (hd : depth ≤ 58) :
    codeStart lengths (58-depth)+lengthCount lengths depth ≤ 2^depth := by
  have hk : 58-depth < 58 := by omega
  have hs := codeStart_mass lengths hc (58-depth) hk
  rw [Nat.sub_sub_self hd] at hs
  have hstep := deeper_step lengths depth hp
  rw [← hs,← Nat.add_mul] at hstep
  have hfull := mass_split lengths (depth-1)
  rw [hc.2] at hfull
  have hb : (codeStart lengths (58-depth)+lengthCount lengths depth)*2^(58-depth) ≤ 2^58 := by omega
  have hpowers : 2^58 = 2^depth*2^(58-depth) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hpowers] at hb
  exact Nat.le_of_mul_le_mul_right hb (Nat.two_pow_pos _)

def code (lengths : List Nat) (i : Nat) : Nat :=
  codeStart lengths (58-lengths.getD i 0)+lengthCount (lengths.take i) (lengths.getD i 0)

theorem code_bound (lengths : List Nat) (hc : Complete lengths) (i : Nat)
    (hi : i < lengths.length) (hp : 0 < lengths.getD i 0) : code lengths i < 2^(lengths.getD i 0) := by
  have hd := hc.1 _ (depth_mem lengths i hi)
  have hr := lengthCount_before_lt lengths i hi
  have hb := start_count_bound lengths hc (lengths.getD i 0) hp hd
  unfold code
  omega

theorem word_code (lengths : List Nat) (hc : Complete lengths) (i : Nat)
    (hi : i < lengths.length) (hp : 0 < lengths.getD i 0) :
    canonicalWord lengths i/64 = code lengths i := by
  have hd := hc.1 _ (depth_mem lengths i hi)
  dsimp only [canonicalWord,code]
  rw [ite_eq_right (by omega : lengths.getD i 0 ≠ 0)]
  omega

theorem word_representable (lengths : List Nat) (hc : Complete lengths) (i : Nat)
    (hi : i < lengths.length) (hp : 0 < lengths.getD i 0) :
    Codebook.Representable (canonicalWord lengths i) := by
  have hd := hc.1 _ (depth_mem lengths i hi)
  unfold Codebook.Representable
  rw [canonicalWord_length lengths i (by omega),word_code lengths hc i hi hp]
  exact ⟨hp,hd,code_bound lengths hc i hi hp⟩

theorem wordBits_length (lengths : List Nat) (hc : Complete lengths) (i : Nat)
    (hi : i < lengths.length) : (Codebook.wordBits (canonicalWord lengths i)).length = lengths.getD i 0 := by
  have hd := hc.1 _ (depth_mem lengths i hi)
  rw [Codebook.wordBits,Bits.codeBits_length,canonicalWord_length lengths i (by omega)]

theorem wordBits_value (lengths : List Nat) (hc : Complete lengths) (i : Nat)
    (hi : i < lengths.length) (hp : 0 < lengths.getD i 0) :
    Bits.value (Codebook.wordBits (canonicalWord lengths i)) = code lengths i := by
  have hr := word_representable lengths hc i hi hp
  rw [Codebook.wordBits,Bits.value_codeBits,Nat.mod_eq_of_lt hr.2.2,word_code lengths hc i hi hp]

theorem deeper_antitone (lengths : List Nat) (a b : Nat) (hab : a ≤ b) : deeper lengths b ≤ deeper lengths a := by
  induction lengths with
  | nil => rfl
  | cons depth rest ih =>
    simp only [deeper]
    by_cases hb : b < depth
    · have ha : a < depth := by omega
      rw [ite_eq_left hb,ite_eq_left ha]
      omega
    · rw [ite_eq_right hb]
      omega

def start (lengths : List Nat) (i : Nat) : Nat := code lengths i*2^(58-lengths.getD i 0)

def finish (lengths : List Nat) (i : Nat) : Nat := start lengths i+2^(58-lengths.getD i 0)

/-- A deeper symbol's entire dyadic block precedes every shallower symbol. -/
theorem deeper_before (lengths : List Nat) (hc : Complete lengths) (i j : Nat)
    (hi : i < lengths.length) (hj : j < lengths.length)
    (hp : 0 < lengths.getD i 0) (hd : lengths.getD i 0 < lengths.getD j 0) :
    finish lengths j ≤ start lengths i := by
  have hposj : 0 < lengths.getD j 0 := by omega
  have hdj := hc.1 _ (depth_mem lengths j hj)
  have hdi := hc.1 _ (depth_mem lengths i hi)
  have hr := lengthCount_before_lt lengths j hj
  have hs := codeStart_mass lengths hc (58-lengths.getD j 0) (by omega)
  rw [Nat.sub_sub_self hdj] at hs
  have he := deeper_step lengths (lengths.getD j 0) hposj
  rw [← hs,← Nat.add_mul] at he
  have hm := deeper_antitone lengths (lengths.getD i 0) (lengths.getD j 0-1) (by omega)
  have hsi := codeStart_mass lengths hc (58-lengths.getD i 0) (by omega)
  rw [Nat.sub_sub_self hdi] at hsi
  have hlo := Nat.mul_le_mul_right (2^(58-lengths.getD j 0))
    (show code lengths j+1 ≤ codeStart lengths (58-lengths.getD j 0)+lengthCount lengths (lengths.getD j 0) by unfold code; omega)
  have hhi := Nat.mul_le_mul_right (2^(58-lengths.getD i 0))
    (show codeStart lengths (58-lengths.getD i 0) ≤ code lengths i by unfold code; omega)
  have hlo' : code lengths j*2^(58-lengths.getD j 0)+2^(58-lengths.getD j 0) ≤
      (codeStart lengths (58-lengths.getD j 0)+lengthCount lengths (lengths.getD j 0))*2^(58-lengths.getD j 0) := by
    simpa only [Nat.add_mul,Nat.one_mul] using hlo
  dsimp only [finish,start]
  omega

/-- Prefix extension can only move a dyadic block's start to the right. -/
theorem prefix_start_le (a b : List Bool) (hp : a <+: b) (hb : b.length ≤ 58) :
    Bits.value a*2^(58-a.length) ≤ Bits.value b*2^(58-b.length) := by
  obtain ⟨tail,rfl⟩ := hp
  have hexp : 58-a.length = tail.length+(58-(a.length+tail.length)) := by simp only [List.length_append] at hb; omega
  rw [List.length_append,Bits.value_append,hexp,Nat.pow_add,Nat.add_mul,Nat.mul_assoc]
  omega

theorem lengthCount_take_strict (lengths : List Nat) (i j : Nat) (hi : i < lengths.length) (hij : i < j) :
    lengthCount (lengths.take i) (lengths.getD i 0) < lengthCount (lengths.take j) (lengths.getD i 0) := by
  let extra := j-i-1
  have hj : j = i+(extra+1) := by omega
  conv_rhs =>
    rw [hj,List.take_add,List.drop_eq_getElem_cons hi,List.take_succ_cons,
      lengthCount_append,lengthCount_cons,← depth_eq_getElem lengths i hi]
  simp only [ite_true]
  omega

theorem code_lt_same_depth (lengths : List Nat) (i j : Nat) (hi : i < lengths.length)
    (hij : i < j) (hd : lengths.getD i 0 = lengths.getD j 0) : code lengths i < code lengths j := by
  have hr := lengthCount_take_strict lengths i j hi hij
  unfold code
  rw [← hd]
  omega

theorem no_prefix_distinct (lengths : List Nat) (hc : Complete lengths) (i j : Nat)
    (hi : i < lengths.length) (hj : j < lengths.length) (hne : i ≠ j)
    (hpi : 0 < lengths.getD i 0) (hpj : 0 < lengths.getD j 0) :
    ¬ Codebook.wordBits (canonicalWord lengths i) <+: Codebook.wordBits (canonicalWord lengths j) := by
  intro hp
  have hlen := hp.length_le
  rw [wordBits_length lengths hc i hi,wordBits_length lengths hc j hj] at hlen
  by_cases hd : lengths.getD i 0 = lengths.getD j 0
  · have he := hp.eq_of_length (by rw [wordBits_length lengths hc i hi,wordBits_length lengths hc j hj]; exact hd)
    have hv := congrArg Bits.value he
    rw [wordBits_value lengths hc i hi hpi,wordBits_value lengths hc j hj hpj] at hv
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · have hl := code_lt_same_depth lengths i j hi hij hd
      omega
    · have hl := code_lt_same_depth lengths j i hj hji hd.symm
      omega
  · have hlt : lengths.getD i 0 < lengths.getD j 0 := by omega
    have hbefore := deeper_before lengths hc i j hi hj hpi hlt
    have hscale := prefix_start_le _ _ hp (by rw [wordBits_length lengths hc j hj]; exact hc.1 _ (depth_mem lengths j hj))
    rw [wordBits_value lengths hc i hi hpi,wordBits_value lengths hc j hj hpj,
      wordBits_length lengths hc i hi,wordBits_length lengths hc j hj] at hscale
    have hpositive := Nat.two_pow_pos (58-lengths.getD j 0)
    dsimp only [finish,start] at hbefore
    omega

theorem words_compatible (lengths : List Nat) (hc : Complete lengths) (i j : Nat)
    (hi : i < lengths.length) (hj : j < lengths.length) (hne : i ≠ j)
    (hpi : 0 < lengths.getD i 0) (hpj : 0 < lengths.getD j 0) :
    Codebook.Compatible (Codebook.wordBits (canonicalWord lengths i)) (Codebook.wordBits (canonicalWord lengths j)) := by
  intro hp
  rcases hp with hp | hp
  · exact no_prefix_distinct lengths hc i j hi hj hne hpi hpj hp
  · exact no_prefix_distinct lengths hc j i hj hi hne.symm hpj hpi hp

theorem word_nonzero_depth (lengths : List Nat) (i : Nat) (hw : canonicalWord lengths i ≠ 0) :
    0 < lengths.getD i 0 := by
  by_contra hn
  have hz : lengths.getD i 0 = 0 := by omega
  apply hw
  simp only [canonicalWord,hz,ite_true]

theorem entries_length (lengths : List Nat) : (Codebook.entries lengths).length = lengths.length := by
  simp [Codebook.entries,canonicalTable]

theorem entries_getElem? (lengths : List Nat) (i : Nat) (hi : i < lengths.length) :
    (Codebook.entries lengths)[i]? = some (i,canonicalWord lengths i) := by
  simp only [Codebook.entries,canonicalTable,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_range hi,Option.map_some,Nat.zero_add]

theorem entries_getElem (lengths : List Nat) (i : Nat) (hi : i < (Codebook.entries lengths).length) :
    (Codebook.entries lengths)[i] = (i,canonicalWord lengths i) := by
  have hir : i < lengths.length := by simpa only [entries_length] using hi
  exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi] using entries_getElem? lengths i hir)

/-- A complete representable length profile gives prefix-free actual
canonical entries, including equal-depth symbol-index tie breaking. -/
theorem entries_prefixFree (lengths : List Nat) (hc : Complete lengths) :
    Codebook.PrefixFreeEntries (Codebook.entries lengths) := by
  unfold Codebook.PrefixFreeEntries
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [entries_getElem lengths i hi,entries_getElem lengths j hj]
  have hir : i < lengths.length := by simpa only [entries_length] using hi
  have hjr : j < lengths.length := by simpa only [entries_length] using hj
  by_cases hzi : canonicalWord lengths i = 0
  · exact Or.inl hzi
  · by_cases hzj : canonicalWord lengths j = 0
    · exact Or.inr (Or.inl hzj)
    · exact Or.inr (Or.inr (words_compatible lengths hc i j hir hjr (by omega)
        (word_nonzero_depth lengths i hzi) (word_nonzero_depth lengths j hzj)))

theorem entries_representable (lengths : List Nat) (hc : Complete lengths) :
    ∀ entry ∈ Codebook.entries lengths, entry.2 ≠ 0 → Codebook.Representable entry.2 := by
  intro entry hm hw
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  rw [entries_getElem lengths i hi] at he
  have hword : entry.2 = canonicalWord lengths i := congrArg Prod.snd he.symm
  rw [hword] at hw ⊢
  have hir : i < lengths.length := by simpa only [entries_length] using hi
  exact word_representable lengths hc i hir (word_nonzero_depth lengths i hw)

/-- Every complete bounded length profile passes the actual checked
canonical constructor. The resulting trie is derived, never an input oracle. -/
theorem build_exists (lengths : List Nat) (hc : Complete lengths) : ∃ trie, Codebook.build lengths = some trie :=
  Codebook.build_exists_of_prefixFree lengths (entries_representable lengths hc) (entries_prefixFree lengths hc)

/-- Every table accepted by the actual frequency heap/length emitter has a
valid descending canonical codebook, including sparse and trailing-zero tables. -/
theorem frequency_build_exists (frequencies result : List Nat) (he : Frequency.lengths frequencies = some result) :
    ∃ trie, Codebook.build result = some trie :=
  build_exists result ⟨Frequency.lengths_bound frequencies result he,Frequency.lengths_mass frequencies result he⟩

end Exr.Piz.Canonical
