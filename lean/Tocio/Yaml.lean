/-
  TinyEXR - Lean 4 formalization of the tocio YAML subset.

  First slice: a minimal YAML value type (null, bool, int, float, string,
  sequence, mapping) and a total parser skeleton. Full parsing, indentation
  handling, and round-trip come in later slices.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Tocio

/-- A minimal YAML value. -/
inductive YamlValue where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | seq (xs : List YamlValue)
  | map (kvs : List (String × YamlValue))
  deriving Repr, Inhabited

/-- Look up a key in a YAML mapping (first match). -/
def YamlValue.lookup (v : YamlValue) (key : String) : Option YamlValue :=
  match v with
  | .map kvs => (kvs.find? (fun p => p.1 = key)).map (·.2)
  | _ => none

/-- Number of entries in a sequence. -/
def YamlValue.seqLen (v : YamlValue) : Nat :=
  match v with
  | .seq xs => xs.length
  | _ => 0

/-- Number of keys in a mapping. -/
def YamlValue.mapSize (v : YamlValue) : Nat :=
  match v with
  | .map kvs => kvs.length
  | _ => 0

theorem YamlValue.seqLen_nonneg (v : YamlValue) : v.seqLen ≥ 0 := Nat.zero_le _

end Tocio