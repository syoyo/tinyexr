/-
  TinyEXR - Lean 4 formalization of the BC4/BC5 alpha-block encoder.

  Ports `tc_encode_bc4_block` and `tc_encode_bc4_block_snorm` in
  `tools/texcomp/src/texcomp_bc5.c` (also used for the BC3 alpha
  sub-block), plus the UNORM↔SNORM byte conversions
  (`tc_unorm8_to_snorm8`, `tc_snorm8_to_unorm8`). The 8-value palette
  is `maxv, minv,` then six interpolants, and the 16 3-bit indices are
  packed LSB-first into 48 bits.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- C `(int)x` cast for a `Float32` (truncation toward zero). -/
def f32ToInt (x : Float32) : Int := (Float32.toInt32 x).toInt

/-- `tc_unorm8_to_snorm8`: UNORM8 → int8 in `[-127, 127]`. -/
def unorm8ToSnorm8 (u : Nat) : Int :=
  let x : Float32 := 2.0 * (Float32.ofNat u / 255.0) - 1.0
  let v := f32ToInt (x * 127.0 + (if x ≥ 0.0 then 0.5 else -0.5))
  if v < -127 then -127 else if v > 127 then 127 else v

/-- `tc_snorm8_to_unorm8`: int8 → UNORM8. -/
def snorm8ToUnorm8 (s : Int) : Nat :=
  let x : Float32 := Float32.ofInt (if s < -127 then -127 else s) / 127.0
  let v := f32ToInt ((x + 1.0) * 0.5 * 255.0 + 0.5)
  if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- Truncating integer division (C semantics for the signed encoder). -/
def tdiv (a b : Int) : Int := Int.tdiv a b

/-- `tc_encode_bc4_block`: 16 UNORM8 samples → an 8-byte BC4 block. -/
def encodeBc4Block (v : List Nat) : List Nat :=
  let minv := (List.range 16).foldl (fun acc i => min acc (v.getD i 255)) 255
  let maxv := (List.range 16).foldl (fun acc i => max acc (v.getD i 0)) 0
  let palette : List Nat :=
    maxv :: minv ::
      ((List.range 6).map (fun k =>
        let i := k + 1
        ((7 - i) * maxv + i * minv + 3) / 7))
  let bits := (List.range 16).foldl (fun (acc : Nat) i =>
    let p := v.getD i 0
    let d := fun (j : Nat) => let q := palette.getD j 0
      let e := (Int.ofNat p) - (Int.ofNat q)
      (e * e).toNat
    let best := (List.range 8).foldl (fun (bacc : Nat × Nat) j =>
      let e := d j
      if e < bacc.2 then (j, e) else bacc) (0, 0xffffffff)
    acc ||| (best.1 <<< (3 * i))) 0
  [maxv, minv,
   bits &&& 0xff, (bits >>> 8) &&& 0xff, (bits >>> 16) &&& 0xff,
   (bits >>> 24) &&& 0xff, (bits >>> 32) &&& 0xff, (bits >>> 40) &&& 0xff]

/-- `tc_encode_bc4_block_snorm`: 16 signed samples → an 8-byte block
  (endpoints stored as int8, so `max > min` selects the 8-value palette). -/
def encodeBc4BlockSnorm (v : List Int) : List Nat :=
  let minv := (List.range 16).foldl (fun acc i => min acc (v.getD i 127)) 127
  let maxv := (List.range 16).foldl (fun acc i => max acc (v.getD i (-127))) (-127)
  let palette : List Int :=
    maxv :: minv ::
      ((List.range 6).map (fun k =>
        let i : Int := Int.ofNat (k + 1)
        tdiv ((7 - i) * maxv + i * minv) 7))
  let bits := (List.range 16).foldl (fun (acc : Nat) i =>
    let p := v.getD i 0
    let best := (List.range 8).foldl (fun (bacc : Nat × Nat) j =>
      let q := palette.getD j 0
      let e := p - q
      let err := (e * e).toNat
      if err < bacc.2 then (j, err) else bacc) (0, 0xffffffff)
    acc ||| (best.1 <<< (3 * i))) 0
  [(Int32.ofInt maxv &&& (0xff : Int32)).toUInt32.toNat &&& 0xff,
   (Int32.ofInt minv &&& (0xff : Int32)).toUInt32.toNat &&& 0xff,
   bits &&& 0xff, (bits >>> 8) &&& 0xff, (bits >>> 16) &&& 0xff,
   (bits >>> 24) &&& 0xff, (bits >>> 32) &&& 0xff, (bits >>> 40) &&& 0xff]

/-- `tc_encode_bc5_block` (UNORM): two 16-channel planes → 16 bytes. -/
def encodeBc5Block (r g : List Nat) : List Nat :=
  encodeBc4Block r ++ encodeBc4Block g

/-- `tc_encode_bc5_block_snorm`: signed planes, converted from UNORM8
  inputs the same way the C wrapper does. -/
def encodeBc5BlockSnorm (r g : List Nat) : List Nat :=
  encodeBc4BlockSnorm ((List.range 16).map (fun i => unorm8ToSnorm8 (r.getD i 0)))
    ++ encodeBc4BlockSnorm ((List.range 16).map (fun i => unorm8ToSnorm8 (g.getD i 0)))

/-- A BC4 block is exactly 8 bytes. -/
theorem encodeBc4Block_length (v : List Nat) : (encodeBc4Block v).length = 8 := by
  simp [encodeBc4Block]

/-- A signed BC4 block is exactly 8 bytes. -/
theorem encodeBc4BlockSnorm_length (v : List Int) : (encodeBc4BlockSnorm v).length = 8 := by
  simp [encodeBc4BlockSnorm]

/-- A BC5 block is exactly 16 bytes (two BC4 planes). -/
theorem encodeBc5Block_length (r g : List Nat) : (encodeBc5Block r g).length = 16 := by
  simp [encodeBc5Block, encodeBc4Block_length]

/-- A signed BC5 block is exactly 16 bytes. -/
theorem encodeBc5BlockSnorm_length (r g : List Nat) :
    (encodeBc5BlockSnorm r g).length = 16 := by
  simp [encodeBc5BlockSnorm, encodeBc4BlockSnorm_length]

end Texcomp
