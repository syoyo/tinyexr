/-
  TinyEXR - Lean 4 formalization of the BC1 colour-block encoder.

  Ports `tc_encode_bc1_color_block` in `tools/texcomp/src/texcomp_bc1.c`:
  RGB bounding-box endpoints refined by two least-squares passes over the
  assigned palette indices, the 4-colour ordering rule (`c0 >= c1`), and
  the single-colour punch-through guard. Endpoint math uses `Float`
  (C `double`), palette/index math uses `Int`/`Nat` (C `int`), and the
  block is emitted as the 8 bytes the C encoder writes.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- C `(int)x` cast (truncation toward zero). -/
def f2i (x : Float) : Int := (Float.toInt32 x).toInt

/-- Clamp an `Int` into `[lo, hi]`. -/
def clampI (x lo hi : Int) : Int := if x < lo then lo else if x > hi then hi else x

/-- Clamp a `Float` into `[lo, hi]`. -/
def clampF (x lo hi : Float) : Float := if x < lo then lo else if x > hi then hi else x

/-- RGB888 as integers (C `int[3]`). -/
structure RgbI where
  (r g b : Int)
  deriving Repr, DecidableEq

/-- RGB as doubles (C `double[3]`). -/
structure RgbF where
  (r g b : Float)
  deriving Repr

/-- `tc_rgb565_pack`: RGB888 → RGB565 with per-channel clamping. -/
def encRgb565Pack (r g b : Int) : Nat :=
  let r := (clampI r 0 255).toNat
  let g := (clampI g 0 255).toNat
  let b := (clampI b 0 255).toNat
  ((r / 8) <<< 11) ||| ((g / 4) <<< 5) ||| (b / 8)

/-- `tc_rgb565_unpack`: RGB565 → RGB888 (bit replication). -/
def encRgb565Unpack (c : Nat) : RgbI :=
  let r := (c >>> 11) &&& 0x1f
  let g := (c >>> 5) &&& 0x3f
  let b := c &&& 0x1f
  ⟨Int.ofNat ((r <<< 3) ||| (r >>> 2)),
   Int.ofNat ((g <<< 2) ||| (g >>> 4)),
   Int.ofNat ((b <<< 3) ||| (b >>> 2))⟩

/-- The 4-entry interpolation palette for the two endpoints. -/
def encBc1Palette (p0 p1 : RgbI) : List RgbI :=
  let third := fun (a b : Int) => (2 * a + b + 1) / 3
  let twothird := fun (a b : Int) => (a + 2 * b + 1) / 3
  [p0, p1,
   ⟨third p0.r p1.r, third p0.g p1.g, third p0.b p1.b⟩,
   ⟨twothird p0.r p1.r, twothird p0.g p1.g, twothird p0.b p1.b⟩]

/-- Squared RGB distance (C computes it in `uint32_t`; the values stay far
  below overflow, so a `Nat` sum is identical). -/
def pxDist (a b : RgbI) : Nat :=
  let e0 := a.r - b.r
  let e1 := a.g - b.g
  let e2 := a.b - b.b
  (e0 * e0 + e1 * e1 + e2 * e2).toNat

/-- Nearest palette index over the first `jmax` entries (ties keep the
  earliest index, as C's strict `<` comparison does). Returns
  `(index, distance)`. -/
def nearestIdx (pal : List RgbI) (p : RgbI) (jmax : Nat) : Nat × Nat :=
  (List.range jmax).foldl (fun (acc : Nat × Nat) j =>
    let d := pxDist p (pal.getD j ⟨0, 0, 0⟩)
    if d < acc.2 then (j, d) else acc) (0, 0xffffffff)

/-- Accumulated normal equations for one least-squares pass. -/
structure Lsq where
  (a00 a01 a11 : Float)
  (b0 b1 : RgbF)
  deriving Repr

/-- One encoder pass: quantise the current endpoints, assign nearest
  indices, and fold the LSQ sums. Returns the indices and the sums. -/
def bc1Pass (px : List (Nat × Nat × Nat × Nat)) (e0 e1 : RgbF) :
    List Nat × Lsq :=
  let af : List Float := [1.0, 0.0, 2.0 / 3.0, 1.0 / 3.0]
  let bf : List Float := [0.0, 1.0, 1.0 / 3.0, 2.0 / 3.0]
  let c0 := encRgb565Pack (f2i (e0.r + 0.5)) (f2i (e0.g + 0.5)) (f2i (e0.b + 0.5))
  let c1 := encRgb565Pack (f2i (e1.r + 0.5)) (f2i (e1.g + 0.5)) (f2i (e1.b + 0.5))
  let pal := encBc1Palette (encRgb565Unpack c0) (encRgb565Unpack c1)
  let rec go (i : Nat) (idxAcc : List Nat) (acc : Lsq) : List Nat × Lsq :=
    if i ≥ 16 then (idxAcc, acc)
    else
      let p := px.getD i (0, 0, 0, 0)
      let q : RgbI := ⟨Int.ofNat p.1, Int.ofNat p.2.1, Int.ofNat p.2.2.1⟩
      let best := (nearestIdx pal q 4).1
      let a := af.getD best 0.0
      let b := bf.getD best 0.0
      let px0 := Float.ofNat p.1
      let px1 := Float.ofNat p.2.1
      let px2 := Float.ofNat p.2.2.1
      go (i + 1) (idxAcc ++ [best])
        { a00 := acc.a00 + a * a
          a01 := acc.a01 + a * b
          a11 := acc.a11 + b * b
          b0 := ⟨acc.b0.r + a * px0, acc.b0.g + a * px1, acc.b0.b + a * px2⟩
          b1 := ⟨acc.b1.r + b * px0, acc.b1.g + b * px1, acc.b1.b + b * px2⟩ }
  go 0 [] { a00 := 0.0, a01 := 0.0, a11 := 0.0, b0 := ⟨0.0, 0.0, 0.0⟩, b1 := ⟨0.0, 0.0, 0.0⟩ }

/-- One LSQ re-fit of the endpoints (C's `if (det != 0)` branch, clamped
  to `[0,255]`). -/
def bc1Refit (e0 e1 : RgbF) (s : Lsq) : RgbF × RgbF :=
  let det := s.a00 * s.a11 - s.a01 * s.a01
  if det == 0.0 then (e0, e1)
  else
    let inv := 1.0 / det
    let n0 := fun (b0 b1 : Float) => clampF ((s.a11 * b0 - s.a01 * b1) * inv) 0.0 255.0
    let n1 := fun (b0 b1 : Float) => clampF ((s.a00 * b1 - s.a01 * b0) * inv) 0.0 255.0
    (⟨n0 s.b0.r s.b1.r, n0 s.b0.g s.b1.g, n0 s.b0.b s.b1.b⟩,
     ⟨n1 s.b0.r s.b1.r, n1 s.b0.g s.b1.g, n1 s.b0.b s.b1.b⟩)

/-- `tc_encode_bc1_color_block`: encode the RGB channels of a 4x4 block
  into an 8-byte DXT1 colour block. `dxt1` selects standalone-BC1
  behaviour (single-colour blocks must avoid the punch-through index). -/
def encodeBc1ColorBlock (px : List (Nat × Nat × Nat × Nat)) (dxt1 : Bool) :
    List Nat :=
  -- RGB bounding box (min, max) of the 16 texels.
  let bb := (List.range 16).foldl (fun (acc : RgbI × RgbI) i =>
    let p := px.getD i (0, 0, 0, 0)
    let c : RgbI := ⟨Int.ofNat p.1, Int.ofNat p.2.1, Int.ofNat p.2.2.1⟩
    (⟨min acc.1.r c.r, min acc.1.g c.g, min acc.1.b c.b⟩,
     ⟨max acc.2.r c.r, max acc.2.g c.g, max acc.2.b c.b⟩))
    (⟨255, 255, 255⟩, ⟨0, 0, 0⟩)
  -- e0 starts at the box max, e1 at the box min, then two refit passes.
  let step := fun (e : RgbF × RgbF) _ =>
    let (_, s) := bc1Pass px e.1 e.2
    bc1Refit e.1 e.2 s
  let init : RgbF × RgbF :=
    (⟨Float.ofInt bb.2.r, Float.ofInt bb.2.g, Float.ofInt bb.2.b⟩,
     ⟨Float.ofInt bb.1.r, Float.ofInt bb.1.g, Float.ofInt bb.1.b⟩)
  let refined := (List.range 2).foldl step init
  let c0a := encRgb565Pack (f2i (refined.1.r + 0.5)) (f2i (refined.1.g + 0.5))
    (f2i (refined.1.b + 0.5))
  let c1a := encRgb565Pack (f2i (refined.2.r + 0.5)) (f2i (refined.2.g + 0.5))
    (f2i (refined.2.b + 0.5))
  -- 4-colour interpolation needs colour0 > colour1.
  let (c0, c1) := if c0a < c1a then (c1a, c0a) else (c0a, c1a)
  let pal := encBc1Palette (encRgb565Unpack c0) (encRgb565Unpack c1)
  let jmax := if dxt1 && c0 == c1 then 3 else 4
  let idx := (List.range 16).map (fun i =>
    let p := px.getD i (0, 0, 0, 0)
    (nearestIdx pal ⟨Int.ofNat p.1, Int.ofNat p.2.1, Int.ofNat p.2.2.1⟩ jmax).1)
  let pack4 := fun (a b c d : Nat) =>
    idx.getD a 0 ||| (idx.getD b 0 <<< 2) ||| (idx.getD c 0 <<< 4) ||| (idx.getD d 0 <<< 6)
  [c0 &&& 0xff, c0 >>> 8, c1 &&& 0xff, c1 >>> 8,
   pack4 0 1 2 3, pack4 4 5 6 7, pack4 8 9 10 11, pack4 12 13 14 15]

/-- Every BC1 colour block is exactly 8 bytes. -/
theorem encodeBc1ColorBlock_length (px : List (Nat × Nat × Nat × Nat)) (dxt1 : Bool) :
    (encodeBc1ColorBlock px dxt1).length = 8 := by
  simp [encodeBc1ColorBlock]
  try omega

end Texcomp
