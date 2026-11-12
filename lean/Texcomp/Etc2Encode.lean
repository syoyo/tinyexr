/-
  TinyEXR - ETC2 RGB / EAC alpha encoder and image driver (Lean model).

  Ports `tools/texcomp/src/texcomp_etc2.c` (`tc_encode_etc2_rgb` and its
  flat / individual / differential / planar candidates, with the C's strict-`<`
  selection order) and `tools/texcomp/src/texcomp_eac.c` (`tc_encode_eac_alpha`),
  plus the column-major image driver of `tc_etc2_compress_rgba8`.

  Blocks are `List (List Nat)` of 16 RGBA texels in ETC order (index = x*4 + y).
  Planar mode does its arithmetic in IEEE single precision (`Float32`), exactly
  as the C's `float` code does on x86-64 (no FMA contraction).

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

def u64Max : Nat := 2 ^ 64 - 1

def bswap32 (v : Nat) : Nat :=
  ((v &&& 0xff) <<< 24) ||| ((v &&& 0xff00) <<< 8) |||
  ((v &&& 0xff0000) >>> 8) ||| ((v &&& 0xff000000) >>> 24)

def bswap64 (v : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc ||| (((v >>> (8 * k)) &&& 0xff) <<< (8 * (7 - k)))) 0

/-- 8 little-endian bytes (`tc_wr_u64`). -/
def le64 (v : Nat) : List Nat := (List.range 8).map (fun k => (v >>> (8 * k)) % 256)

theorem le64_length (v : Nat) : (le64 v).length = 8 := by simp [le64]

/-- Channel `c` of texel `i`. -/
def etcPx (blk : List (List Nat)) (i c : Nat) : Nat := (blk.getD i []).getD c 0

def etcClamp255 (v : Int) : Int := max 0 (min 255 v)

/-- `tc_etc2_fix_byte_order`. -/
def etc2FixByteOrder (d : Nat) : Nat :=
  (d &&& 0xffffffff) ||| ((d &&& 0xff00000000000000) >>> 24) |||
  ((d &&& 0x000000ff00000000) <<< 24) ||| ((d &&& 0x00ff000000000000) >>> 8) |||
  ((d &&& 0x0000ff0000000000) <<< 8)

def etc1Mod : List (List Int) :=
  [[2, 8, -2, -8], [5, 17, -5, -17], [9, 29, -9, -29], [13, 42, -13, -42],
   [18, 60, -18, -60], [24, 80, -24, -80], [33, 106, -33, -106], [47, 183, -47, -183]]

def etc2PlanarFlags : List Nat :=
  [0x80800402, 0x80800402, 0x80800402, 0x80800402, 0x80800402, 0x80800402, 0x80800402, 0x8080e002,
   0x80800402, 0x80800402, 0x8080e002, 0x8080e002, 0x80800402, 0x8080e002, 0x8080e002, 0x8080e002,
   0x80000402, 0x80000402, 0x80000402, 0x80000402, 0x80000402, 0x80000402, 0x80000402, 0x8000e002,
   0x80000402, 0x80000402, 0x8000e002, 0x8000e002, 0x80000402, 0x8000e002, 0x8000e002, 0x8000e002,
   0x00800402, 0x00800402, 0x00800402, 0x00800402, 0x00800402, 0x00800402, 0x00800402, 0x0080e002,
   0x00800402, 0x00800402, 0x0080e002, 0x0080e002, 0x00800402, 0x0080e002, 0x0080e002, 0x0080e002,
   0x00000402, 0x00000402, 0x00000402, 0x00000402, 0x00000402, 0x00000402, 0x00000402, 0x0000e002,
   0x00000402, 0x00000402, 0x0000e002, 0x0000e002, 0x00000402, 0x0000e002, 0x0000e002, 0x0000e002]

/-- `tc_encode_etc2_rgb_flat`. -/
def etc2RgbFlat (blk : List (List Nat)) : Nat :=
  let avg (c : Nat) := ((List.range 16).foldl (fun a i => a + etcPx blk i c) 0 + 8) >>> 4
  0x02000000 ||| (((avg 2) &&& 0xf8) <<< 16) ||| (((avg 1) &&& 0xf8) <<< 8) ||| ((avg 0) &&& 0xf8)

/-- `tc_etc2_flat_error`. -/
def etc2FlatError (blk : List (List Nat)) (flat : Nat) : Nat :=
  let ext (v : Nat) := (v &&& 0xff) ||| ((v &&& 0xff) >>> 5)
  let r := ext flat
  let g := ext (flat >>> 8)
  let b := ext (flat >>> 16)
  (List.range 16).foldl (fun a i =>
    let dr : Int := (etcPx blk i 0 : Int) - r
    let dg : Int := (etcPx blk i 1 : Int) - g
    let db : Int := (etcPx blk i 2 : Int) - b
    a + (dr * dr + dg * dg + db * db).toNat) 0

def etc1Quant4 (v : Nat) : Nat := (v * 15 + 127) / 255
def etc1Expand4 (v : Nat) : Nat := (v <<< 4) ||| v
def etc1Quant5 (v : Nat) : Nat := (v * 31 + 127) / 255
def etc1Expand5 (v : Nat) : Nat := (v <<< 3) ||| (v >>> 2)

/-- `tc_etc1_subset_for_split`. -/
def etc1Subset (split i : Nat) : Nat :=
  let x := i % 4
  let y := i / 4
  if split == 0 then (if y < 2 then 1 else 0) else (if x < 2 then 1 else 0)

/-- Per-subset, per-channel rounded average. -/
def etc1SubsetAvg (blk : List (List Nat)) (split s c : Nat) : Nat :=
  let (sum, cnt) := (List.range 16).foldl (fun (a : Nat × Nat) i =>
    if etc1Subset split i == s then (a.1 + etcPx blk i c, a.2 + 1) else a) (0, 0)
  (sum + cnt / 2) / cnt

/-- The table/selector search shared by the individual and differential
  encoders: best of the 8 modifier tables for subset `s` (strict `<`, tables
  in order; per-texel best selector with strict `<`). Returns
  `(error, table, selectors)`; selectors of other-subset texels are 0. -/
def etc1FitSubset (blk : List (List Nat)) (split s : Nat) (base : List Nat) :
    Nat × Nat × List Nat :=
  let tabFit (t : Nat) : Nat × List Nat :=
    (List.range 16).foldl (fun (acc : Nat × List Nat) i =>
      if etc1Subset split i != s then (acc.1, acc.2 ++ [0])
      else
        let best := (List.range 4).foldl (fun (b : Nat × Nat) c =>
          let m : Int := (etc1Mod.getD t []).getD c 0
          let e := ((List.range 3).foldl (fun (a : Int) ch =>
            let rec_ := etcClamp255 ((base.getD ch 0 : Nat) + m)
            let d : Int := (etcPx blk i ch : Int) - rec_
            a + d * d) 0).toNat
          if e < b.1 then (e, c) else b) (u64Max, 0)
        (acc.1 + best.1, acc.2 ++ [best.2])) (0, [])
  (List.range 8).foldl (fun (b : Nat × Nat × List Nat) t =>
    let (te, ts) := tabFit t
    if te < b.1 then (te, t, ts) else b) (u64Max, 0, (List.range 16).map (fun _ => 0))

/-- Selector bit packing shared by individual / differential:
  `d |= (sv & 1) << (i+32); d |= (sv & 2) << (i+47)`. -/
def etc1SelBits (sel : List Nat) : Nat :=
  (List.range 16).foldl (fun acc i =>
    let sv := sel.getD i 0
    acc ||| ((sv &&& 1) <<< (i + 32)) ||| ((sv &&& 2) <<< (i + 47))) 0

/-- Merge the two subsets' fits into the 16 selectors. -/
def etc1MergeSel (split : Nat) (f0 f1 : Nat × Nat × List Nat) : List Nat :=
  (List.range 16).map (fun i =>
    if etc1Subset split i == 0 then f0.2.2.getD i 0 else f1.2.2.getD i 0)

/-- One split of `tc_encode_etc1_individual`: `(bits, error)`. -/
def etc1IndividualSplit (blk : List (List Nat)) (split : Nat) : Nat × Nat :=
  let b (s c : Nat) := etc1Expand4 (etc1Quant4 (etc1SubsetAvg blk split s c))
  let base (s : Nat) : List Nat := [b s 0, b s 1, b s 2]
  let f0 := etc1FitSubset blk split 0 (base 0)
  let f1 := etc1FitSubset blk split 1 (base 1)
  let sel := etc1MergeSel split f0 f1
  let d : Nat :=
    (split <<< 24) ||| ((b 0 0 >>> 4) <<< 0) ||| ((b 1 0 >>> 4) <<< 4) |||
    ((b 0 1 >>> 4) <<< 8) ||| ((b 1 1 >>> 4) <<< 12) ||| ((b 0 2 >>> 4) <<< 16) |||
    ((b 1 2 >>> 4) <<< 20) ||| (f0.2.1 <<< 26) ||| (f1.2.1 <<< 29) ||| etc1SelBits sel
  (etc2FixByteOrder d, f0.1 + f1.1)

/-- `tc_encode_etc1_individual`: `(bits, error)`, strict `<` over splits. -/
def etc1Individual (blk : List (List Nat)) : Nat × Nat :=
  [0, 1].foldl (fun (acc : Nat × Nat) split =>
    let r := etc1IndividualSplit blk split
    if r.2 < acc.2 then r else acc) (0, u64Max)

/-- One split of `tc_encode_etc1_differential`; `none` when a channel delta
  falls outside [-4, 3] (the C then abandons the whole encode). -/
def etc1DifferentialSplit (blk : List (List Nat)) (split : Nat) : Option (Nat × Nat) :=
  let q (s c : Nat) := etc1Quant5 (etc1SubsetAvg blk split s c)
  let diff (c : Nat) : Int := (q 0 c : Int) - (q 1 c : Int)
  if (List.range 3).any (fun c => diff c < -4 || diff c > 3) then none
  else
    let base (s : Nat) : List Nat := [etc1Expand5 (q s 0), etc1Expand5 (q s 1), etc1Expand5 (q s 2)]
    let f0 := etc1FitSubset blk split 0 (base 0)
    let f1 := etc1FitSubset blk split 1 (base 1)
    let sel := etc1MergeSel split f0 f1
    let d3 (c : Nat) : Nat := (diff c % 8).toNat
    let d : Nat :=
      (split <<< 24) ||| (1 <<< 25) ||| (d3 0) ||| (q 1 0 <<< 3) ||| (d3 1 <<< 8) |||
      (q 1 1 <<< 11) ||| (d3 2 <<< 16) ||| (q 1 2 <<< 19) ||| (f0.2.1 <<< 26) |||
      (f1.2.1 <<< 29) ||| etc1SelBits sel
    some (etc2FixByteOrder d, f0.1 + f1.1)

/-- `tc_encode_etc1_differential`: one out-of-range split makes the whole call
  return `(0, UINT64_MAX)`. -/
def etc1Differential (blk : List (List Nat)) : Nat × Nat :=
  let r := [0, 1].foldl (fun (acc : Option (Nat × Nat)) split =>
    match acc with
    | none => none
    | some a =>
      match etc1DifferentialSplit blk split with
      | none => none
      | some r => if r.2 < a.2 then some r else some a) (some (0, u64Max))
  r.getD (0, u64Max)

/-- `tc_etc2_convert6`. -/
def etc2Convert6 (f : Float32) : Nat :=
  let t : Int := f.toInt32.toInt
  let i : Int := (max 0 (min 1023 t) - 15) >>> 1
  (((i + 11 - ((i + 11) >>> 7) - ((i + 4) >>> 7)) >>> 3) % 256).toNat

/-- `tc_etc2_convert7`. -/
def etc2Convert7 (f : Float32) : Nat :=
  let t : Int := f.toInt32.toInt
  let i : Int := (max 0 (min 1023 t) - 15) >>> 1
  (((i + 9 - ((i + 9) >>> 8) - ((i + 6) >>> 8)) >>> 2) % 256).toNat

def etc2Expand6 (v : Nat) : Nat := ((v >>> 4) ||| (v <<< 2)) % 256
def etc2Expand7 (v : Nat) : Nat := ((v >>> 6) ||| (v <<< 1)) % 256

/-- `tc_encode_etc2_rgb_planar`: `(bits, error)`. -/
def etc2RgbPlanar (blk : List (List Nat)) : Nat × Nat :=
  let sum (c : Nat) : Int := (List.range 16).foldl (fun a i => a + (etcPx blk i c : Int)) 0
  let scaling : List Int := [-255, -85, 85, 255]
  let dif (c i : Nat) : Int := (etcPx blk i c : Int) * 16 - sum c
  let dxz (c : Nat) : Int :=
    (List.range 16).foldl (fun a i => a + dif c i * scaling.getD (i / 4) 0) 0
  let dyz (c : Nat) : Int :=
    (List.range 16).foldl (fun a i => a + dif c i * scaling.getD (i % 4) 0) 0
  let scale : Float32 :=
    (-4.0 : Float32) / (((255.0 : Float32) * 255.0 * 8.0 + 85.0 * 85.0 * 8.0) * 16.0)
  let a (c : Nat) : Float32 := Float32.ofInt (dxz c) * scale
  let b (c : Nat) : Float32 := Float32.ofInt (dyz c) * scale
  let d (c : Nat) : Float32 := Float32.ofInt (sum c) * 0.25
  let conv (c : Nat) (f : Float32) : Nat := if c == 1 then etc2Convert7 f else etc2Convert6 f
  let co (c : Nat) := conv c (a c * 255.0 + b c * 255.0 + d c)
  let ch (c : Nat) := conv c (a c * (-425.0) + b c * 255.0 + d c)
  let cv (c : Nat) := conv c (a c * 255.0 + b c * (-425.0) + d c)
  let ex (c v : Nat) : Int := (if c == 1 then etc2Expand7 v else etc2Expand6 v : Nat)
  let o (c : Nat) : Int := ex c (co c)
  let h (c : Nat) : Int := ex c (ch c) - o c
  let v (c : Nat) : Int := ex c (cv c) - o c
  let o2 (c : Nat) : Int := o c * 4 + 2
  let err : Nat := (List.range 16).foldl (fun acc i =>
    let x : Int := (i / 4 : Nat)
    let y : Int := (i % 4 : Nat)
    let e (c : Nat) : Int :=
      (etcPx blk i c : Int) - etcClamp255 ((h c * x + v c * y + o2 c) >>> 2)
    acc + (e 0 * e 0 + e 1 * e 1 + e 2 * e 2).toNat) 0
  let co_r := co 0
  let co_g := co 1
  let co_b := co 2
  let ch_r := ch 0
  let rgbv := cv 2 ||| (cv 1 <<< 6) ||| (cv 0 <<< 13)
  let rgbh := ch 2 ||| (ch 1 <<< 6) ||| (ch 0 <<< 13)
  let hi := (rgbv ||| ((rgbh &&& 0x1fff) <<< 19)) % 2 ^ 32
  let lo0 := (ch_r &&& 1) ||| 2 ||| ((ch_r <<< 1) &&& 0x7c)
  let lo1 := lo0 ||| ((co_b &&& 0x07) <<< 7) ||| ((co_b &&& 0x18) <<< 8) ||| ((co_b &&& 0x20) <<< 11)
  let lo2 := lo1 ||| ((co_g &&& 0x3f) <<< 17) ||| ((co_g &&& 0x40) <<< 18)
  let lo3 := lo2 ||| (co_r <<< 25)
  let idx := (co_r &&& 0x20) ||| ((co_g &&& 0x20) >>> 1) ||| ((co_b &&& 0x1e) >>> 1)
  let lo := (lo3 ||| etc2PlanarFlags.getD idx 0) % 2 ^ 32
  (bswap32 lo ||| (bswap32 hi <<< 32), err)

/-- `tc_encode_etc2_rgb`: flat, then individual / differential / planar each
  replacing the best only on a strictly smaller error. -/
def etc2RgbEncode (blk : List (List Nat)) : Nat :=
  let flat := etc2RgbFlat blk
  let s0 : Nat × Nat := (flat, etc2FlatError blk flat)
  let s1 := let r := etc1Individual blk; if r.2 < s0.2 then r else s0
  let s2 := let r := etc1Differential blk; if r.2 < s1.2 then r else s1
  let s3 := let r := etc2RgbPlanar blk; if r.2 < s2.2 then r else s2
  s3.1

def eacAlphaTab : List (List Int) :=
  [[-3, -6, -9, -15, 2, 5, 8, 14], [-3, -7, -10, -13, 2, 6, 9, 12],
   [-2, -5, -8, -13, 1, 4, 7, 12], [-2, -4, -6, -13, 1, 3, 5, 12],
   [-3, -6, -8, -12, 2, 5, 7, 11], [-3, -7, -9, -11, 2, 6, 8, 10],
   [-4, -7, -8, -11, 3, 6, 7, 10], [-3, -5, -8, -11, 2, 4, 7, 10],
   [-2, -6, -8, -10, 1, 5, 7, 9], [-2, -5, -8, -10, 1, 4, 7, 9],
   [-2, -4, -8, -10, 1, 3, 7, 9], [-2, -5, -7, -10, 1, 4, 6, 9],
   [-3, -4, -7, -10, 2, 3, 6, 9], [-1, -2, -3, -10, 0, 1, 2, 9],
   [-4, -6, -8, -9, 3, 5, 7, 8], [-3, -5, -7, -9, 2, 4, 6, 8]]

def eacAlphaRange : List Nat :=
  [0x100FF / 30, 0x100FF / 26, 0x100FF / 26, 0x100FF / 26, 0x100FF / 24,
   0x100FF / 22, 0x100FF / 22, 0x100FF / 22, 0x100FF / 20, 0x100FF / 20,
   0x100FF / 20, 0x100FF / 20, 0x100FF / 20, 0x100FF / 20, 0x100FF / 18, 0x100FF / 18]

/-- `tc_encode_eac_alpha`. A constant block returns just the value (as the C). -/
def eacAlphaEncode (alpha : List Nat) : Nat :=
  let minv := (List.range 16).foldl (fun a i => min a (alpha.getD i 0)) 255
  let maxv := (List.range 16).foldl (fun a i => max a (alpha.getD i 0)) 0
  if minv == maxv then minv
  else
    let mid := (minv + maxv) >>> 1
    let range := maxv - minv
    let tabFit (tab : Nat) : Nat × Nat × List Nat :=
      let mul := ((range * eacAlphaRange.getD tab 0) >>> 16) + 1
      let (err, sel) := (List.range 16).foldl (fun (acc : Nat × List Nat) i =>
        let best := (List.range 8).foldl (fun (b : Nat × Nat) j =>
          let rec_ := etcClamp255 ((mid : Int) + (eacAlphaTab.getD tab []).getD j 0 * (mul : Int))
          let diff : Int := (alpha.getD i 0 : Int) - rec_
          let e := (diff * diff).toNat
          if e < b.1 then (e, j) else b) (2 ^ 31 - 1, 0)
        (acc.1 + best.1, acc.2 ++ [best.2])) (0, [])
      (err, mul, sel)
    let (_, bestTab, bestMul, bestSel) := (List.range 16).foldl
      (fun (acc : Nat × Nat × Nat × List Nat) tab =>
        let (e, mul, sel) := tabFit tab
        if e < acc.1 then (e, tab, mul, sel) else acc)
      (2 ^ 31 - 1, 0, 0, (List.range 16).map (fun _ => 0))
    let d := (mid <<< 56) ||| ((bestMul &&& 15) <<< 52) ||| ((bestTab &&& 15) <<< 48) |||
      (List.range 16).foldl (fun acc i => acc ||| (bestSel.getD i 0 <<< (45 - 3 * i))) 0
    bswap64 d

/-- `tc_etc2_compress_rgba8`: edge-clamped, **column-major** (index = x*4 + y)
  4x4 gather; per block an optional 8-byte EAC alpha block (little-endian)
  followed by the 8-byte RGB block. -/
def etc2CompressRgba8 (pix : List (List Nat)) (w h : Nat) (alpha : Bool) : List Nat :=
  let bw := (w + 3) / 4
  let bh := (h + 3) / 4
  (List.range (bh * bw)).foldl (fun (acc : List Nat) bi =>
    let bx := (bi % bw) * 4
    let by0 := (bi / bw) * 4
    let blk : List (List Nat) := (List.range 16).map (fun k =>
      let x := min (bx + k / 4) (w - 1)
      let y := min (by0 + k % 4) (h - 1)
      pix.getD (y * w + x) [0, 0, 0, 0])
    let al := blk.map (fun p => p.getD 3 0)
    acc ++ (if alpha then le64 (eacAlphaEncode al) else []) ++ le64 (etc2RgbEncode blk)) []

end Texcomp
