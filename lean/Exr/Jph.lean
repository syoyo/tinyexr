/-
  TinyEXR - wrapper-level Lean model of the HTJ2K/JPH codestream.

  Scope (matches `AGENTS.md`): the JPEG 2000 marker sequence, SIZ/COD/CAP/QCD
  profile geometry and the tile/codeblock descriptors' *bounds*. The HT
  entropy decoder (VLC tag trees, SPP/MRP, codeblock decode) is deliberately
  NOT modelled. This is a structural model validated against the real JPH
  fixtures by `make jph-diff`; it is not a proof of `src/exr_jph.c`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Exr

set_option linter.unusedVariables false

/-- JPEG 2000 markers used by the OpenEXR HTJ2K wrapper. -/
inductive JphMark where
  | soc | siz | cap | cod | qcd | qcc | nlt | sot | sod | eoc
  | plt | com | DFS | ads | atk | poc | other (code : Nat)
  deriving Repr, DecidableEq

def markCode (m : JphMark) : Nat :=
  match m with
  | .soc => 0xff4f | .cap => 0xff50 | .siz => 0xff51 | .cod => 0xff52
  | .qcd => 0xff5c | .qcc => 0xff5d | .nlt => 0xff76
  | .sot => 0xff90 | .sod => 0xff93 | .eoc => 0xffd9
  | .plt => 0xff58 | .com => 0xff64 | .DFS => 0xff85
  | .ads => 0xff88 | .atk => 0xff89 | .poc => 0xff5f
  | .other c => c

def markOfCode (c : Nat) : JphMark :=
  if c = 0xff4f then .soc else if c = 0xff50 then .cap
  else if c = 0xff51 then .siz else if c = 0xff52 then .cod
  else if c = 0xff5c then .qcd else if c = 0xff5d then .qcc
  else if c = 0xff76 then .nlt else if c = 0xff90 then .sot
  else if c = 0xff93 then .sod else if c = 0xffd9 then .eoc
  else if c = 0xff58 then .plt else if c = 0xff64 then .com
  else if c = 0xff85 then .DFS else if c = 0xff88 then .ads
  else if c = 0xff89 then .atk else if c = 0xff5f then .poc
  else .other c

/-- `jph_next_marker`: skip 0xff runs and byte-stuffed 0xff00. -/
def nextMark (data : List UInt8) (pos : Nat) : Option (JphMark × Nat) :=
  let rec go (p : Nat) : Option (Nat × Nat) :=
    if h : p < data.length then
      if data.get ⟨p, h⟩ == 0xff then
        let rec skipFf (q : Nat) : Option (Nat × Nat) :=
          if h2 : q < data.length then
            if data.get ⟨q, h2⟩ == 0xff then skipFf (q + 1)
            else if data.get ⟨q, h2⟩ == 0 then go (q + 1)
            else some ((0xff00 : Nat) + (data.get ⟨q, h2⟩).toNat, q + 1)
          else none
        skipFf (p + 1)
      else go (p + 1)
    else none
  match go pos with
  | some (c, q) => some (markOfCode c, q)
  | none => none

def be16 (data : List UInt8) (p : Nat) : Nat :=
  let a := (data.getD p 0).toNat
  let b := (data.getD (p + 1) 0).toNat
  (a <<< 8) ||| b

def be32 (data : List UInt8) (p : Nat) : Nat :=
  (be16 data p <<< 16) ||| be16 data (p + 2)

/-- SIZ fields (all as natural numbers; the C side validates 32-bit ranges). -/
structure SizInfo where
  rsiz : Nat
  xsiz : Nat
  ysiz : Nat
  xosiz : Nat
  yosiz : Nat
  xtsiz : Nat
  ytsiz : Nat
  xtosiz : Nat
  ytosiz : Nat
  csiz : Nat
  ssiz : List Nat
  xrsiz : List Nat
  yrsiz : List Nat
  deriving Repr

/-- Parse SIZ starting just after the marker (at the 2-byte length field). -/
def parseSiz (data : List UInt8) (p : Nat) : Option (SizInfo × Nat) :=
  let len := be16 data p
  if len < 38 then none else
  if data.length < p + len then none else
  let csiz := be16 data (p + 36)
  if csiz == 0 || len - 38 != csiz * 3 then none else
  let comps := List.range csiz
  some ({ rsiz := be16 data (p + 2)
          xsiz := be32 data (p + 4), ysiz := be32 data (p + 8)
          xosiz := be32 data (p + 12), yosiz := be32 data (p + 16)
          xtsiz := be32 data (p + 20), ytsiz := be32 data (p + 24)
          xtosiz := be32 data (p + 28), ytosiz := be32 data (p + 32)
          csiz := csiz
          ssiz := comps.map (fun i => (data.getD (p + 38 + i * 3) 0).toNat)
          xrsiz := comps.map (fun i => (data.getD (p + 39 + i * 3) 0).toNat)
          yrsiz := comps.map (fun i => (data.getD (p + 40 + i * 3) 0).toNat) },
        p + len)

/-- Number of tiles in the image (1 for a single-tile OpenEXR chunk). -/
def jphTileCount (s : SizInfo) : Nat :=
  let nx := (s.xsiz - s.xtosiz + s.xtsiz - 1) / s.xtsiz
  let ny := (s.ysiz - s.ytosiz + s.ytsiz - 1) / s.ytsiz
  nx * ny

/-- COD fields relevant to the profile checks. -/
structure CodInfo where
  scod : Nat
  prog : Nat
  layers : Nat
  mc : Nat
  ndecomp : Nat
  bw : Nat
  bh : Nat
  style : Nat
  wavelet : Nat
  deriving Repr

def parseCod (data : List UInt8) (p : Nat) : Option (CodInfo × Nat) :=
  let len := be16 data p
  if len < 12 || data.length < p + len then none else
  let scod := (data.getD (p + 2) 0).toNat
  let expect := 12 + (if scod &&& 1 != 0 then 1 + (data.getD (p + 7) 0).toNat else 0)
  if len != expect then none else
  some ({ scod := scod
          prog := (data.getD (p + 3) 0).toNat
          layers := be16 data (p + 4)
          mc := (data.getD (p + 6) 0).toNat
          ndecomp := (data.getD (p + 7) 0).toNat
          bw := (data.getD (p + 8) 0).toNat
          bh := (data.getD (p + 9) 0).toNat
          style := (data.getD (p + 10) 0).toNat
          wavelet := (data.getD (p + 11) 0).toNat }, p + len)

/-- Quantization subband count from QCD (no QCC override modelled here). -/
def qcdCount (data : List UInt8) (p : Nat) : Option (Nat × Nat) :=
  let len := be16 data p
  if len < 3 || data.length < p + len then none else
  let sq := (data.getD (p + 2) 0).toNat
  let guard := sq >>> 5
  if guard > 3 then none else
  let style := sq &&& 0x1f
  if style == 0 then some (len - 3, p + len)
  else if style == 1 then some ((len - 3) / 2, p + len)
  else if style == 2 then some (len - 3, p + len)
  else none


/-- Tile-part marker walk after SOT. Fuel-bounded and total. -/
def jphTileParts (data : List UInt8) (fuel : Nat) (marks : List JphMark)
    (p : Nat) : Option (List JphMark × Nat) :=
  if fuel = 0 then none else
  match nextMark data p with
  | none => none
  | some (tm, tq) =>
      let marks := marks ++ [tm]
      match tm with
      | .sod => some (marks, tq)
      | .plt | .com | .DFS | .ads | .atk | .poc =>
          if tq + 2 > data.length then none else
          let l := be16 data tq
          if l < 2 || tq + l > data.length then none
          else jphTileParts data (fuel - 1) marks (tq + l)
      | _ => none
termination_by fuel

/-- Find EOC in the entropy-coded tile payload. -/
def jphFindEoc (data : List UInt8) (fuel : Nat) (p : Nat) : Option Nat :=
  if fuel = 0 then none else
  match nextMark data p with
  | none => none
  | some (em, eq) => if em == .eoc then some eq else jphFindEoc data (fuel - 1) eq
termination_by fuel

/-- Marker sequence and geometry observed by the wrapper-level validator. -/
structure JphProfile where
  marks : List JphMark
  siz : SizInfo
  cod : Option CodInfo
  qcdCount : Option Nat
  sawSot : Bool
  sawSod : Bool
  deriving Repr

/-- Walk the codestream with segment lengths, mirroring `jph_validate_profile`
  at the wrapper level. `none` means the marker layout is unsupported/corrupt. -/
def jphLoop (data : List UInt8) (siz : SizInfo) (fuel : Nat)
    (marks : List JphMark) (cod : Option CodInfo) (qc : Option Nat)
    (sot : Bool) (sod : Bool) (p : Nat) : Option JphProfile :=
  if fuel = 0 then none else
  match nextMark data p with
  | none => none
  | some (m, q) =>
      let marks := marks ++ [m]
      match m with
      | .eoc =>
          if cod.isNone || qc.isNone || !sot || !sod then none
          else some ⟨marks, siz, cod, qc, sot, sod⟩
      | .cod =>
          match parseCod data q with
          | none => none
          | some (ci, q') => jphLoop data siz (fuel - 1) marks (some ci) qc sot sod q'
      | .qcd =>
          match qcdCount data q with
          | none => none
          | some (n, q') => jphLoop data siz (fuel - 1) marks cod (some n) sot sod q'
      | .sot =>
          if q + 10 > data.length then none else
          let len := be16 data q
          if len < 10 || q + len > data.length then none else
          match jphTileParts data fuel marks (q + len) with
          | none => none
          | some (marks', afterSod) =>
              match jphFindEoc data fuel afterSod with
              | none => none
              | some _ =>
                  if cod.isNone || qc.isNone then none
                  else some ⟨marks' ++ [.eoc], siz, cod, qc, true, true⟩
      | .cap | .qcc | .nlt | .plt | .com | .DFS | .ads | .atk | .poc | .other _ =>
          if q + 2 > data.length then none else
          let l := be16 data q
          if l < 2 || q + l > data.length then none
          else jphLoop data siz (fuel - 1) marks cod qc sot sod (q + l)
      | _ => none
termination_by fuel

/-- Entry point: SOC + SIZ followed by the wrapper-level marker walk. -/
def scanJph (data : List UInt8) : Option JphProfile := do
  let (m0, p0) ← nextMark data 0
  if m0 != .soc then none
  let (m1, p1) ← nextMark data p0
  if m1 != .siz then none
  let (siz, p2) ← parseSiz data p1
  jphLoop data siz (data.length + 1) [.soc, .siz] none none false false p2

def defaultCod : CodInfo := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The profile constraints checked by the C wrapper (excluding those that
  need the EXR header's channel count, which remain a documented boundary). -/
def jphProfileValid (p : JphProfile) : Bool :=
  let s := p.siz
  p.cod.isSome && p.qcdCount.isSome && p.sawSot && p.sawSod &&
  (s.rsiz &&& 0x4000 != 0) &&
  (s.xosiz == 0 && s.yosiz == 0 && s.xtosiz == 0 && s.ytosiz == 0) &&
  (s.xtsiz == s.xsiz && s.ytsiz == s.ysiz) &&
  (p.qcdCount.getD 0 == 1 + 3 * (p.cod.getD defaultCod).ndecomp)


/-- A valid wrapper profile has seen both SOT and SOD. -/
theorem jphProfileValid_saw {p : JphProfile} (h : jphProfileValid p) :
    p.sawSot = true ∧ p.sawSod = true := by
  unfold jphProfileValid at h
  simp_all

/-- An OpenEXR JPH chunk carries exactly one tile: SIZ tile size equals the
  image extent and all origins are zero. -/
theorem jphTileCount_single {s : SizInfo} (hx : 0 < s.xsiz) (hy : 0 < s.ysiz)
    (ht : s.xtsiz = s.xsiz) (hty : s.ytsiz = s.ysiz)
    (hxo : s.xtosiz = 0) (hyo : s.ytosiz = 0) : jphTileCount s = 1 := by
  unfold jphTileCount
  rw [ht, hty, hxo, hyo]
  simp only [Nat.sub_zero]
  have hxdiv : (s.xsiz + s.xsiz - 1) / s.xsiz = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hydiv : (s.ysiz + s.ysiz - 1) / s.ysiz = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  rw [hxdiv, hydiv]

end Exr
