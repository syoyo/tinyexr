/-
  TinyEXR - Lean 4 formalization of the ASTC block decoder (stage A).

  Stage A of the faithful port of `tc_astc_decode_block_rgba8` in
  `tools/texcomp/src/texcomp_astc_decode.c` (spec C.2): ISE data +
  decode, block-mode 2D unpacking, partition hash (C.2.21) and weight
  infill (C.2.18) — all integer, all total.

  Inverse Trit/Quint tables are defined by enumeration over the
  spec forward tables (the C code builds the same tables by loops).
  CEM endpoint decode and full-block texel decode are stage B.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- ISE bit count parameters (spec data). -/
def iseBits : List Nat := [1, 0, 2, 0, 1, 3, 1, 2, 4, 2, 3, 5, 3, 4, 6, 4, 5, 7, 5, 6, 8]
def iseHasTrit : List Bool :=
  [false, true, false, false, true, false, false, true, false, false, true,
   false, false, true, false, false, true, false, false, true, false]
def iseHasQuint : List Bool :=
  [false, false, false, true, false, false, true, false, false, true, false,
   false, true, false, false, true, false, false, true, false, false]

/-- Forward trit value for digits (matches `tacd_integer_of_trits`;
  table is [i4][i3][i2][i1][i0], outer to inner). -/
def tritFwd (i0 i1 i2 i3 i4 : Nat) : Nat :=
  let table : List (List (List (List (List Nat)))) :=
    [[[[[0,1,2],[4,5,6],[8,9,10]],[[16,17,18],[20,21,22],[24,25,26]],[[3,7,15],[19,23,27],[12,13,14]]],
      [[[32,33,34],[36,37,38],[40,41,42]],[[48,49,50],[52,53,54],[56,57,58]],[[35,39,47],[51,55,59],[44,45,46]]],
      [[[64,65,66],[68,69,70],[72,73,74]],[[80,81,82],[84,85,86],[88,89,90]],[[67,71,79],[83,87,91],[76,77,78]]]],
     [[[[128,129,130],[132,133,134],[136,137,138]],[[144,145,146],[148,149,150],[152,153,154]],[[131,135,143],[147,151,155],[140,141,142]]],
      [[[160,161,162],[164,165,166],[168,169,170]],[[176,177,178],[180,181,182],[184,185,186]],[[163,167,175],[179,183,187],[172,173,174]]],
      [[[192,193,194],[196,197,198],[200,201,202]],[[208,209,210],[212,213,214],[216,217,218]],[[195,199,207],[211,215,219],[204,205,206]]]],
     [[[[96,97,98],[100,101,102],[104,105,106]],[[112,113,114],[116,117,118],[120,121,122]],[[99,103,111],[115,119,123],[108,109,110]]],
      [[[224,225,226],[228,229,230],[232,233,234]],[[240,241,242],[244,245,246],[248,249,250]],[[227,231,239],[243,247,251],[236,237,238]]],
      [[[28,29,30],[60,61,62],[92,93,94]],[[156,157,158],[188,189,190],[220,221,222]],[[31,63,127],[159,191,255],[252,253,254]]]]]
  ((((table.getD i4 []).getD i3 []).getD i2 []).getD i1 []).getD i0 0

/-- Forward quint value (matches `tacd_integer_of_quints`). -/
def quintFwd (i0 i1 i2 : Nat) : Nat :=
  let table : List (List (List Nat)) :=
    [[[0,1,2,3,4],[8,9,10,11,12],[16,17,18,19,20],[24,25,26,27,28],[5,13,21,29,6]],
     [[32,33,34,35,36],[40,41,42,43,44],[48,49,50,51,52],[56,57,58,59,60],[37,45,53,61,14]],
     [[64,65,66,67,68],[72,73,74,75,76],[80,81,82,83,84],[88,89,90,91,92],[69,77,85,93,22]],
     [[96,97,98,99,100],[104,105,106,107,108],[112,113,114,115,116],[120,121,122,123,124],[101,109,117,125,30]],
     [[102,103,70,71,38],[110,111,78,79,46],[118,119,86,87,54],[126,127,94,95,62],[39,47,55,63,31]]]
  ((table.getD i2 []).getD i1 []).getD i0 0

/-- Weights unquant tables by quant index (spec data). -/
def weightUnquant : List (List Nat) :=
  [[0,64],[0,32,64],[0,21,43,64],[0,16,32,48,64],[0,64,12,52,25,39],
   [0,9,18,27,37,46,55,64],[0,64,7,57,14,50,21,43,28,36],
   [0,64,17,47,5,59,23,41,11,53,28,36],[0,4,8,12,17,21,25,29,35,39,43,47,52,56,60,64],
   [0,64,16,48,3,61,19,45,6,58,23,41,9,55,26,38,13,51,29,35],
   [0,64,8,56,16,48,24,40,2,62,11,53,19,45,27,37,5,59,13,51,22,42,30,34],
   [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64]]

/-- Colour unquant tables by quant index (spec data). -/
def colorUnquant : List (List Nat) :=
  [[0,255,51,204,102,153],[0,36,73,109,146,182,219,255],
   [0,255,28,227,56,199,84,171,113,142],[0,255,69,186,23,232,92,163,46,209,116,139],
   [0,17,34,51,68,85,102,119,136,153,170,187,204,221,238,255],
   [0,255,67,188,13,242,80,175,27,228,94,161,40,215,107,148,54,201,121,134],
   [0,255,33,222,66,189,99,156,11,244,44,211,77,178,110,145,22,233,55,200,88,167,121,134],
   [0,8,16,24,33,41,49,57,66,74,82,90,99,107,115,123,132,140,148,156,165,173,181,189,198,206,214,222,231,239,247,255],
   [0,255,32,223,65,190,97,158,6,249,39,216,71,184,104,151,13,242,45,210,78,177,110,145,19,236,52,203,84,171,117,138,26,229,58,197,91,164,123,132],
   [0,255,16,239,32,223,48,207,65,190,81,174,97,158,113,142,5,250,21,234,38,217,54,201,70,185,86,169,103,152,119,136,11,244,27,228,43,212,59,196,76,179,92,163,108,147,124,131],
   [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,130,134,138,142,146,150,154,158,162,166,170,174,178,182,186,190,195,199,203,207,211,215,219,223,227,231,235,239,243,247,251,255],
   [0,255,16,239,32,223,48,207,64,191,80,175,96,159,112,143,3,252,19,236,35,220,51,204,67,188,83,172,100,155,116,139,6,249,22,233,38,217,54,201,71,184,87,168,103,152,119,136,9,246,25,230,42,213,58,197,74,181,90,165,106,149,122,133,13,242,29,226,45,210,61,194,77,178,93,162,109,146,125,130],
   [0,255,8,247,16,239,24,231,32,223,40,215,48,207,56,199,64,191,72,183,80,175,88,167,96,159,104,151,112,143,120,135,2,253,10,245,18,237,26,229,35,220,43,212,51,204,59,196,67,188,75,180,83,172,91,164,99,156,107,148,115,140,123,132,5,250,13,242,21,234,29,226,37,218,45,210,53,202,61,194,70,185,78,177,86,169,94,161,102,153,110,145,118,137,126,129],
   [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,129,131,133,135,137,139,141,143,145,147,149,151,153,155,157,159,161,163,165,167,169,171,173,175,177,179,181,183,185,187,189,191,193,195,197,199,201,203,205,207,209,211,213,215,217,219,221,223,225,227,229,231,233,235,237,239,241,243,245,247,249,251,253,255],
   [0,255,8,247,16,239,24,231,32,223,40,215,48,207,56,199,64,191,72,183,80,175,88,167,96,159,104,151,112,143,120,135,1,254,9,246,17,238,25,230,33,222,41,214,49,206,57,198,65,190,73,182,81,174,89,166,97,158,105,150,113,142,121,134,3,252,11,244,19,236,27,228,35,220,43,212,51,204,59,196,67,188,75,180,83,172,91,164,99,156,107,148,115,140,123,132,4,251,12,243,20,235,28,227,36,219,44,211,52,203,60,195,68,187,76,179,84,171,92,163,100,155,108,147,116,139,124,131,6,249,14,241,22,233,30,225,38,217,46,209,54,201,62,193,70,185,78,177,86,169,94,161,102,153,110,145,118,137,126,129],
   [0,255,4,251,8,247,12,243,16,239,20,235,24,231,28,227,32,223,36,219,40,215,44,211,48,207,52,203,56,199,60,195,64,191,68,187,72,183,76,179,80,175,84,171,88,167,92,163,96,159,100,155,104,151,108,147,112,143,116,139,120,135,124,131,1,254,5,250,9,246,13,242,17,238,21,234,25,230,29,226,33,222,37,218,41,214,45,210,49,206,53,202,57,198,61,194,65,190,69,186,73,182,77,178,81,174,85,170,89,166,93,162,97,158,101,154,105,150,109,146,113,142,117,138,121,134,125,130,2,253,6,249,10,245,14,241,18,237,22,233,26,229,30,225,34,221,38,217,42,213,46,209,50,205,54,201,58,197,62,193,66,189,70,185,74,181,78,177,82,173,86,169,90,165,94,161,98,157,102,153,106,149,110,145,114,141,118,137,122,133,126,129]]

/-- Raw bit reader (LSB-first over the byte list). -/
def rdBits (bytes : List Nat) (bitpos nbits : Nat) : Nat :=
  (List.range nbits).foldl (fun acc i =>
    acc ||| (((bytes.getD ((bitpos + i) >>> 3) 0 >>> ((bitpos + i) &&& 7)) &&& 1) <<< i)) 0

/-- ISE bit count. -/
def iseBitcount (valueCount quant : Nat) : Nat :=
  let scale := [1,8,2,7,13,3,10,18,4,13,23,5,16,28,6,19,33,7,22,38,8].getD quant 0
  let divCode := [0,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0].getD quant 0
  let divisor := divCode * 2 + 1
  (scale * valueCount + divisor - 1) / divisor

/-- Inverse trit lookup by enumeration (none = invalid). -/
def tritsOf (t : Nat) : Option (List Nat) :=
  ((List.range 243).find? (fun n =>
    tritFwd (n % 3) ((n / 3) % 3) ((n / 9) % 3) ((n / 27) % 3) ((n / 81) % 3) == t)).map
    (fun n => [n % 3, (n / 3) % 3, (n / 9) % 3, (n / 27) % 3, (n / 81) % 3])

/-- Inverse quint lookup by enumeration (none = invalid). -/
def quintsOf (q : Nat) : Option (List Nat) :=
  ((List.range 125).find? (fun n =>
    quintFwd (n % 5) ((n / 5) % 5) ((n / 25) % 5) == q)).map
    (fun n => [n % 5, (n / 5) % 5, (n / 25) % 5])

/-- Trit-group ISE decode (group of up to 5 symbols), fuel-bounded. -/
def iseDecodeTritsGo (fuel rem off : Nat) (acc : List Nat) (bytesList : List Nat)
    (nbits : Nat) : Option (List Nat) :=
  let tbits := [2, 2, 1, 2, 1]
  let tshift := [0, 2, 4, 5, 7]
  if rem == 0 then some acc
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let group := if rem < 5 then rem else 5
      let (lows, t, off2) : (List Nat × Nat × Nat) :=
        (List.range group).foldl (fun a j =>
          let low := rdBits bytesList a.2.2 nbits
          let off1 := a.2.2 + nbits
          let tt := a.2.1 ||| (rdBits bytesList off1 (tbits.getD j 0) <<< (tshift.getD j 0))
          (a.1 ++ [low], (tt, off1 + tbits.getD j 0))) (([], (0, off)))
      match tritsOf t with
      | none => none
      | some trits =>
        iseDecodeTritsGo fuel (rem - group) off2 (acc ++
          (List.range group).map (fun j =>
            (trits.getD j 0 <<< nbits) ||| lows.getD j 0)) bytesList nbits

def iseDecodeTrits (valueCount : Nat) (bytesList : List Nat) (bitOffset : Nat)
    (nbits : Nat) : Option (List Nat) :=
  iseDecodeTritsGo valueCount valueCount bitOffset [] bytesList nbits

/-- Quint-group ISE decode (group of up to 3 symbols), fuel-bounded. -/
def iseDecodeQuintsGo (fuel rem off : Nat) (acc : List Nat) (bytesList : List Nat)
    (nbits : Nat) : Option (List Nat) :=
  let qbits := [3, 2, 2]
  let qshift := [0, 3, 5]
  if rem == 0 then some acc
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let group := if rem < 3 then rem else 3
      let (lows, q, off2) : (List Nat × Nat × Nat) :=
        (List.range group).foldl (fun a j =>
          let low := rdBits bytesList a.2.2 nbits
          let off1 := a.2.2 + nbits
          let qq := a.2.1 ||| (rdBits bytesList off1 (qbits.getD j 0) <<< (qshift.getD j 0))
          (a.1 ++ [low], (qq, off1 + qbits.getD j 0))) (([], (0, off)))
      match quintsOf q with
      | none => none
      | some qs =>
        iseDecodeQuintsGo fuel (rem - group) off2 (acc ++
          (List.range group).map (fun j =>
            (qs.getD j 0 <<< nbits) ||| lows.getD j 0)) bytesList nbits

def iseDecodeQuints (valueCount : Nat) (bytesList : List Nat) (bitOffset : Nat)
    (nbits : Nat) : Option (List Nat) :=
  iseDecodeQuintsGo valueCount valueCount bitOffset [] bytesList nbits

/-- ISE decode: returns symbols or none on invalid input. -/
def iseDecode (quant valueCount : Nat) (bytesList : List Nat) (bitOffset : Nat) :
    Option (List Nat) :=
  if quant >= 21 || valueCount == 0 then none
  else
    let nbits := iseBits.getD quant 0
    if iseHasTrit.getD quant false then
      iseDecodeTrits valueCount bytesList bitOffset nbits
    else if iseHasQuint.getD quant false then
      iseDecodeQuints valueCount bytesList bitOffset nbits
    else
      let (syms, _) := (List.range valueCount).foldl (fun a _ =>
        let v := rdBits bytesList a.2 nbits
        (a.1 ++ [v], a.2 + nbits)) (([] : List Nat), bitOffset)
      some syms

/-- Block-mode 2D decode (spec C.2.10). -/
structure BlockMode where
  wx : Nat
  wy : Nat
  quant : Nat
  dual : Nat
  deriving Repr

def decodeBlockMode (mode : Nat) : Option BlockMode :=
  let baseQuant0 := (mode >>> 4) &&& 1
  let h := (mode >>> 9) &&& 1
  let d := (mode >>> 10) &&& 1
  let a := (mode >>> 5) &&& 3
  let (baseQuant, x, y, h', d') :=
    if (mode &&& 3) != 0 then
      let baseQuant := baseQuant0 ||| ((mode &&& 3) <<< 1)
      let b := (mode >>> 7) &&& 3
      match (mode >>> 2) &&& 3 with
      | 0 => (baseQuant, b + 4, a + 2, h, d)
      | 1 => (baseQuant, b + 8, a + 2, h, d)
      | 2 => (baseQuant, a + 2, b + 8, h, d)
      | _ =>
        let b' := b &&& 1
        if mode &&& 0x100 != 0 then (baseQuant, b' + 2, a + 2, h, d)
        else (baseQuant, a + 2, b' + 6, h, d)
    else
      let baseQuant := baseQuant0 ||| (((mode >>> 2) &&& 3) <<< 1)
      if ((mode >>> 2) &&& 3) == 0 then (baseQuant, 0, 0, h, d)
      else
        let b := (mode >>> 9) &&& 3
        match (mode >>> 7) &&& 3 with
        | 0 => (baseQuant, 12, a + 2, h, d)
        | 1 => (baseQuant, a + 2, 12, h, d)
        | 2 => (baseQuant, a + 6, b + 6, 0, 0)
        | _ =>
          if a == 0 then (baseQuant, 6, 10, h, d)
          else if a == 1 then (baseQuant, 10, 6, h, d)
          else (baseQuant, 0, 0, 0, 0)
  if baseQuant < 2 then none
  else
    let quant := (baseQuant - 2) + 6 * h'
    if quant < 12 && x * y * (d' + 1) <= 64 then some ⟨x, y, quant, d'⟩
    else none

/-- Partition hash (spec C.2.21), UInt32 wraparound. -/
def hash52 (inp : UInt32) : UInt32 :=
  let a := inp ^^^ (inp >>> 15)
  let b := a * 0xeede0891
  let c := b ^^^ (b >>> 5)
  let d := c + (c <<< 16)
  let e := d ^^^ (d >>> 7)
  let f := e ^^^ (e >>> 3)
  let g := f ^^^ (f <<< 6)
  g ^^^ (g >>> 17)

def selectPartition (seed x y partitionCount : Nat) (smallBlock : Bool) : Nat :=
  let x' := if smallBlock then x * 2 else x
  let y' := if smallBlock then y * 2 else y
  let seed' := (seed + (partitionCount - 1) * 1024) % 4294967296
  let rnum := hash52 (UInt32.ofNat seed')
  let s1n := (rnum &&& 15).toNat
  let s2n := ((rnum >>> 4) &&& 15).toNat
  let s3n := ((rnum >>> 8) &&& 15).toNat
  let s4n := ((rnum >>> 12) &&& 15).toNat
  let s5n := ((rnum >>> 16) &&& 15).toNat
  let s6n := ((rnum >>> 20) &&& 15).toNat
  let s7n := ((rnum >>> 24) &&& 15).toNat
  let s8n := ((rnum >>> 28) &&& 15).toNat
  let s9n := ((rnum >>> 18) &&& 15).toNat
  let s10n := ((rnum >>> 22) &&& 15).toNat
  let s11n := ((rnum >>> 26) &&& 15).toNat
  let s12n := (((rnum >>> 30) ||| (rnum <<< 2)) &&& 15).toNat
  let sq := fun v : Nat => v * v
  let sh1 := if (seed' % 2) != 0 then (if (seed' % 4) >= 2 then 4 else 5)
             else if partitionCount == 3 then 6 else 5
  let sh2 := if (seed' % 2) != 0 then (if partitionCount == 3 then 6 else 5)
             else if (seed' % 4) >= 2 then 4 else 5
  let sh3 := if (seed' % 16) >= 16 then sh1 else sh2
  let s1 := sq s1n >>> sh1
  let s2 := sq s2n >>> sh2
  let s3 := sq s3n >>> sh1
  let s4 := sq s4n >>> sh2
  let s5 := sq s5n >>> sh1
  let s6 := sq s6n >>> sh2
  let s7 := sq s7n >>> sh1
  let s8 := sq s8n >>> sh2
  let s9 := sq s9n >>> sh3
  let s10 := sq s10n >>> sh3
  let s11 := sq s11n >>> sh3
  let s12 := sq s12n >>> sh3
  let a := (s1 * x' + s2 * y' + ((rnum >>> 14).toNat)) % 64
  let b := (s3 * x' + s4 * y' + ((rnum >>> 10).toNat)) % 64
  let c := (s5 * x' + s6 * y' + ((rnum >>> 6).toNat)) % (if partitionCount > 2 then 64 else 1)
  let d := (s7 * x' + s8 * y' + ((rnum >>> 2).toNat)) % (if partitionCount > 3 then 64 else 1)
  if a >= b && a >= c && a >= d then 0
  else if b >= c && b >= d then 1
  else if c >= d then 2
  else 3

/-- Weight infill (spec C.2.18). -/
def infillWeight (grid : List Nat) (gw gh bw bh x y' : Nat) : Nat :=
  let ds := (1024 + bw / 2) / (bw - 1)
  let dt := (1024 + bh / 2) / (bh - 1)
  let cs := ds * x
  let ct := dt * y'
  let gs := (cs * (gw - 1) + 32) / 64
  let gt := (ct * (gh - 1) + 32) / 64
  let js := gs / 16
  let fs := gs % 16
  let jt := gt / 16
  let ft := gt % 16
  let w11 := (fs * ft + 8) / 16
  let w10 := (ft : Int) - (w11 : Int)
  let w01 := (fs : Int) - (w11 : Int)
  let w00 := (16 : Int) - (fs : Int) - (ft : Int) + (w11 : Int)
  let v0 := js + jt * gw
  let p00 := grid.getD v0 0
  let p01 := if js + 1 < gw then grid.getD (v0 + 1) 0 else 0
  let p10 := if jt + 1 < gh then grid.getD (v0 + gw) 0 else 0
  let p11 := if js + 1 < gw && jt + 1 < gh then grid.getD (v0 + gw + 1) 0 else 0
  (Int.toNat (p00 * w00 + p01 * w01 + p10 * w10 + p11 * w11 + 8)) / 16

/-- Clamp to 0..255 (Nat input/output). -/
def clampNat (v : Int) : Nat :=
  if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- One bit-transfer step on a (base, delta) pair (signed, Int). -/
def bitTransfer (base delta : Int) : Int × Int :=
  let b := base / 2 + (if delta % 256 < 128 then 0 else 128)
  let d0 := (delta / 2) % 64
  let d := if d0 % 64 >= 32 then d0 - 64 else d0
  (b, d)

/-- Blue contract: v0=(v0+v2)/2, v1=(v1+v2)/2 on a 4-lane Nat tuple. -/
def blueContract (v : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  ((v.1 + v.2.1) / 2, (v.2.2.1 + v.2.1) / 2, v.2.1, v.2.2.2)

/-- LDR CEM decode. Returns (e0, e1, consumed). -/
def decodeCem (cem : Nat) (v : List Nat) :
    Option ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) × Nat) :=
  match cem with
  | 1 =>
    let l0 := (v.getD 0 0 >>> 2) ||| (v.getD 1 0 &&& 0xC0)
    let l1 := if l0 + (v.getD 1 0 &&& 0x3F) > 255 then 255 else l0 + (v.getD 1 0 &&& 0x3F)
    some ((l0, l0, l0, 255), (l1, l1, l1, 255), 2)
  | 5 =>
    let (l0, l1) := bitTransfer (Int.ofNat (v.getD 0 0)) (Int.ofNat (v.getD 1 0))
    let (a0, a1) := bitTransfer (Int.ofNat (v.getD 2 0)) (Int.ofNat (v.getD 3 0))
    some ((clampNat l0, clampNat l0, clampNat l0, clampNat a0),
          (clampNat (l1 + l0), clampNat (l1 + l0), clampNat (l1 + l0), clampNat (a1 + a0)), 4)
  | 9 | 13 =>
    let n := if cem == 9 then 3 else 4
    let pairs := (List.range n).map (fun c =>
      bitTransfer (Int.ofNat (v.getD (c * 2) 0)) (Int.ofNat (v.getD (c * 2 + 1) 0)))
    let bases0 := pairs.map (·.1)
    let deltas0 := pairs.map (·.2)
    let base := if n == 3 then bases0 ++ [255] else bases0
    let delta := if n == 3 then deltas0 ++ [0] else deltas0
    let sum := delta.getD 0 0 + delta.getD 1 0 + delta.getD 2 0
    let delta1 := (List.range 4).map (fun c => delta.getD c 0 + base.getD c 0)
    let (base', delta') :=
      if sum < 0 then
        let bc := fun l => [(l.getD 0 0 + l.getD 2 0) / 2, (l.getD 1 0 + l.getD 2 0) / 2,
                            l.getD 2 0, l.getD 3 0]
        (bc delta1, bc base)
      else (base, delta1)
    let to4 := fun l => (clampNat (l.getD 0 0), clampNat (l.getD 1 0),
                         clampNat (l.getD 2 0), clampNat (l.getD 3 0))
    let e0 := to4 base'
    let e1 := to4 delta'
    if n == 3 then some ((e0.1, e0.2.1, e0.2.2.1, 255), (e1.1, e1.2.1, e1.2.2.1, 255), 6)
    else some (e0, e1, 8)
  | 0 =>
    let e0 := v.getD 0 0
    let e1 := v.getD 1 0
    some ((e0, e0, e0, 255), (e1, e1, e1, 255), 2)
  | 4 =>
    let e0 := v.getD 0 0
    let e1 := v.getD 1 0
    some ((e0, e0, e0, v.getD 2 0), (e1, e1, e1, v.getD 3 0), 4)
  | 6 =>
    let s := v.getD 3 0
    some (((v.getD 0 0 * s) / 256, (v.getD 1 0 * s) / 256, (v.getD 2 0 * s) / 256, 255),
          (v.getD 0 0, v.getD 1 0, v.getD 2 0, 255), 4)
  | 8 =>
    let s0 := v.getD 0 0 + v.getD 2 0 + v.getD 4 0
    let s1 := v.getD 1 0 + v.getD 3 0 + v.getD 5 0
    if s1 >= s0 then
      some ((v.getD 0 0, v.getD 2 0, v.getD 4 0, 255),
            (v.getD 1 0, v.getD 3 0, v.getD 5 0, 255), 6)
    else
      let rgb0 := (v.getD 1 0, v.getD 3 0, v.getD 5 0, 255)
      let rgb1 := ((v.getD 0 0 + v.getD 4 0) / 2, (v.getD 2 0 + v.getD 4 0) / 2, v.getD 4 0, 255)
      some (rgb0, rgb1, 6)
  | 12 =>
    let s0 := v.getD 0 0 + v.getD 2 0 + v.getD 4 0
    let s1 := v.getD 1 0 + v.getD 3 0 + v.getD 5 0
    if s1 >= s0 then
      some ((v.getD 0 0, v.getD 2 0, v.getD 4 0, v.getD 6 0),
            (v.getD 1 0, v.getD 3 0, v.getD 5 0, v.getD 7 0), 8)
    else
      let rgb0 := (v.getD 1 0, v.getD 3 0, v.getD 5 0, v.getD 6 0)
      let rgb1 := ((v.getD 0 0 + v.getD 4 0) / 2, (v.getD 2 0 + v.getD 4 0) / 2,
                   v.getD 4 0, v.getD 7 0)
      some (rgb0, rgb1, 8)
  | 10 =>
    let s := v.getD 3 0
    some (((v.getD 0 0 * s) / 256, (v.getD 1 0 * s) / 256, (v.getD 2 0 * s) / 256, v.getD 4 0),
          (v.getD 0 0, v.getD 1 0, v.getD 2 0, v.getD 5 0), 6)
  | _ => none

/-- 8-bit reversal (ASTC weight stream order). -/
def bitrev8 (v : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (((v >>> i) &&& 1) <<< (7 - i))) 0

/-- Decode one ASTC block to bw*bh RGBA texels (row-major). Invalid → zeros.
  `bytesList` holds the 16 block bytes as naturals. -/
def astcDecodeBlock (bytesList : List Nat) (bw bh : Nat) :
    Fin (bw * bh) → (UInt8 × UInt8 × UInt8 × UInt8) :=
  fun texel =>
    let mode := rdBits bytesList 0 11
    let zero : UInt8 × UInt8 × UInt8 × UInt8 := (0, 0, 0, 0)
    if (mode &&& 0x1FF) == 0x1FC && (mode &&& (1 <<< 9)) == 0 then
      let v := fun c => (bytesList.getD (8 + c * 2) 0 ||| (bytesList.getD (9 + c * 2) 0 <<< 8)) >>> 8
      (UInt8.ofNat (v 0), UInt8.ofNat (v 1), UInt8.ofNat (v 2), UInt8.ofNat (v 3))
    else
      match decodeBlockMode mode with
      | none => zero
      | some bm =>
        if bm.wx > bw || bm.wy > bh then zero
        else
          let partCount := rdBits bytesList 11 2 + 1
          if bm.dual != 0 && partCount == 4 then zero
          else
            let weightCount := bm.wx * bm.wy * (if bm.dual != 0 then 2 else 1)
            let weightBits := iseBitcount weightCount bm.quant
            if weightCount > 64 || weightBits < 24 || weightBits > 96 then zero
            else
              let rev := (List.range 16).map (fun i => bitrev8 (bytesList.getD (15 - i) 0))
              match iseDecode bm.quant weightCount rev 0 with
              | none => zero
              | some wvalues =>
                let wx := bm.wx
                let wy := bm.wy
                let uq := weightUnquant.getD bm.quant []
                let wgrid0 := (List.range (wx * wy)).map (fun i =>
                  uq.getD (wvalues.getD (if bm.dual != 0 then i * 2 else i) 0) 0)
                let wgrid1 := (List.range (wx * wy)).map (fun i =>
                  uq.getD (wvalues.getD (i * 2 + 1) 0) 0)
                let (cems, colorStart, extraBits, pindex) :
                    (List Nat × Nat × Nat × Nat) :=
                  if partCount == 1 then
                    ([rdBits bytesList 13 4], 17, 0, 0)
                  else
                    let pindex := rdBits bytesList 13 10
                    let cf := rdBits bytesList 23 6
                    if (cf &&& 3) == 0 then
                      ((List.range partCount).map (fun _ => cf >>> 2), 29, 0, pindex)
                    else
                      let baseClass := (cf &&& 3) - 1
                      let extra := 3 * partCount - 4
                      let extPos := 128 - weightBits - extra
                      let code := cf + (rdBits bytesList extPos extra <<< 6)
                      ((List.range partCount).map (fun i =>
                        (((baseClass + ((code >>> (2 + i)) &&& 1)) <<< 2) +
                         ((code >>> (2 + partCount + 2 * i)) &&& 3))), 29, extra, pindex)
                let (extraBits', ccs) :
                    (Nat × Nat) :=
                  if bm.dual != 0 then
                    (extraBits, rdBits bytesList (128 - weightBits - extraBits - 2) 2)
                  else (extraBits, 3)
                let ccsBits := if bm.dual != 0 then 2 else 0
                let vcount := (List.range partCount).foldl (fun acc i =>
                  acc + (((cems.getD i 0 >>> 2) + 1) * 2)) 0
                let used := colorStart + weightBits + extraBits' + ccsBits
                let avail := 128 - used
                let cq := (List.range 21).reverse.find? (fun i =>
                  (not (i < 4)) && (iseBitcount vcount i <= avail))
                match cq with
                | none => zero
                | some cq =>
                  match iseDecode cq vcount bytesList colorStart with
                  | none => zero
                  | some csyms =>
                    let cu := colorUnquant.getD (cq - 4) []
                    let vals := (List.range vcount).map (fun i =>
                      if cq == 20 then csyms.getD i 0 else cu.getD (csyms.getD i 0) 0)
                    let (elist, consumed) :=
                      (List.range partCount).foldl (fun a i =>
                        match decodeCem (cems.getD i 0) (vals.drop a.2) with
                        | none => (a.1, a.2)
                        | some (e0, e1, n) => (a.1 ++ [(e0, e1)], a.2 + n))
                        (([] : List ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat))), 0)
                    if consumed != vals.length then zero
                    else
                      let smallBlock := bw * bh < 32
                      let x := texel.val % bw
                      let y := texel.val / bw
                      let part := if partCount == 1 then 0
                                  else selectPartition pindex x y partCount smallBlock
                      let part := if part >= partCount then partCount - 1 else part
                      let w0 := infillWeight wgrid0 wx wy bw bh x y
                      let w1 := if bm.dual != 0 then infillWeight wgrid1 wx wy bw bh x y else w0
                      let (e0, e1) := elist.getD part ((0, 0, 0, 0), (0, 0, 0, 0))
                      let chan := fun t : Nat × Nat × Nat × Nat => fun c =>
                        match c with | 0 => t.1 | 1 => t.2.1 | 2 => t.2.2.1 | _ => t.2.2.2
                      let interp := fun c w =>
                        ((((chan e0 c) * (64 - w) + (chan e1 c) * w) * 257 + 32) / 64) / 256
                      (UInt8.ofNat (interp 0 (if bm.dual != 0 && ccs == 0 then w1 else w0)),
                       UInt8.ofNat (interp 1 (if bm.dual != 0 && ccs == 1 then w1 else w0)),
                       UInt8.ofNat (interp 2 (if bm.dual != 0 && ccs == 2 then w1 else w0)),
                       UInt8.ofNat (interp 3 (if bm.dual != 0 && ccs == 3 then w1 else w0)))

end Texcomp
