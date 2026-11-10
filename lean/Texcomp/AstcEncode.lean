/-
  Forward ISE bit packing (`tc_astc_ise_encode_bits`).
-/

import Texcomp.AstcDecode

namespace Texcomp

set_option linter.unusedVariables false

def astcSetBits (dst : List Nat) (bp n val : Nat) : List Nat × Nat :=
  let st := (List.range n).foldl (fun (s : List Nat × Nat × Nat) _ =>
    let (d, p, v) := s
    let byteIdx := p / 8
    let shift := p % 8
    let bit := v &&& 1
    let d := d.set byteIdx (d.getD byteIdx 0 ||| (bit <<< shift))
    (d, p + 1, v >>> 1)) (dst, bp, val)
  (st.1, st.2.1)

def astcIseEncodeBits (quantLevel valueCount : Nat) (values : List Nat)
    (out : List Nat) (bitOffset : Nat) (outSize : Nat) : List Nat × Nat :=
  let bitsTable : List Nat := [1, 0, 2, 0, 1, 3, 1, 2, 4, 2, 3, 5, 3, 4, 6, 4, 5, 7, 5, 6, 8]
  let hasTritTable : List Nat := [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]
  let hasQuintTable : List Nat := [0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]
  if values.isEmpty || out.isEmpty || valueCount == 0 || quantLevel ≥ 21 then
    (out, bitOffset)
  else
    let nbits := bitsTable.getD quantLevel 0
    let totalBits := iseBitcount valueCount quantLevel
    if (bitOffset + totalBits + 7) / 8 > outSize then (out, bitOffset)
    else if hasTritTable.getD quantLevel 0 != 0 then
      let mask := (1 <<< nbits) - 1
      let (out, bp, i) := (List.range (valueCount / 5)).foldl (fun (st : List Nat × Nat × Nat) _ =>
        let (out, bp, i) := st
        if i + 4 >= valueCount then (out, bp, i)
        else
          let t := tritFwd (values.getD i 0 >>> nbits)
                           (values.getD (i + 1) 0 >>> nbits)
                           (values.getD (i + 2) 0 >>> nbits)
                           (values.getD (i + 3) 0 >>> nbits)
                           (values.getD (i + 4) 0 >>> nbits)
          let pack0 := (values.getD i 0 &&& mask) ||| (((t &&& 3)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 2) pack0
          let pack1 := (values.getD (i + 1) 0 &&& mask) ||| ((((t >>> 2) &&& 3)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 2) pack1
          let pack2 := (values.getD (i + 2) 0 &&& mask) ||| ((((t >>> 4) &&& 1)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 1) pack2
          let pack3 := (values.getD (i + 3) 0 &&& mask) ||| ((((t >>> 5) &&& 3)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 2) pack3
          let pack4 := (values.getD (i + 4) 0 &&& mask) ||| ((((t >>> 7) &&& 1)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 1) pack4
          (out, bp, i + 5)) (out, bitOffset, 0)
      if i >= valueCount then (out, bp)
      else
        let i3 := if i + 3 >= valueCount then 0 else values.getD (i + 3) 0 >>> nbits
        let i2 := if i + 2 >= valueCount then 0 else values.getD (i + 2) 0 >>> nbits
        let i1 := if i + 1 >= valueCount then 0 else values.getD (i + 1) 0 >>> nbits
        let i0 := values.getD i 0 >>> nbits
        let t := tritFwd i0 i1 i2 i3 0
        let tbits : List Nat := [2, 2, 1, 2]
        let tshift : List Nat := [0, 2, 4, 5]
        let r := valueCount - i
        let (out, bp) := if r >= 1 then
          let pack := (values.getD i 0 &&& mask) ||| ((((t >>> (tshift.getD 0 0)) &&& ((1 <<< (tbits.getD 0 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 0 0)) pack
        else (out, bp)
        let (out, bp) := if r >= 2 then
          let pack := (values.getD (i + 1) 0 &&& mask) ||| ((((t >>> (tshift.getD 1 0)) &&& ((1 <<< (tbits.getD 1 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 1 0)) pack
        else (out, bp)
        let (out, bp) := if r >= 3 then
          let pack := (values.getD (i + 2) 0 &&& mask) ||| ((((t >>> (tshift.getD 2 0)) &&& ((1 <<< (tbits.getD 2 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 2 0)) pack
        else (out, bp)
        let (out, bp) := if r >= 4 then
          let pack := (values.getD (i + 3) 0 &&& mask) ||| ((((t >>> (tshift.getD 3 0)) &&& ((1 <<< (tbits.getD 3 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 3 0)) pack
        else (out, bp)
        (out, bp)
    else if hasQuintTable.getD quantLevel 0 != 0 then
      let mask := (1 <<< nbits) - 1
      let (out, bp, i) := (List.range ((valueCount + 2) / 3)).foldl (fun (st : List Nat × Nat × Nat) _ =>
        let (out, bp, i) := st
        if i + 2 >= valueCount then (out, bp, i)
        else
          let q := quintFwd (values.getD i 0 >>> nbits)
                            (values.getD (i + 1) 0 >>> nbits)
                            (values.getD (i + 2) 0 >>> nbits)
          let pack0 := (values.getD i 0 &&& mask) ||| (((q &&& 7)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 3) pack0
          let pack1 := (values.getD (i + 1) 0 &&& mask) ||| ((((q >>> 3) &&& 3)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 2) pack1
          let pack2 := (values.getD (i + 2) 0 &&& mask) ||| ((((q >>> 5) &&& 3)) <<< nbits)
          let (out, bp) := astcSetBits out bp (nbits + 2) pack2
          (out, bp, i + 3)) (out, bitOffset, 0)
      if i >= valueCount then (out, bp)
      else
        let i1 := if i + 1 >= valueCount then 0 else values.getD (i + 1) 0 >>> nbits
        let i0 := values.getD i 0 >>> nbits
        let q := quintFwd i0 i1 0
        let tbits : List Nat := [3, 2]
        let tshift : List Nat := [0, 3]
        let r := valueCount - i
        let (out, bp) := if r >= 1 then
          let pack := (values.getD i 0 &&& mask) ||| ((((q >>> (tshift.getD 0 0)) &&& ((1 <<< (tbits.getD 0 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 0 0)) pack
        else (out, bp)
        let (out, bp) := if r >= 2 then
          let pack := (values.getD (i + 1) 0 &&& mask) ||| ((((q >>> (tshift.getD 1 0)) &&& ((1 <<< (tbits.getD 1 0)) - 1))) <<< nbits)
          astcSetBits out bp (nbits + (tbits.getD 1 0)) pack
        else (out, bp)
        (out, bp)
    else
      (List.range valueCount).foldl (fun (st : List Nat × Nat) k =>
        astcSetBits st.1 st.2 nbits (values.getD k 0)) (out, bitOffset)

end Texcomp
