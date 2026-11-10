/-
  TinyEXR - Lean 4 formalization of the ASTC partition RGB block's bit-packing
  tail (`tc_astc_pack_partition_rgb`), extracted for independent testing.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.AstcEncode
import Texcomp.AstcEndpoints
namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_pack_partition_rgb`: the bit-packing tail, starting from the
  already ISE-encoded weight buffer. -/
def astcPackPartitionRgb (blockMode partitionCount piSeed : Nat)
    (endpointFormatsMatched : Nat) (endpointFormats : List Nat)
    (endpointHighpartSize : Nat) (colorValues : List Nat)
    (weightbuf : List Nat) (colorQuantMethod endpointValueCount weightBits : Nat) :
    List Nat :=
  let out0 := (List.range 16).map (fun i => bitrev8 (weightbuf.getD (15 - i) 0))
  let (out, bitpos) := astcSetBits out0 0 11 blockMode
  let (out, bitpos) := astcSetBits out bitpos 2 (partitionCount - 1)
  let (out, bitpos) := astcSetBits out bitpos 6 (piSeed &&& 63)
  let (out, bitpos) := astcSetBits out bitpos 4 (piSeed >>> 6)
  let bitpos := 23
  let (out, bitpos) :=
    if endpointFormatsMatched == 1 then
      astcSetBits out bitpos 6 ((endpointFormats.getD 0 0) <<< 2)
    else
      let endpointType := astcPartitionEndpointTypeCode partitionCount endpointFormats
      let endpointHighpartPos := 128 - weightBits - endpointHighpartSize
      let (out, _) := astcSetBits out bitpos 6 (endpointType &&& 63)
      let (out, _) := astcSetBits out endpointHighpartPos endpointHighpartSize (endpointType >>> 6)
      (out, endpointHighpartPos)
  let (out, _) := astcIseEncodeBits colorQuantMethod endpointValueCount colorValues out 29 16
  out

end Texcomp
