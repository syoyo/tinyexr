/-
  TinyEXR - Lean 4 model of the ASTC colour-endpoint quantizer.

  Ports the pieces of `tools/texcomp/src/texcomp_astc.c` used by
  `tc_astc_hdr_color_roundtrip` (the colour-quant level path that the ASTC
  HDR endpoint packers fall back to below level 20):

  * `tc_astc_quant_levels` (per-quant-method level counts),
  * the `tc_astc_color_pquant_to_uquant` tables,
  * `tc_astc_quant_color_pquant_slow` (nearest level by absolute error,
    first minimal wins), and
  * `tc_astc_color_roundtrip` / `tc_astc_hdr_color_roundtrip`
    (clamp to 0..255, identity at level >= 20).

  The tables are transcribed verbatim from the C source; the differential
  gate (`make texcomp-astc-quant-diff`) checks all 21 levels x 256 values.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Texcomp

set_option linter.unusedVariables false

/-- `tc_astc_quant_levels`: colour symbol count per quant method (0..20). -/
def colorQuantLevels : List Nat :=
  [2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128, 160, 192, 256]

/-- Colour unquant table for 6 levels (quant method "6"). -/
def colorUquantQ6 : List Nat :=
  [0, 255, 51, 204, 102, 153]

/-- Colour unquant table for 8 levels (quant method "8"). -/
def colorUquantQ8 : List Nat :=
  [0, 36, 73, 109, 146, 182, 219, 255]

/-- Colour unquant table for 10 levels (quant method "10"). -/
def colorUquantQ10 : List Nat :=
  [0, 255, 28, 227, 56, 199, 84, 171, 113, 142]

/-- Colour unquant table for 12 levels (quant method "12"). -/
def colorUquantQ12 : List Nat :=
  [0, 255, 69, 186, 23, 232, 92, 163, 46, 209, 116, 139]

/-- Colour unquant table for 16 levels (quant method "16"). -/
def colorUquantQ16 : List Nat :=
  [0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255]

/-- Colour unquant table for 20 levels (quant method "20"). -/
def colorUquantQ20 : List Nat :=
  [0, 255, 67, 188, 13, 242, 80, 175, 27, 228, 94, 161, 40, 215, 107, 148,
   54, 201, 121, 134]

/-- Colour unquant table for 24 levels (quant method "24"). -/
def colorUquantQ24 : List Nat :=
  [0, 255, 33, 222, 66, 189, 99, 156, 11, 244, 44, 211, 77, 178, 110, 145,
   22, 233, 55, 200, 88, 167, 121, 134]

/-- Colour unquant table for 32 levels (quant method "32"). -/
def colorUquantQ32 : List Nat :=
  [0, 8, 16, 24, 33, 41, 49, 57, 66, 74, 82, 90, 99, 107, 115, 123,
   132, 140, 148, 156, 165, 173, 181, 189, 198, 206, 214, 222, 231, 239, 247, 255]

/-- Colour unquant table for 40 levels (quant method "40"). -/
def colorUquantQ40 : List Nat :=
  [0, 255, 32, 223, 65, 190, 97, 158, 6, 249, 39, 216, 71, 184, 104, 151,
   13, 242, 45, 210, 78, 177, 110, 145, 19, 236, 52, 203, 84, 171, 117, 138,
   26, 229, 58, 197, 91, 164, 123, 132]

/-- Colour unquant table for 48 levels (quant method "48"). -/
def colorUquantQ48 : List Nat :=
  [0, 255, 16, 239, 32, 223, 48, 207, 65, 190, 81, 174, 97, 158, 113, 142,
   5, 250, 21, 234, 38, 217, 54, 201, 70, 185, 86, 169, 103, 152, 119, 136,
   11, 244, 27, 228, 43, 212, 59, 196, 76, 179, 92, 163, 108, 147, 124, 131]

/-- Colour unquant table for 64 levels (quant method "64"). -/
def colorUquantQ64 : List Nat :=
  [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60,
   65, 69, 73, 77, 81, 85, 89, 93, 97, 101, 105, 109, 113, 117, 121, 125,
   130, 134, 138, 142, 146, 150, 154, 158, 162, 166, 170, 174, 178, 182, 186, 190,
   195, 199, 203, 207, 211, 215, 219, 223, 227, 231, 235, 239, 243, 247, 251, 255]

/-- Colour unquant table for 80 levels (quant method "80"). -/
def colorUquantQ80 : List Nat :=
  [0, 255, 16, 239, 32, 223, 48, 207, 64, 191, 80, 175, 96, 159, 112, 143,
   3, 252, 19, 236, 35, 220, 51, 204, 67, 188, 83, 172, 100, 155, 116, 139,
   6, 249, 22, 233, 38, 217, 54, 201, 71, 184, 87, 168, 103, 152, 119, 136,
   9, 246, 25, 230, 42, 213, 58, 197, 74, 181, 90, 165, 106, 149, 122, 133,
   13, 242, 29, 226, 45, 210, 61, 194, 77, 178, 93, 162, 109, 146, 125, 130]

/-- Colour unquant table for 96 levels (quant method "96"). -/
def colorUquantQ96 : List Nat :=
  [0, 255, 8, 247, 16, 239, 24, 231, 32, 223, 40, 215, 48, 207, 56, 199,
   64, 191, 72, 183, 80, 175, 88, 167, 96, 159, 104, 151, 112, 143, 120, 135,
   2, 253, 10, 245, 18, 237, 26, 229, 35, 220, 43, 212, 51, 204, 59, 196,
   67, 188, 75, 180, 83, 172, 91, 164, 99, 156, 107, 148, 115, 140, 123, 132,
   5, 250, 13, 242, 21, 234, 29, 226, 37, 218, 45, 210, 53, 202, 61, 194,
   70, 185, 78, 177, 86, 169, 94, 161, 102, 153, 110, 145, 118, 137, 126, 129]

/-- Colour unquant table for 128 levels (quant method "128"). -/
def colorUquantQ128 : List Nat :=
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30,
   32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62,
   64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94,
   96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126,
   129, 131, 133, 135, 137, 139, 141, 143, 145, 147, 149, 151, 153, 155, 157, 159,
   161, 163, 165, 167, 169, 171, 173, 175, 177, 179, 181, 183, 185, 187, 189, 191,
   193, 195, 197, 199, 201, 203, 205, 207, 209, 211, 213, 215, 217, 219, 221, 223,
   225, 227, 229, 231, 233, 235, 237, 239, 241, 243, 245, 247, 249, 251, 253, 255]

/-- Colour unquant table for 160 levels (quant method "160"). -/
def colorUquantQ160 : List Nat :=
  [0, 255, 8, 247, 16, 239, 24, 231, 32, 223, 40, 215, 48, 207, 56, 199,
   64, 191, 72, 183, 80, 175, 88, 167, 96, 159, 104, 151, 112, 143, 120, 135,
   1, 254, 9, 246, 17, 238, 25, 230, 33, 222, 41, 214, 49, 206, 57, 198,
   65, 190, 73, 182, 81, 174, 89, 166, 97, 158, 105, 150, 113, 142, 121, 134,
   3, 252, 11, 244, 19, 236, 27, 228, 35, 220, 43, 212, 51, 204, 59, 196,
   67, 188, 75, 180, 83, 172, 91, 164, 99, 156, 107, 148, 115, 140, 123, 132,
   4, 251, 12, 243, 20, 235, 28, 227, 36, 219, 44, 211, 52, 203, 60, 195,
   68, 187, 76, 179, 84, 171, 92, 163, 100, 155, 108, 147, 116, 139, 124, 131,
   6, 249, 14, 241, 22, 233, 30, 225, 38, 217, 46, 209, 54, 201, 62, 193,
   70, 185, 78, 177, 86, 169, 94, 161, 102, 153, 110, 145, 118, 137, 126, 129]

/-- Colour unquant table for 192 levels (quant method "192"). -/
def colorUquantQ192 : List Nat :=
  [0, 255, 4, 251, 8, 247, 12, 243, 16, 239, 20, 235, 24, 231, 28, 227,
   32, 223, 36, 219, 40, 215, 44, 211, 48, 207, 52, 203, 56, 199, 60, 195,
   64, 191, 68, 187, 72, 183, 76, 179, 80, 175, 84, 171, 88, 167, 92, 163,
   96, 159, 100, 155, 104, 151, 108, 147, 112, 143, 116, 139, 120, 135, 124, 131,
   1, 254, 5, 250, 9, 246, 13, 242, 17, 238, 21, 234, 25, 230, 29, 226,
   33, 222, 37, 218, 41, 214, 45, 210, 49, 206, 53, 202, 57, 198, 61, 194,
   65, 190, 69, 186, 73, 182, 77, 178, 81, 174, 85, 170, 89, 166, 93, 162,
   97, 158, 101, 154, 105, 150, 109, 146, 113, 142, 117, 138, 121, 134, 125, 130,
   2, 253, 6, 249, 10, 245, 14, 241, 18, 237, 22, 233, 26, 229, 30, 225,
   34, 221, 38, 217, 42, 213, 46, 209, 50, 205, 54, 201, 58, 197, 62, 193,
   66, 189, 70, 185, 74, 181, 78, 177, 82, 173, 86, 169, 90, 165, 94, 161,
   98, 157, 102, 153, 106, 149, 110, 145, 114, 141, 118, 137, 122, 133, 126, 129]

/-- `tc_astc_color_pquant_to_uquant`, indexed by `quantMethod - 4`. -/
def colorPquantToUquant : List (List Nat) :=
  [colorUquantQ6, colorUquantQ8, colorUquantQ10, colorUquantQ12, colorUquantQ16, colorUquantQ20, colorUquantQ24, colorUquantQ32, colorUquantQ40, colorUquantQ48, colorUquantQ64, colorUquantQ80, colorUquantQ96, colorUquantQ128, colorUquantQ160, colorUquantQ192]

/-- `tc_astc_color_quant_supported`: the level has a table (or is the
  identity level 20). -/
def colorQuantSupported (quantMethod : Nat) : Bool :=
  quantMethod == 20 ||
    (4 ≤ quantMethod && quantMethod ≤ 19 &&
      (colorPquantToUquant.getD (quantMethod - 4) []).length > 0)

/-- `tc_astc_quant_color_pquant_slow`: nearest level by absolute error,
  ties going to the earliest level. -/
def quantColorPquantSlow (v quantMethod : Nat) : Nat :=
  if quantMethod == 20 then v
  else
    let table := colorPquantToUquant.getD (quantMethod - 4) []
    let levels := colorQuantLevels.getD quantMethod 0
    ((List.range levels).foldl (fun (acc : Nat × Nat) i =>
      let u := table.getD i 0
      let err := if u > v then u - v else v - u
      if err < acc.2 then (i, err) else acc) (0, 0xFFFFFFFF)).1

/-- `tc_astc_color_pquant_lut[quantMethod][v]`. -/
def colorPquantLut (quantMethod v : Nat) : Nat :=
  if colorQuantSupported quantMethod then quantColorPquantSlow v quantMethod else 0

/-- `tc_astc_color_symbol_uquant`. -/
def colorSymbolUquant (quantMethod sym : Nat) : Nat :=
  if quantMethod ≥ 20 then sym
  else (colorPquantToUquant.getD (quantMethod - 4) []).getD sym 0

/-- `tc_astc_color_roundtrip`: quantize then dequantize a colour value. -/
def colorRoundtrip (quantMethod v : Nat) : Nat :=
  colorSymbolUquant quantMethod (colorPquantLut quantMethod v)

/-- `tc_astc_hdr_color_roundtrip`: colour value as the decoder reconstructs
  it at this quant level. Identity at level >= 20 and for levels 0..3, which
  have no colour table (the C helper indexes the table array at `level - 4`,
  so it must not be reached below 4); values are clamped to 0..255. -/
def hdrColorRoundtrip (level value : Nat) : Nat :=
  let v := if value > 255 then 255 else value
  if level ≥ 20 || level < 4 then v else colorRoundtrip level v

end Texcomp
