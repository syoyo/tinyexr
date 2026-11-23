/-
  TinyEXR - shared header-validation predicate.

  Mirrors the checks in `exr_header_validate` (`src/exr_core.c`) that both
  the reader (`interpret_header`) and the writer (`exr_writer_add_part`)
  apply. This is a specification of the accepted-header set, checked against
  the C validator by `make header-validate-diff`.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

namespace Exr

set_option linter.unusedVariables false

def maxDimension : Nat := 1 <<< 20
def maxChannels : Nat := 1024
def maxName : Nat := 256

structure ChanView where
  nameLen : Nat
  pixelType : Int
  xSampling : Int
  ySampling : Int
  pLinear : Int
  deriving Repr

structure HeaderView where
  numChannels : Nat
  channelsPresent : Bool
  partType : Int
  compression : Int
  lineOrder : Int
  minX : Int
  maxX : Int
  minY : Int
  maxY : Int
  displayMinX : Int
  displayMaxX : Int
  displayMinY : Int
  displayMaxY : Int
  pixelAspectRatio : Float
  screenWidth : Float
  finiteFloats : Bool
  tiled : Bool
  tileX : Nat
  tileY : Nat
  levelMode : Int
  roundingMode : Int
  nameLen : Nat
  channels : List ChanView
  deriving Repr

def allFinite (h : HeaderView) : Bool := h.finiteFloats

/-- `exr_header_validate` restricted to the fields the differential vectors
  enumerate. The C validator also walks custom attributes; that part is
  covered by the C regression tests and remains a documented boundary. -/
def headerValid (h : HeaderView) : Bool :=
  let w : Int := h.maxX - h.minX + 1
  let ht : Int := h.maxY - h.minY + 1
  h.numChannels > 0 && h.numChannels <= maxChannels && h.channelsPresent &&
  h.partType >= 0 && h.partType <= 3 &&
  h.compression >= 0 && h.compression <= 8 &&
  h.lineOrder >= 0 && h.lineOrder <= 1 &&
  w > 0 && ht > 0 && w <= (maxDimension : Int) && ht <= (maxDimension : Int) &&
  h.displayMaxX >= h.displayMinX && h.displayMaxY >= h.displayMinY &&
  allFinite h && h.pixelAspectRatio > 0 && h.screenWidth >= 0 &&
  (((h.partType == 1) || (h.partType == 3)) == h.tiled) &&
  (!h.tiled ||
    (h.tileX > 0 && h.tileY > 0 &&
     h.tileX <= maxDimension && h.tileY <= maxDimension &&
     h.levelMode >= 0 && h.levelMode <= 2 &&
     h.roundingMode >= 0 && h.roundingMode <= 2)) &&
  h.nameLen < maxName &&
  h.channels.length == h.numChannels &&
  (h.channels.all (fun c =>
    c.nameLen > 0 && c.nameLen < maxName &&
    c.pixelType >= 0 && c.pixelType <= 2 &&
    c.xSampling >= 1 && c.ySampling >= 1 &&
    c.pLinear >= 0 && c.pLinear <= 1 &&
    (!h.tiled || (c.xSampling == 1 && c.ySampling == 1))))

theorem headerValid_numChannels_pos {h : HeaderView} (hv : headerValid h) :
    0 < h.numChannels := by
  simp [headerValid] at hv
  omega

end Exr
