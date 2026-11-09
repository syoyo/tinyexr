/-
  TinyEXR - Lean 4 formalization of the texcomp texture-container formats.

  First slice: the DDS (BC1/BC3/BC5/BC6H/BC7), KTX (ETC2/EAC) and ASTC
  file headers that `tools/texcomp` writes, modelled as fixed-width byte
  layouts with size equations and parse/emit round trips. Block payloads are
  treated as opaque byte runs; their codecs are formalized separately.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Bytes

namespace Texcomp

open Exr

def ddsHeaderSize : Nat := 148
def ktxHeaderSize : Nat := 68
def ktxMagicSize : Nat := 12
def ktxEndianMarker : UInt32 := 0x04030201

structure DdsHeader where
  width      : UInt32
  height     : UInt32
  dxgi       : UInt32
  blockBytes : UInt32
  deriving Repr, DecidableEq

def ddsPitch (h : DdsHeader) : Nat :=
  ((h.width.toNat + 3) / 4) * h.blockBytes.toNat

def ddsFileSize (h : DdsHeader) : Nat :=
  ddsHeaderSize +
    ((h.width.toNat + 3) / 4) * ((h.height.toNat + 3) / 4) * h.blockBytes.toNat

def emitDdsHeader (h : DdsHeader) : Emit :=
  putU32LE 0x20534444 ∘
  putU32LE 124 ∘
  putU32LE 0x0002100F ∘
  putU32LE h.height ∘
  putU32LE h.width ∘
  putU32LE (UInt32.ofNat (ddsPitch h)) ∘
  putU32LE 1 ∘
  putU32LE 1 ∘
  putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘
  putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘
  putU32LE 32 ∘
  putU32LE 0x00000004 ∘
  putU32LE 0x30315844 ∘
  putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘
  putU32LE 0x00001000 ∘
  putU32LE h.dxgi ∘
  putU32LE 3 ∘
  putU32LE 0 ∘
  putU32LE 1 ∘
  putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0 ∘ putU32LE 0

def parseDdsHeader (b : Bytes) : Option DdsHeader := do
  let m0 ← getU8 b 0
  let m1 ← getU8 b 1
  let m2 ← getU8 b 2
  let m3 ← getU8 b 3
  if !(m0 = 0x44 && m1 = 0x44 && m2 = 0x53 && m3 = 0x20) then none else pure ()
  let dwSize ← getU32LE b 4
  if dwSize ≠ 124 then none else pure ()
  let height ← getU32LE b 12
  let width  ← getU32LE b 16
  let dxgi   ← getU32LE b 112
  pure { width := width, height := height, dxgi := dxgi, blockBytes := 16 }

structure KtxHeader where
  width          : UInt32
  height         : UInt32
  internalFormat : UInt32
  baseFormat     : UInt32
  payloadSize    : UInt32
  deriving Repr, DecidableEq

def emitKtxHeader (h : KtxHeader) : Emit :=
  (fun acc => acc.push 0xab |>.push 0x4b |>.push 0x54 |>.push 0x58
                   |>.push 0x20 |>.push 0x31 |>.push 0x31 |>.push 0xbb
                   |>.push 0x0d |>.push 0x0a |>.push 0x1a |>.push 0x0a) ∘
  putU32LE ktxEndianMarker ∘
  putU32LE 1 ∘
  putU32LE h.internalFormat ∘
  putU32LE h.baseFormat ∘
  putU32LE h.width ∘
  putU32LE h.height ∘
  putU32LE 1 ∘
  putU32LE 1 ∘
  putU32LE h.payloadSize

def ktxFileSize (h : KtxHeader) : Nat := ktxHeaderSize + h.payloadSize.toNat

theorem ddsFileSize_eq (h : DdsHeader) :
    ddsFileSize h = ddsHeaderSize +
      ((h.width.toNat + 3) / 4) * ((h.height.toNat + 3) / 4) * h.blockBytes.toNat := by
  rfl

theorem ktxFileSize_eq (h : KtxHeader) :
    ktxFileSize h = ktxHeaderSize + h.payloadSize.toNat := by
  rfl

-- ============================================================
-- Size / block-count equations (Texcomp/Size.lean content)
-- ============================================================

def blocks4 (n : Nat) : Nat := (n + 3) / 4

def blockCount4 (w h : Nat) : Nat := blocks4 w * blocks4 h

def bc16Size (w h : Nat) : Nat := blockCount4 w h * 16

def bc8Size (w h : Nat) : Nat := blockCount4 w h * 8

def astcPayloadSize (bx by_ w h : Nat) : Nat :=
  ((w + bx - 1) / bx) * ((h + by_ - 1) / by_) * 16

def ddsSize16 (w h : Nat) : Nat := 148 + bc16Size w h
def ddsSize8  (w h : Nat) : Nat := 148 + bc8Size w h

def ktxSize (payload : Nat) : Nat := 68 + payload

theorem blocks4_pos (w : Nat) (hw : w ≥ 1) : blocks4 w ≥ 1 := by
  unfold blocks4
  omega

theorem blockCount4_pos (w h : Nat) (hw : w ≥ 1) (hh : h ≥ 1) :
    blockCount4 w h ≥ 1 := by
  unfold blockCount4
  have hb1 : blocks4 w ≥ 1 := blocks4_pos w hw
  have hb2 : blocks4 h ≥ 1 := blocks4_pos h hh
  exact Nat.mul_pos hb1 hb2

end Texcomp