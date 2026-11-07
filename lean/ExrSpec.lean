/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Root module for the `ExrSpec` library. Importing this module pulls in the
  whole formalization (byte layer, version field, attributes, file model,
  codecs) once those modules land.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Bytes
import Exr.Version
import Exr.Attribute
import Exr.Tiles
import Exr.File
import Exr.Parse
import Exr.Emit
import Exr.Size
import Exr.Deep
import Exr.Rle
import Exr.Zip
import Exr.TypedEmit

import Exr.Chunk

import Exr.Piz

import Exr.PizTraversal
import Exr.PizWavelet
import Exr.PizDisjoint
import Exr.PizWaveletInverse
import Exr.PizSmallRange
import Exr.PizComposition
import Exr.PizReconstruct
import Exr.PizDecodePacket
import Exr.PizBitmap
import Exr.PizBitmapSpan
import Exr.PizFrameEmit
import Exr.PizRoundtrip

import Exr.PizHeap
import Exr.PizKraft
import Exr.PizLengthTable
import Exr.PizFrequencySource
import Exr.PizHistogram
import Exr.PizWireBounds
import Exr.PizGeneratedRoundtrip

import Exr.PizBits
import Exr.PizTable

import Exr.PizCodebook
import Exr.PizEntropy
import Exr.PizPacket
import Exr.PizPacketEmit
import Exr.PizLayout
import Exr.PizBlock

import Exr.PizCodebookTotal
import Exr.PizCanonicalMass
import Exr.PizCanonicalWords
