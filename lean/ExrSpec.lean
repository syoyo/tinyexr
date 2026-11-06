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
