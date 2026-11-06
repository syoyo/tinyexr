/-
  TinyEXR - Lean 4 formalization of the OpenEXR file format.

  Byte-level emitters for the structural model: attributes, headers, the
  magic/version prefix and chunk-offset tables. Pixel payloads are emitted
  verbatim by the caller.

  The emitters are total and produce exactly the layout the parser expects
  (`Exr.Parse`), which is the statement `parse_emitHeader` is about.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/

import Exr.Parse

namespace Exr

namespace Emit

/-- A NUL byte. -/
def nulByte : Bytes := ByteArray.mk #[0]

/-- Little-endian 4-byte encoding of a natural number. -/
def u32Bytes (n : Nat) : Bytes :=
  (putU32LE (UInt32.ofNat n) ByteArray.empty)

/-- Little-endian 8-byte encoding of a natural number. -/
def u64Bytes (n : Nat) : Bytes :=
  (putU64LE (UInt64.ofNat n) ByteArray.empty)

/-- Emit a raw attribute: name NUL type NUL size(u32) value. -/
def attrBytes (a : RawAttr) : Bytes :=
  a.name ++ nulByte ++ a.typeName ++ nulByte ++ u32Bytes a.value.size ++ a.value

/-- Emit a header: all attributes plus the end-of-header NUL byte. -/
def headerBytes (attrs : List RawAttr) : Bytes :=
  attrs.foldl (fun acc a => acc ++ attrBytes a) ByteArray.empty ++ nulByte

/-- Emit `n` offset-table entries (absolute file offsets). -/
def offsetTableBytes (offsets : List Nat) : Bytes :=
  offsets.foldl (fun acc o => acc ++ u64Bytes o) ByteArray.empty

/-- Emit the magic number and version field. -/
def magicVersionBytes (v : Version) : Bytes :=
  (putU32LE magicUInt32LE ByteArray.empty) ++ u32Bytes v.toBits.toNat

/-- Emit the complete structural prefix of a file: magic + version +
    headers (with the multi-part terminator) + offset tables.

    Returns the bytes; pixel payloads follow at `dataStart`. -/
def filePrefix (f : ParsedFile) : Bytes :=
  let headers := f.parts.foldl (fun acc h => acc ++ headerBytes h.attrs) ByteArray.empty
  let headers := if f.version.multipart then headers ++ nulByte else headers
  let tables := f.offsetTables.foldl (fun acc t => acc ++ offsetTableBytes t.offsets)
    ByteArray.empty
  magicVersionBytes f.version ++ headers ++ tables

end Emit

end Exr
