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
import Exr.TypedEmit

namespace Exr

namespace Emit

/-- A NUL byte. -/
def nulByte : Bytes := ByteArray.mk #[0]

theorem nulByte_size_emit : (nulByte).size = 1 := rfl

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

/-- The emitted attribute bytes are exactly the wire form used by the
    attribute-layer proofs. -/
theorem attrBytes_eq_wire (a : RawAttr) : attrBytes a = RawAttr.wire a := by
  simp only [attrBytes, RawAttr.wire, u32Bytes, ByteArray.append_assoc]
  rfl

/-- The emitted header bytes are exactly the emitted attribute list plus the
    end-of-header NUL byte. -/
theorem headerBytes_eq_wireAll (attrs : List RawAttr) :
    headerBytes attrs = RawAttr.wireAll attrs ++ nulByte := by
  unfold headerBytes
  have h : (fun acc a => acc ++ attrBytes a) = (fun acc a => acc ++ RawAttr.wire a) := by
    funext acc
    funext a
    rw [attrBytes_eq_wire]
  rw [h, RawAttr.foldl_wireAll, ByteArray.empty_append]

end Emit

namespace Emit

/-- Emit the offset tables of every part. -/
def tablesBytes (ts : List OffsetTable) : Bytes :=
  ts.foldl (fun acc t => acc ++ offsetTableBytes t.offsets) ByteArray.empty

/-- The emitted tables region has the expected size. -/
theorem tablesBytes_size (ts : List OffsetTable) :
    (tablesBytes ts).size = 8 * (ts.map fun t => t.offsets.length).sum := by
  unfold tablesBytes
  -- generalize over the accumulator
  have key : ∀ (acc : Bytes), (ts.foldl (fun acc t => acc ++ offsetTableBytes t.offsets) acc).size
      = acc.size + 8 * (ts.map fun t => t.offsets.length).sum := by
    induction ts with
    | nil => intro acc; simp
    | cons t ts ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have hos : (offsetTableBytes t.offsets).size = 8 * t.offsets.length := by
        have key2 : ∀ (os : List Nat) (acc : Bytes),
            (os.foldl (fun acc o => acc ++ u64Bytes o) acc).size
              = acc.size + 8 * os.length := by
          intro os
          induction os with
          | nil => intro acc; simp
          | cons o os ih =>
            intro acc
            simp only [List.foldl_cons]
            rw [ih (acc ++ u64Bytes o), ByteArray.size_append, List.length_cons]
            have hos2 : (u64Bytes o).size = 8 := by
              simp [u64Bytes, putU64LE]
            omega
        rw [offsetTableBytes, key2 t.offsets ByteArray.empty, ByteArray.size_empty]
        omega
      rw [ih (acc ++ offsetTableBytes t.offsets), ByteArray.size_append, hos]
      omega
  rw [key ByteArray.empty, ByteArray.size_empty]
  omega


/-- Encoded `chlist` value of a header's channels. -/
def chlistOf (h : Header) : Bytes :=
  (h.channels.foldl (fun acc c =>
      acc ++ c.name ++ nulByte ++ u32Bytes c.pixelType.toBits.toNat
        ++ ByteArray.mk #[0, 0, 0, 0]
        ++ u32Bytes c.xSampling.toInt.toNat
        ++ u32Bytes c.ySampling.toInt.toNat) ByteArray.empty)
    ++ nulByte

/-- Encoded `box2i` value. -/
def box2iOf (b : Box2i) : Bytes :=
  u32Bytes b.minX.toUInt32.toNat ++ u32Bytes b.minY.toUInt32.toNat
    ++ u32Bytes b.maxX.toUInt32.toNat ++ u32Bytes b.maxY.toUInt32.toNat

/-- One emitted attribute with string name/type. -/
def attr (name ty : String) (v : Bytes) : RawAttr :=
  { name := name.toUTF8, typeName := ty.toUTF8, value := v }

/-- Size of a one-byte `mk` array. -/
theorem mk1_size (x : UInt8) : (ByteArray.mk #[x]).size = 1 := rfl

/-- The eight always-present attributes of a part header. -/
def baseAttrs (h : Header) : List RawAttr :=
  [ attr "channels" "chlist" (chlistOf h),
    attr "compression" "compression" (ByteArray.mk #[h.compression.toBits]),
    attr "dataWindow" "box2i" (box2iOf h.dataWindow),
    attr "displayWindow" "box2i" (box2iOf h.displayWindow),
    attr "lineOrder" "lineOrder" (ByteArray.mk #[h.lineOrder.toBits]),
    attr "pixelAspectRatio" "float" (u32Bytes h.pixelAspectRatio.toNat),
    attr "screenWindowCenter" "v2f"
      (u32Bytes h.screenWindowCenterX.toNat
        ++ u32Bytes h.screenWindowCenterY.toNat),
    attr "screenWindowWidth" "float" (u32Bytes h.screenWindowWidth.toNat) ]

/-- `baseAttrs` plus the `tiles` attribute when a tile descriptor is present. -/
def withTiles (h : Header) : List RawAttr :=
  match h.tileDesc with
  | some td =>
    let lm : Nat := match td.levelMode with
      | .oneLevel => 0
      | .mipmap => 1
      | .ripmap => 2
    let rm : Nat := match td.roundingMode with
      | .roundDown => 0
      | .roundUp => 1
    baseAttrs h ++ [ attr "tiles" "tiledesc"
      (u32Bytes td.xSize ++ u32Bytes td.ySize
        ++ ByteArray.mk #[UInt8.ofNat (lm ||| rm <<< 4)]) ]
  | none => baseAttrs h

/-- Plus the declaring `chunkCount` when present. -/
def withChunkCount (h : Header) : List RawAttr :=
  match h.chunkCount with
  | some n => withTiles h ++ [ attr "chunkCount" "int" (u32Bytes n) ]
  | none => withTiles h

/-- Plus the part `name` when present. -/
def withName (h : Header) : List RawAttr :=
  match h.name with
  | some n => withChunkCount h ++ [ attr "name" "string" n ]
  | none => withChunkCount h

/-- Plus the `version` attribute for deep parts. -/
def withVersion (h : Header) : List RawAttr :=
  if h.partType.isDeep then withName h ++ [ attr "version" "int" (u32Bytes 1) ]
  else withName h

/-- Plus `maxSamplesPerPixel` when known. -/
def withMaxSamples (h : Header) : List RawAttr :=
  match h.maxSamplesPerPixel with
  | some m =>
    withVersion h ++ [ attr "maxSamplesPerPixel" "int" (u32Bytes m.toInt.toNat) ]
  | none => withVersion h

/-- Build the attribute list of a part header (canonical encoder). Multi-part
    and deep parts additionally carry the `type` attribute. -/
def headerAttrs (h : Header) (multipart : Bool) : List RawAttr :=
  if multipart || h.partType.isDeep then
    withMaxSamples h ++ [ attr "type" "string" (h.partType.wireName.toUTF8) ]
  else withMaxSamples h

/-- Size of a `u32Bytes` encoding. -/
theorem u32Bytes_size_emit (n : Nat) : (u32Bytes n).size = 4 := by
  simp [u32Bytes, putU32LE]

/-- Size of an encoded `box2i`. -/
theorem box2iOf_size (b : Box2i) : (box2iOf b).size = 16 := by
  unfold box2iOf
  simp [u32Bytes_size_emit]

/-- Size of an encoded `chlist`. -/
theorem chlistOf_size (h : Header) :
    (chlistOf h).size
      = (h.channels.map fun c => c.name.size + 17).sum + 1 := by
  unfold chlistOf
  have key : ∀ (cs : List Channel) (acc : Bytes),
      (cs.foldl (fun acc c =>
          acc ++ c.name ++ nulByte ++ u32Bytes c.pixelType.toBits.toNat
            ++ ByteArray.mk #[0, 0, 0, 0]
            ++ u32Bytes c.xSampling.toInt.toNat
            ++ u32Bytes c.ySampling.toInt.toNat) acc).size
        = acc.size + (cs.map fun c => c.name.size + 17).sum := by
    intro cs
    induction cs with
    | nil => intro acc; simp
    | cons c cs ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (acc ++ c.name ++ nulByte ++ u32Bytes c.pixelType.toBits.toNat
            ++ ByteArray.mk #[0, 0, 0, 0]
            ++ u32Bytes c.xSampling.toInt.toNat
            ++ u32Bytes c.ySampling.toInt.toNat)]
      have hmk : (ByteArray.mk #[0, 0, 0, 0] : Bytes).size = 4 := by decide
      have hn : (nulByte).size = 1 := by decide
      simp only [ByteArray.size_append, hn, u32Bytes_size_emit, hmk]
      omega
  have hn : (nulByte).size = 1 := by decide
  have he : (ByteArray.empty : Bytes).size = 0 := rfl
  rw [ByteArray.size_append, key h.channels ByteArray.empty, hn, he]
  omega



/-- One encoded `chlist` entry (canonical form must have pLinear = false). -/
def encChannel (c : Channel) : Bytes :=
  c.name ++ nulByte ++ u32Bytes c.pixelType.toBits.toNat
    ++ ByteArray.mk #[0, 0, 0, 0]
    ++ u32Bytes c.xSampling.toInt.toNat
    ++ u32Bytes c.ySampling.toInt.toNat

def encChlist (cs : List Channel) : Bytes :=
  cs.foldr (fun c acc => encChannel c ++ acc) nulByte

theorem encChlist_nil : encChlist [] = nulByte := rfl

theorem encChlist_cons (c : Channel) (cs : List Channel) :
    encChlist (c :: cs) = encChannel c ++ encChlist cs := rfl

theorem encChannel_size (c : Channel) :
    (encChannel c).size = c.name.size + 17 := by
  unfold encChannel
  simp only [ByteArray.size_append, u32Bytes_size_emit]
  have hmk : (ByteArray.mk #[0, 0, 0, 0] : Bytes).size = 4 := by decide
  have hn : (nulByte).size = 1 := by decide
  simp only [hmk, hn]

theorem encChlist_size (cs : List Channel) :
    (encChlist cs).size = (cs.map fun c => c.name.size + 17).sum + 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [encChlist_cons, ByteArray.size_append, encChannel_size, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The canonical encoded channel list of a header. -/
theorem chlistOf_eq_encChlist (h : Header) :
    chlistOf h = encChlist h.channels := by
  unfold chlistOf
  have hf : (fun acc c => acc ++ c.name ++ nulByte ++ u32Bytes c.pixelType.toBits.toNat
        ++ ByteArray.mk #[0, 0, 0, 0]
        ++ u32Bytes c.xSampling.toInt.toNat
        ++ u32Bytes c.ySampling.toInt.toNat)
      = (fun acc c => acc ++ encChannel c) := by
    funext acc c
    simp [encChannel, ByteArray.append_assoc]
  rw [hf, foldl_append_eq_foldr]
  have hgen : ∀ (cs : List Channel) (b : Bytes),
      (cs.foldr (fun a acc' => encChannel a ++ acc') ByteArray.empty ++ b)
        = cs.foldr (fun a acc' => encChannel a ++ acc') b := by
    intro cs b
    induction cs generalizing b with
    | nil => simp
    | cons c cs ih => simp [List.foldr_cons, ih, ByteArray.append_assoc]
  simp only [ByteArray.empty_append]
  rw [hgen]
  simp [encChlist]

/-- A channel that the canonical encoder round-trips. -/
def ChannelOK (c : Channel) : Prop :=
  1 ≤ c.name.size ∧ RawAttr.NoNul c.name ∧ 1 ≤ c.xSampling.toInt ∧
    1 ≤ c.ySampling.toInt ∧ c.pLinear = false


/-- The canonical encoded `chlist` parses back to the original channel list
    (with any accumulator appended). Prefix/suffix-aware: any bytes before
    and after the encoded list are skipped. -/
theorem decodeChlistFuel_encode (cs : List Channel) (p rest : Bytes) (fuel : Nat)
    (acc : List Channel) (hOK : ∀ c ∈ cs, ChannelOK c) (hf : cs.length + 1 ≤ fuel) :
    TypedAttr.decodeChlistFuel (p ++ (encChlist cs ++ rest)) p.size fuel acc =
      some (cs ++ acc, p.size + (encChlist cs).size) := by
  induction cs generalizing p fuel acc with
  | nil =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    unfold TypedAttr.decodeChlistFuel
    have heq : encChlist ([] : List Channel) ++ rest = RawAttr.nulByte ++ rest := rfl
    rw [heq, RawAttr.getU8?_nul_at (p := p) (rest := rest)]
    rfl
  | cons c cs ih =>
    have hOK' : ∀ t ∈ cs, ChannelOK t := by
      intro t ht
      exact hOK t (List.mem_cons_of_mem c ht)
    obtain ⟨nm, pt, pl, xs, ys⟩ := c
    have hOKc := hOK (⟨nm, pt, pl, xs, ys⟩ : Channel) (by simp)
    obtain ⟨hlen, hnn, hxp, hyp, hplf⟩ := hOKc
    subst hplf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    -- the bytes: channel frame then the rest of the list
    have hB : p ++ (encChlist ((⟨nm, pt, false, xs, ys⟩ : Channel) :: cs) ++ rest)
        = p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
            (ByteArray.mk #[0, 0, 0, 0] ++
             (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest))))))) := by
      simp [encChlist_cons, encChannel, ByteArray.append_assoc]
    rw [hB]
    unfold TypedAttr.decodeChlistFuel
    -- head byte of the channel name
    have hnm : 0 < nm.size := hlen
    have hg8 : getU8? (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) p.size
        = some (nm[0]'hnm) := by
      rw [show p.size = p.size + 0 by omega, getU8?_append_right' (a := p) (b := nm ++ _) (k := 0),
        getU8?_append_left (a := nm) (i := 0) hnm, getU8?_of_lt hnm]
    have hnz : (nm[0]'hnm) ≠ 0 := by
      have h := hnn 0
      rw [getU8?_of_lt hnm] at h
      intro hc
      exact h (congrArg some hc)
    simp only [hg8, show ((nm[0]'hnm) == 0) = false from by
      rw [beq_eq_false_iff_ne]; exact hnz]
    -- name cstring
    have hname : readCString (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) p.size
        = some (nm, p.size + nm.size + 1) := by
      have hnln : RawAttr.nulByte = nulByte := rfl
      rw [← hnln]
      exact RawAttr.readCString_emit_at (p := p) (s := nm)
        (rest := u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest))))) hnn
    simp only [hname]
    -- prefixes P2..P5 of the byte string, with B split at each read point
    set P2 : Bytes := p ++ nm ++ nulByte with hP2
    set P3 : Bytes := P2 ++ u32Bytes pt.toBits.toNat with hP3
    set P4 : Bytes := P3 ++ ByteArray.mk #[0, 0, 0, 0] with hP4
    set P5 : Bytes := P4 ++ u32Bytes xs.toInt.toNat with hP5
    have hB5 : p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))
        = P5 ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)) := by
      simp [hP2, hP3, hP4, hP5, ByteArray.append_assoc]
    have hsz2 : P2.size = p.size + nm.size + 1 := by
      rw [hP2]
      simp only [ByteArray.size_append]
      have hn : (nulByte).size = 1 := by decide
      rw [hn]
    have hsz3 : P3.size = p.size + nm.size + 1 + 4 := by
      rw [hP3, ByteArray.size_append, hsz2, u32Bytes_size_emit]
    have hsz4 : P4.size = p.size + nm.size + 1 + 4 + 4 := by
      rw [hP4, ByteArray.size_append, hsz3]
      have hmk : (ByteArray.mk #[0, 0, 0, 0] : Bytes).size = 4 := by decide
      rw [hmk]
    have hsz5 : P5.size = p.size + nm.size + 1 + 4 + 4 + 4 := by
      rw [hP5, ByteArray.size_append, hsz4, u32Bytes_size_emit]
    -- pixel type at P2.size
    have hpt : getU32LE (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) (p.size + nm.size + 1)
        = some pt.toBits := by
      have hB2 : p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
            (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))
          = P2 ++ (u32Bytes pt.toBits.toNat ++
              (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest))))) := by
        simp [hP2, ByteArray.append_assoc]
      rw [hB2, ← hsz2, getU32LE_append_right]
      rw [getU32LE_append_left (a := u32Bytes pt.toBits.toNat)
            (b := ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))) (i := 0) (by rw [u32Bytes_size_emit])]
      rw [show u32Bytes pt.toBits.toNat = putU32LE (UInt32.ofNat pt.toBits.toNat) ByteArray.empty from rfl,
          show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE]
      rw [UInt32.ofNat_toNat]
    simp only [hpt, PixelType.ofBits_toBits]
    -- pLinear and reserved bytes
    have hbyte : ∀ (k : Nat) (hk : k < 4),
        getU8? (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) (p.size + nm.size + 1 + 4 + k)
          = some 0 := by
      intro k hk
      have hB3 : p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
            (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))
          = P3 ++ (ByteArray.mk #[0, 0, 0, 0] ++
              (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))) := by
        simp [hP2, hP3, ByteArray.append_assoc]
      rw [hB3]
      have hidx : p.size + nm.size + 1 + 4 + k = P3.size + k := by
        rw [hsz3]
      rw [hidx, getU8?_append_right' (a := P3) (b := _) (k := k),
        getU8?_append_left (a := ByteArray.mk #[0, 0, 0, 0])
            (b := u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest))) (i := k)
            (by have hmk : (ByteArray.mk #[0, 0, 0, 0] : Bytes).size = 4 := by decide
                rw [hmk]
                omega)]
      have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk4 with rfl | rfl | rfl | rfl <;> decide
    simp only [hbyte 0 (by omega), hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega),
      show ((0 : UInt8) != 0 || (0 : UInt8) != 0 || (0 : UInt8) != 0) = false from rfl]
    simp only [show ((0 : UInt8) != 0 && (0 : UInt8) != 1) = false from rfl]
    -- samplings
    have hxs : getU32LE (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) (p.size + nm.size + 1 + 8)
        = some (UInt32.ofNat xs.toInt.toNat) := by
      have hB4 : p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
            (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))
          = P4 ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest))) := by
        simp [hP2, hP3, hP4, ByteArray.append_assoc]
      rw [hB4]
      have hidx : p.size + nm.size + 1 + 8 = P4.size := by rw [hsz4]
      rw [hidx, getU32LE_append_right]
      rw [getU32LE_append_left (a := u32Bytes xs.toInt.toNat)
            (b := u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)) (i := 0) (by rw [u32Bytes_size_emit])]
      rw [show u32Bytes xs.toInt.toNat = putU32LE (UInt32.ofNat xs.toInt.toNat) ByteArray.empty from rfl,
          show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE]
    have hys : getU32LE (p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))) (p.size + nm.size + 1 + 12)
        = some (UInt32.ofNat ys.toInt.toNat) := by
      rw [hB5]
      have hidx : p.size + nm.size + 1 + 12 = P5.size := by rw [hsz5]
      rw [hidx, getU32LE_append_right]
      rw [getU32LE_append_left (a := u32Bytes ys.toInt.toNat)
            (b := encChlist cs ++ rest) (i := 0) (by rw [u32Bytes_size_emit])]
      rw [show u32Bytes ys.toInt.toNat = putU32LE (UInt32.ofNat ys.toInt.toNat) ByteArray.empty from rfl,
          show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE]
    have hxsame : (UInt32.ofNat xs.toInt.toNat).toInt32 = xs :=
      Int32_ofNat_toNat_toInt32 xs hxp
    have hysame : (UInt32.ofNat ys.toInt.toNat).toInt32 = ys :=
      Int32_ofNat_toNat_toInt32 ys hyp
    have hxpos : ¬ (xs ≤ 0) := by
      have hxp' : 1 ≤ xs.toInt := hxp
      rw [Int32.le_iff_toInt_le]
      have h0 : (0 : Int32).toInt = 0 := rfl
      rw [h0]
      omega
    have hypos : ¬ (ys ≤ 0) := by
      have hyp' : 1 ≤ ys.toInt := hyp
      rw [Int32.le_iff_toInt_le]
      have h0 : (0 : Int32).toInt = 0 := rfl
      rw [h0]
      omega
    simp only [hxs, hys, hxsame, hysame, decide_eq_false hxpos, decide_eq_false hypos,
      show (false || false : Bool) = false from rfl]
    -- tail recursion
    have htail : p ++ (nm ++ (nulByte ++ (u32Bytes pt.toBits.toNat ++
          (ByteArray.mk #[0, 0, 0, 0] ++ (u32Bytes xs.toInt.toNat ++ (u32Bytes ys.toInt.toNat ++ (encChlist cs ++ rest)))))))
        = (p ++ encChannel (⟨nm, pt, false, xs, ys⟩ : Channel)) ++ (encChlist cs ++ rest) := by
      simp [encChannel, ByteArray.append_assoc]
    rw [htail]
    have hidx' : (p ++ encChannel (⟨nm, pt, false, xs, ys⟩ : Channel)).size
        = p.size + (nm.size + 17) := by
      rw [ByteArray.size_append, encChannel_size]
    have hidx : p.size + nm.size + 1 + 16 = (p ++ encChannel (⟨nm, pt, false, xs, ys⟩ : Channel)).size := by
      rw [hidx']
      omega
    rw [hidx]
    have hfn : cs.length + 1 ≤ n := by
      simp only [List.length_cons] at hf
      omega
    have ih' := ih (p := p ++ encChannel (⟨nm, pt, false, xs, ys⟩ : Channel)) (fuel := n) (acc := acc) hOK' hfn
    simp only [ih']
    have hsz1 : (p ++ encChannel (⟨nm, pt, false, xs, ys⟩ : Channel)).size
        = p.size + ((⟨nm, pt, false, xs, ys⟩ : Channel).name.size + 17) := by
      rw [ByteArray.size_append, encChannel_size]
    rw [hsz1, encChlist_cons, ByteArray.size_append, encChannel_size]
    congr 1
    congr 1
    omega

/-- An emitted attribute with literal short name/type and a small value is
    always well-formed for the short-name limit. -/
theorem attr_emittable (name ty : String) (v : Bytes)
    (hn1 : 1 ≤ name.toUTF8.size) (hn2 : name.toUTF8.size ≤ 31)
    (hn3 : RawAttr.NoNul name.toUTF8)
    (ht1 : 1 ≤ ty.toUTF8.size) (ht2 : ty.toUTF8.size ≤ 31)
    (ht3 : RawAttr.NoNul ty.toUTF8)
    (hv : v.size < 2 ^ 31) : RawAttr.Emittable (attr name ty v) 31 :=
  ⟨hn1, hn2, hn3, ht1, ht2, ht3, hv⟩

/-- The canonical attribute list is always well-formed (for the short-name
    limit 31): names/types are short fixed strings, values are small except
    `chlist`, which needs the channel count/name-size bound. -/
theorem headerAttrs_emittable (h : Header) (multipart : Bool)
    (hChLen : h.channels.length ≤ 2 ^ 20)
    (hChName : ∀ c ∈ h.channels, c.name.size ≤ 255)
    (hName : ∀ n, h.name = some n → n.size ≤ 255) :
    ∀ a ∈ headerAttrs h multipart, RawAttr.Emittable a 31 := by
  have hChlist : (chlistOf h).size < 2 ^ 31 := by
    rw [chlistOf_size]
    have hsum : ∀ cs : List Channel, (∀ c ∈ cs, c.name.size ≤ 255) →
        (cs.map fun c => c.name.size + 17).sum ≤ cs.length * 272 := by
      intro cs
      induction cs with
      | nil => intro _; simp
      | cons c cs ih =>
        intro hc
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have h1 := ih (fun t ht => hc t (List.mem_cons_of_mem c ht))
        have h2 := hc c (by simp)
        omega
    have h1 := hsum h.channels hChName
    have hle : h.channels.length * 272 ≤ 2 ^ 20 * 272 := by
      apply Nat.mul_le_mul_right
      exact hChLen
    omega
  have hBase : ∀ a ∈ baseAttrs h, RawAttr.Emittable a 31 := by
    intro a ha
    simp only [baseAttrs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide)) hChlist
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by rw [show (ByteArray.mk #[h.compression.toBits]).size = 1 from rfl]; omega)
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide)) (by rw [box2iOf_size]; omega)
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide)) (by rw [box2iOf_size]; omega)
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by rw [show (ByteArray.mk #[h.lineOrder.toBits]).size = 1 from rfl]; omega)
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by rw [u32Bytes_size_emit]; omega)
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by simp [u32Bytes_size_emit])
    · exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
        (by rw [u32Bytes_size_emit]; omega)
  have hTiles : ∀ a ∈ withTiles h, RawAttr.Emittable a 31 := by
    intro a ha
    unfold withTiles at ha
    cases ht : h.tileDesc with
    | none => rw [ht] at ha; exact hBase a ha
    | some td =>
      rw [ht, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hBase a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by simp only [ByteArray.size_append, u32Bytes_size_emit, mk1_size]; omega)
  have hChunk : ∀ a ∈ withChunkCount h, RawAttr.Emittable a 31 := by
    intro a ha
    unfold withChunkCount at ha
    cases hc : h.chunkCount with
    | none => rw [hc] at ha; exact hTiles a ha
    | some n =>
      rw [hc, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hTiles a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by rw [u32Bytes_size_emit]; omega)
  have hName' : ∀ a ∈ withName h, RawAttr.Emittable a 31 := by
    intro a ha
    unfold withName at ha
    cases hn : h.name with
    | none => rw [hn] at ha; exact hChunk a ha
    | some n =>
      rw [hn, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hChunk a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by have := hName n hn; omega)
  have hVersion : ∀ a ∈ withVersion h, RawAttr.Emittable a 31 := by
    intro a ha
    unfold withVersion at ha
    split at ha
    · rename_i hd
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hName' a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by rw [u32Bytes_size_emit]; omega)
    · exact hName' a ha
  have hMax : ∀ a ∈ withMaxSamples h, RawAttr.Emittable a 31 := by
    intro a ha
    unfold withMaxSamples at ha
    cases hm : h.maxSamplesPerPixel with
    | none => rw [hm] at ha; exact hVersion a ha
    | some m =>
      rw [hm, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hVersion a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by rw [u32Bytes_size_emit]; omega)
  intro a ha
  unfold headerAttrs at ha
  split at ha
  · rename_i hmp
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hMax a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [ha]
      cases h.partType <;>
        exact attr_emittable _ _ _ (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide))
          (by decide) (by decide) (RawAttr.NoNul.of_bound (by decide)) (by decide)
  · exact hMax a ha


/-! ## Bridge lemmas to the typed encoders/decoders (`Exr.TypedEmit`) -/

theorem box2iOf_eq_encBox2i (b : Box2i) : box2iOf b = encBox2i b := by
  simp [box2iOf, encBox2i, u32Bytes, u32Words, ByteArray.append_assoc]

theorem u32Bytes_eq_u32Words (x : UInt32) : u32Bytes x.toNat = u32Words [x] := by
  simp [u32Bytes, u32Words]

theorem u32Bytes_append_eq_u32Words (x y : UInt32) :
    u32Bytes x.toNat ++ u32Bytes y.toNat = u32Words [x, y] := by
  simp [u32Bytes, u32Words]

theorem decodeInt_u32Bytes (n : Nat) :
    TypedAttr.decodeInt (u32Bytes n) = some (Int32.ofNat n) := by
  unfold TypedAttr.decodeInt
  rw [u32Bytes_size_emit]
  simp
  show ((getU32LE (putU32LE (UInt32.ofNat n) ByteArray.empty) 0).bind fun v => some v.toInt32) = some (Int32.ofNat n)
  rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE, Option.bind_some]
  simp

/-- The canonical encoded `tiles` value equals `encTileDesc`. -/
theorem tileBytes_eq_encTileDesc (t : TypedAttr.TileDesc) :
    u32Bytes t.xSize ++ u32Bytes t.ySize ++
      ByteArray.mk #[UInt8.ofNat ((match t.levelMode with
        | .oneLevel => 0 | .mipmap => 1 | .ripmap => 2) ||| (match t.roundingMode with
        | .roundDown => 0 | .roundUp => 1) <<< 4)]
    = encTileDesc t := by
  obtain ⟨x, y, lm, rm⟩ := t
  cases lm <;> cases rm <;>
    simp [encTileDesc, encLevelMode, encRoundingMode, u32Bytes, u32Words,
          ByteArray.append_assoc] <;> rfl

/-- The whole encoded `chlist` value parses back to the channel list. -/
theorem decodeChlist_encChlist (cs : List Channel) (hOK : ∀ c ∈ cs, ChannelOK c) :
    TypedAttr.decodeChlist (encChlist cs) = some (cs, (encChlist cs).size) := by
  unfold TypedAttr.decodeChlist
  have hge : cs.length + 1 ≤ (encChlist cs).size + 1 := by
    rw [encChlist_size]
    have hsum : ∀ cs : List Channel, cs.length ≤ (cs.map fun c => c.name.size + 17).sum := by
      intro cs
      induction cs with
      | nil => simp
      | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
    have := hsum cs
    omega
  have h := decodeChlistFuel_encode cs ByteArray.empty ByteArray.empty
    ((encChlist cs).size + 1) [] hOK hge
  simpa using h


/-! ## `findAttr` over the emitted attribute lists -/

theorem findAttr_append {l l' : List RawAttr} {n : String} :
    Parse.findAttr (l ++ l') n = (Parse.findAttr l n).or (Parse.findAttr l' n) := by
  simp [Parse.findAttr, List.find?_append]

theorem findAttr_append_some {l l' : List RawAttr} {n : String} {a : RawAttr}
    (h : Parse.findAttr l n = some a) : Parse.findAttr (l ++ l') n = some a := by
  rw [findAttr_append, h]
  rfl

theorem findAttr_base_channels (h : Header) :
    Parse.findAttr (baseAttrs h) "channels"
      = some (attr "channels" "chlist" (chlistOf h)) := rfl

theorem findAttr_base_compression (h : Header) :
    Parse.findAttr (baseAttrs h) "compression"
      = some (attr "compression" "compression" (ByteArray.mk #[h.compression.toBits])) := rfl

theorem findAttr_base_dataWindow (h : Header) :
    Parse.findAttr (baseAttrs h) "dataWindow"
      = some (attr "dataWindow" "box2i" (box2iOf h.dataWindow)) := rfl

theorem findAttr_base_displayWindow (h : Header) :
    Parse.findAttr (baseAttrs h) "displayWindow"
      = some (attr "displayWindow" "box2i" (box2iOf h.displayWindow)) := rfl

theorem findAttr_base_lineOrder (h : Header) :
    Parse.findAttr (baseAttrs h) "lineOrder"
      = some (attr "lineOrder" "lineOrder" (ByteArray.mk #[h.lineOrder.toBits])) := rfl

theorem findAttr_base_pixelAspectRatio (h : Header) :
    Parse.findAttr (baseAttrs h) "pixelAspectRatio"
      = some (attr "pixelAspectRatio" "float" (u32Bytes h.pixelAspectRatio.toNat)) := rfl

theorem findAttr_base_screenWindowCenter (h : Header) :
    Parse.findAttr (baseAttrs h) "screenWindowCenter"
      = some (attr "screenWindowCenter" "v2f"
          (u32Bytes h.screenWindowCenterX.toNat ++ u32Bytes h.screenWindowCenterY.toNat)) := rfl

theorem findAttr_base_screenWindowWidth (h : Header) :
    Parse.findAttr (baseAttrs h) "screenWindowWidth"
      = some (attr "screenWindowWidth" "float" (u32Bytes h.screenWindowWidth.toNat)) := rfl


theorem findAttr_withTiles_some {h : Header} {n : String} {a : RawAttr}
    (h0 : Parse.findAttr (baseAttrs h) n = some a) :
    Parse.findAttr (withTiles h) n = some a := by
  unfold withTiles
  cases ht : h.tileDesc with
  | none => exact h0
  | some td => exact findAttr_append_some h0

theorem findAttr_withChunkCount_some {h : Header} {n : String} {a : RawAttr}
    (h0 : Parse.findAttr (withTiles h) n = some a) :
    Parse.findAttr (withChunkCount h) n = some a := by
  unfold withChunkCount
  cases ht : h.chunkCount with
  | none => exact h0
  | some n' => exact findAttr_append_some h0

theorem findAttr_withName_some {h : Header} {n : String} {a : RawAttr}
    (h0 : Parse.findAttr (withChunkCount h) n = some a) :
    Parse.findAttr (withName h) n = some a := by
  unfold withName
  cases hn : h.name with
  | none => exact h0
  | some n' => exact findAttr_append_some h0

theorem findAttr_withVersion_some {h : Header} {n : String} {a : RawAttr}
    (h0 : Parse.findAttr (withName h) n = some a) :
    Parse.findAttr (withVersion h) n = some a := by
  unfold withVersion
  split
  · exact findAttr_append_some h0
  · exact h0

theorem findAttr_withMaxSamples_some {h : Header} {n : String} {a : RawAttr}
    (h0 : Parse.findAttr (withVersion h) n = some a) :
    Parse.findAttr (withMaxSamples h) n = some a := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none => exact h0
  | some m => exact findAttr_append_some h0

theorem findAttr_base_type_none (h : Header) :
    Parse.findAttr (baseAttrs h) "type" = none := rfl

theorem findAttr_withTiles_type_none (h : Header) :
    Parse.findAttr (withTiles h) "type" = none := by
  unfold withTiles
  cases ht : h.tileDesc with
  | none => exact findAttr_base_type_none h
  | some td =>
    rw [findAttr_append, findAttr_base_type_none h]
    rfl

theorem findAttr_withChunkCount_type_none (h : Header) :
    Parse.findAttr (withChunkCount h) "type" = none := by
  unfold withChunkCount
  cases ht : h.chunkCount with
  | none => exact findAttr_withTiles_type_none h
  | some n' =>
    rw [findAttr_append, findAttr_withTiles_type_none h]
    rfl

theorem findAttr_withName_type_none (h : Header) :
    Parse.findAttr (withName h) "type" = none := by
  unfold withName
  cases hn : h.name with
  | none => exact findAttr_withChunkCount_type_none h
  | some n' =>
    rw [findAttr_append, findAttr_withChunkCount_type_none h]
    rfl

theorem findAttr_withVersion_type_none (h : Header) :
    Parse.findAttr (withVersion h) "type" = none := by
  unfold withVersion
  split
  · rw [findAttr_append, findAttr_withName_type_none h]
    rfl
  · exact findAttr_withName_type_none h

theorem findAttr_withMaxSamples_type_none (h : Header) :
    Parse.findAttr (withMaxSamples h) "type" = none := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none => exact findAttr_withVersion_type_none h
  | some m =>
    rw [findAttr_append, findAttr_withVersion_type_none h]
    rfl



theorem findAttr_base_tiles_none (h : Header) :
    Parse.findAttr (baseAttrs h) "tiles" = none := rfl

theorem findAttr_withTiles_tiles (h : Header) (td : TypedAttr.TileDesc)
    (ht : h.tileDesc = some td) :
    Parse.findAttr (withTiles h) "tiles"
      = some (attr "tiles" "tiledesc"
          (u32Bytes td.xSize ++ u32Bytes td.ySize ++
            ByteArray.mk #[UInt8.ofNat ((match td.levelMode with
              | .oneLevel => 0 | .mipmap => 1 | .ripmap => 2) ||| (match td.roundingMode with
              | .roundDown => 0 | .roundUp => 1) <<< 4)])) := by
  unfold withTiles
  rw [ht, findAttr_append, findAttr_base_tiles_none h]
  rfl


theorem findAttr_base_chunkCount_none (h : Header) :
    Parse.findAttr (baseAttrs h) "chunkCount" = none := rfl

theorem findAttr_base_name_none (h : Header) :
    Parse.findAttr (baseAttrs h) "name" = none := rfl

theorem findAttr_base_maxSamples_none (h : Header) :
    Parse.findAttr (baseAttrs h) "maxSamplesPerPixel" = none := rfl



theorem findAttr_withTiles_chunkCount_none (h : Header) :
    Parse.findAttr (withTiles h) "chunkCount" = none := by
  unfold withTiles
  cases ht : h.tileDesc with
  | none => exact findAttr_base_chunkCount_none h
  | some td =>
    rw [findAttr_append, findAttr_base_chunkCount_none h]
    rfl

theorem findAttr_withTiles_name_none (h : Header) :
    Parse.findAttr (withTiles h) "name" = none := by
  unfold withTiles
  cases ht : h.tileDesc with
  | none => exact findAttr_base_name_none h
  | some td =>
    rw [findAttr_append, findAttr_base_name_none h]
    rfl
theorem findAttr_withChunkCount_name_none (h : Header) :
    Parse.findAttr (withChunkCount h) "name" = none := by
  unfold withChunkCount
  cases ht : h.chunkCount with
  | none => exact findAttr_withTiles_name_none h
  | some n' =>
    rw [findAttr_append, findAttr_withTiles_name_none h]
    rfl
theorem findAttr_withTiles_maxSamples_none (h : Header) :
    Parse.findAttr (withTiles h) "maxSamplesPerPixel" = none := by
  unfold withTiles
  cases ht : h.tileDesc with
  | none => exact findAttr_base_maxSamples_none h
  | some td =>
    rw [findAttr_append, findAttr_base_maxSamples_none h]
    rfl
theorem findAttr_withChunkCount_maxSamples_none (h : Header) :
    Parse.findAttr (withChunkCount h) "maxSamplesPerPixel" = none := by
  unfold withChunkCount
  cases ht : h.chunkCount with
  | none => exact findAttr_withTiles_maxSamples_none h
  | some n' =>
    rw [findAttr_append, findAttr_withTiles_maxSamples_none h]
    rfl
theorem findAttr_withName_maxSamples_none (h : Header) :
    Parse.findAttr (withName h) "maxSamplesPerPixel" = none := by
  unfold withName
  cases hn : h.name with
  | none => exact findAttr_withChunkCount_maxSamples_none h
  | some n' =>
    rw [findAttr_append, findAttr_withChunkCount_maxSamples_none h]
    rfl
theorem findAttr_withVersion_maxSamples_none (h : Header) :
    Parse.findAttr (withVersion h) "maxSamplesPerPixel" = none := by
  unfold withVersion
  split
  · rw [findAttr_append, findAttr_withName_maxSamples_none h]
    rfl
  · exact findAttr_withName_maxSamples_none h
theorem findAttr_withChunkCount_chunkCount (h : Header) (n : Nat)
    (ht : h.chunkCount = some n) :
    Parse.findAttr (withChunkCount h) "chunkCount"
      = some (attr "chunkCount" "int" (u32Bytes n)) := by
  unfold withChunkCount
  rw [ht, findAttr_append, findAttr_withTiles_chunkCount_none h]
  rfl

theorem findAttr_withName_name (h : Header) (n : Bytes)
    (ht : h.name = some n) :
    Parse.findAttr (withName h) "name"
      = some (attr "name" "string" n) := by
  unfold withName
  rw [ht, findAttr_append, findAttr_withChunkCount_name_none h]
  rfl

theorem findAttr_withMaxSamples_maxSamples (h : Header) (m : Int32)
    (ht : h.maxSamplesPerPixel = some m) :
    Parse.findAttr (withMaxSamples h) "maxSamplesPerPixel"
      = some (attr "maxSamplesPerPixel" "int" (u32Bytes m.toInt.toNat)) := by
  unfold withMaxSamples
  rw [ht, findAttr_append, findAttr_withVersion_maxSamples_none h]
  rfl

theorem findAttr_withTiles_tiles_none (h : Header) (ht : h.tileDesc = none) :
    Parse.findAttr (withTiles h) "tiles" = none := by
  unfold withTiles
  rw [ht]
  exact findAttr_base_tiles_none h

theorem findAttr_withChunkCount_tiles_none (h : Header) (ht : h.tileDesc = none) :
    Parse.findAttr (withChunkCount h) "tiles" = none := by
  unfold withChunkCount
  cases hc : h.chunkCount with
  | none => exact findAttr_withTiles_tiles_none h ht
  | some n' =>
    rw [findAttr_append, findAttr_withTiles_tiles_none h ht]
    rfl

theorem findAttr_withName_tiles_none (h : Header) (ht : h.tileDesc = none) :
    Parse.findAttr (withName h) "tiles" = none := by
  unfold withName
  cases hn : h.name with
  | none => exact findAttr_withChunkCount_tiles_none h ht
  | some n' =>
    rw [findAttr_append, findAttr_withChunkCount_tiles_none h ht]
    rfl

theorem findAttr_withVersion_tiles_none (h : Header) (ht : h.tileDesc = none) :
    Parse.findAttr (withVersion h) "tiles" = none := by
  unfold withVersion
  split
  · rw [findAttr_append, findAttr_withName_tiles_none h ht]
    rfl
  · exact findAttr_withName_tiles_none h ht

theorem findAttr_withName_name_none (h : Header) (ht : h.name = none) :
    Parse.findAttr (withName h) "name" = none := by
  unfold withName
  rw [ht]
  exact findAttr_withChunkCount_name_none h

theorem findAttr_withVersion_name_none (h : Header) (ht : h.name = none) :
    Parse.findAttr (withVersion h) "name" = none := by
  unfold withVersion
  split
  · rw [findAttr_append, findAttr_withName_name_none h ht]
    rfl
  · exact findAttr_withName_name_none h ht

/-! ## `findAttr` over `headerAttrs` -/



theorem findAttr_withMaxSamples_tiles_none (h : Header) (ht : h.tileDesc = none) :
    Parse.findAttr (withMaxSamples h) "tiles" = none := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none => exact findAttr_withVersion_tiles_none h ht
  | some m =>
    rw [findAttr_append, findAttr_withVersion_tiles_none h ht]
    rfl

theorem findAttr_withMaxSamples_name_none (h : Header) (ht : h.name = none) :
    Parse.findAttr (withMaxSamples h) "name" = none := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none => exact findAttr_withVersion_name_none h ht
  | some m =>
    rw [findAttr_append, findAttr_withVersion_name_none h ht]
    rfl

theorem findAttr_headerAttrs_tiles_none (h : Header) (mp : Bool) (ht : h.tileDesc = none) :
    Parse.findAttr (headerAttrs h mp) "tiles" = none := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc, findAttr_append, findAttr_withMaxSamples_tiles_none h ht]
    rfl
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_tiles_none h ht

theorem findAttr_headerAttrs_name_none (h : Header) (mp : Bool) (ht : h.name = none) :
    Parse.findAttr (headerAttrs h mp) "name" = none := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc, findAttr_append, findAttr_withMaxSamples_name_none h ht]
    rfl
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_name_none h ht

theorem findAttr_headerAttrs_type_some (h : Header) (multipart : Bool)
    (hmp : multipart || h.partType.isDeep) :
    Parse.findAttr (headerAttrs h multipart) "type"
      = some (attr "type" "string" (h.partType.wireName.toUTF8)) := by
  unfold headerAttrs
  rw [ite_eq_left hmp, findAttr_append, findAttr_withMaxSamples_type_none h]
  rfl

theorem findAttr_headerAttrs_type_none (h : Header) (multipart : Bool)
    (hmp : ¬ (multipart || h.partType.isDeep)) :
    Parse.findAttr (headerAttrs h multipart) "type" = none := by
  unfold headerAttrs
  rw [ite_eq_right hmp]
  exact findAttr_withMaxSamples_type_none h


theorem findAttr_headerAttrs_channels (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "channels"
      = some (attr "channels" "chlist" (chlistOf h)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_channels h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_channels h)))))

theorem findAttr_headerAttrs_compression (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "compression"
      = some (attr "compression" "compression" (ByteArray.mk #[h.compression.toBits])) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_compression h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_compression h)))))

theorem findAttr_headerAttrs_dataWindow (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "dataWindow"
      = some (attr "dataWindow" "box2i" (box2iOf h.dataWindow)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_dataWindow h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_dataWindow h)))))

theorem findAttr_headerAttrs_displayWindow (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "displayWindow"
      = some (attr "displayWindow" "box2i" (box2iOf h.displayWindow)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_displayWindow h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_displayWindow h)))))

theorem findAttr_headerAttrs_lineOrder (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "lineOrder"
      = some (attr "lineOrder" "lineOrder" (ByteArray.mk #[h.lineOrder.toBits])) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_lineOrder h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_lineOrder h)))))

theorem findAttr_headerAttrs_pixelAspectRatio (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "pixelAspectRatio"
      = some (attr "pixelAspectRatio" "float" (u32Bytes h.pixelAspectRatio.toNat)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_pixelAspectRatio h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_pixelAspectRatio h)))))

theorem findAttr_headerAttrs_screenWindowCenter (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "screenWindowCenter"
      = some (attr "screenWindowCenter" "v2f"
          (u32Bytes h.screenWindowCenterX.toNat ++ u32Bytes h.screenWindowCenterY.toNat)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_screenWindowCenter h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_screenWindowCenter h)))))

theorem findAttr_headerAttrs_screenWindowWidth (h : Header) (mp : Bool) :
    Parse.findAttr (headerAttrs h mp) "screenWindowWidth"
      = some (attr "screenWindowWidth" "float" (u32Bytes h.screenWindowWidth.toNat)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_some
        (findAttr_base_screenWindowWidth h))))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_some (findAttr_base_screenWindowWidth h)))))

theorem findAttr_headerAttrs_tiles (h : Header) (mp : Bool) (td : TypedAttr.TileDesc)
    (ht : h.tileDesc = some td) :
    Parse.findAttr (headerAttrs h mp) "tiles"
      = some (attr "tiles" "tiledesc"
          (u32Bytes td.xSize ++ u32Bytes td.ySize ++
            ByteArray.mk #[UInt8.ofNat ((match td.levelMode with
              | .oneLevel => 0 | .mipmap => 1 | .ripmap => 2) ||| (match td.roundingMode with
              | .roundDown => 0 | .roundUp => 1) <<< 4)])) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_some (findAttr_withTiles_tiles h td ht)))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_some (findAttr_withTiles_tiles h td ht))))

theorem findAttr_headerAttrs_chunkCount (h : Header) (mp : Bool) (n : Nat)
    (ht : h.chunkCount = some n) :
    Parse.findAttr (headerAttrs h mp) "chunkCount"
      = some (attr "chunkCount" "int" (u32Bytes n)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_some (findAttr_withChunkCount_chunkCount h n ht))))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some (findAttr_withName_some
      (findAttr_withChunkCount_chunkCount h n ht)))

theorem findAttr_headerAttrs_name (h : Header) (mp : Bool) (n : Bytes)
    (ht : h.name = some n) :
    Parse.findAttr (headerAttrs h mp) "name"
      = some (attr "name" "string" n) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_name h n ht)))
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_some (findAttr_withVersion_some
      (findAttr_withName_name h n ht))

theorem findAttr_headerAttrs_maxSamples (h : Header) (mp : Bool) (m : Int32)
    (ht : h.maxSamplesPerPixel = some m) :
    Parse.findAttr (headerAttrs h mp) "maxSamplesPerPixel"
      = some (attr "maxSamplesPerPixel" "int" (u32Bytes m.toInt.toNat)) := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc]
    exact findAttr_append_some (findAttr_withMaxSamples_maxSamples h m ht)
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_maxSamples h m ht


/-- The canonical attribute encoder is inverted by the typed decoders:
    channel lists, windows, scalars, tile descriptors, names, chunk and
    sample counts, and (when present) the part type all decode back. -/
theorem findAttr_withChunkCount_chunkCount_none (h : Header) (ht : h.chunkCount = none) :
    Parse.findAttr (withChunkCount h) "chunkCount" = none := by
  unfold withChunkCount
  rw [ht]
  exact findAttr_withTiles_chunkCount_none h

theorem findAttr_withName_chunkCount_none (h : Header) (ht : h.chunkCount = none) :
    Parse.findAttr (withName h) "chunkCount" = none := by
  unfold withName
  cases hn : h.name with
  | none => exact findAttr_withChunkCount_chunkCount_none h ht
  | some n' =>
    rw [findAttr_append, findAttr_withChunkCount_chunkCount_none h ht]
    rfl

theorem findAttr_withVersion_chunkCount_none (h : Header) (ht : h.chunkCount = none) :
    Parse.findAttr (withVersion h) "chunkCount" = none := by
  unfold withVersion
  split
  · rw [findAttr_append, findAttr_withName_chunkCount_none h ht]
    rfl
  · exact findAttr_withName_chunkCount_none h ht

theorem findAttr_withMaxSamples_chunkCount_none (h : Header) (ht : h.chunkCount = none) :
    Parse.findAttr (withMaxSamples h) "chunkCount" = none := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none => exact findAttr_withVersion_chunkCount_none h ht
  | some m =>
    rw [findAttr_append, findAttr_withVersion_chunkCount_none h ht]
    rfl

theorem findAttr_headerAttrs_chunkCount_none (h : Header) (mp : Bool) (ht : h.chunkCount = none) :
    Parse.findAttr (headerAttrs h mp) "chunkCount" = none := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc, findAttr_append, findAttr_withMaxSamples_chunkCount_none h ht]
    rfl
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_chunkCount_none h ht

theorem findAttr_withMaxSamples_maxSamples_none (h : Header) (ht : h.maxSamplesPerPixel = none) :
    Parse.findAttr (withMaxSamples h) "maxSamplesPerPixel" = none := by
  unfold withMaxSamples
  rw [ht]
  exact findAttr_withVersion_maxSamples_none h

theorem findAttr_headerAttrs_maxSamples_none (h : Header) (mp : Bool)
    (ht : h.maxSamplesPerPixel = none) :
    Parse.findAttr (headerAttrs h mp) "maxSamplesPerPixel" = none := by
  unfold headerAttrs
  by_cases hc : mp || h.partType.isDeep
  · rw [ite_eq_left hc, findAttr_append, findAttr_withMaxSamples_maxSamples_none h ht]
    rfl
  · rw [ite_eq_right hc]
    exact findAttr_withMaxSamples_maxSamples_none h ht

theorem int32Of_headerAttrs_chunkCount (h : Header) (mp : Bool) (n : Nat)
    (ht : h.chunkCount = some n) :
    Parse.int32Of (headerAttrs h mp) "chunkCount" = some (Int32.ofNat n) := by
  unfold Parse.int32Of
  rw [findAttr_headerAttrs_chunkCount h mp n ht, Option.bind_some,
      show (attr "chunkCount" "int" (u32Bytes n)).value = u32Bytes n from rfl, decodeInt_u32Bytes]

theorem int32Of_headerAttrs_chunkCount_none (h : Header) (mp : Bool)
    (ht : h.chunkCount = none) :
    Parse.int32Of (headerAttrs h mp) "chunkCount" = none := by
  unfold Parse.int32Of
  rw [findAttr_headerAttrs_chunkCount_none h mp ht]
  rfl

theorem int32Of_headerAttrs_maxSamples (h : Header) (mp : Bool) (m : Int32)
    (ht : h.maxSamplesPerPixel = some m) (hnonneg : 1 ≤ m.toInt) :
    Parse.int32Of (headerAttrs h mp) "maxSamplesPerPixel" = some m := by
  unfold Parse.int32Of
  rw [findAttr_headerAttrs_maxSamples h mp m ht, Option.bind_some,
      show (attr "maxSamplesPerPixel" "int" (u32Bytes m.toInt.toNat)).value = u32Bytes m.toInt.toNat from rfl,
      decodeInt_u32Bytes, Int32_ofNat_toNat m hnonneg]

theorem int32Of_headerAttrs_maxSamples_none (h : Header) (mp : Bool)
    (ht : h.maxSamplesPerPixel = none) :
    Parse.int32Of (headerAttrs h mp) "maxSamplesPerPixel" = none := by
  unfold Parse.int32Of
  rw [findAttr_headerAttrs_maxSamples_none h mp ht]
  rfl

theorem headerOfAttrs_headerAttrs (h : Header) (mp singleTile deep : Bool)
    (hChanOK : ∀ c ∈ h.channels, ChannelOK c)
    (hCC : ∀ n, h.chunkCount = some n → n < 2 ^ 31)
    (hTd : ∀ td, h.tileDesc = some td → td.xSize < 2 ^ 32 ∧ td.ySize < 2 ^ 32)
    (hMS : ∀ m, h.maxSamplesPerPixel = some m → 1 ≤ m.toInt)
    (hAttrs : h.attrs = headerAttrs h mp)
    (hDeep : h.partType.isDeep = deep)
    (hPart : ¬ (mp || h.partType.isDeep) →
      h.partType = (if deep then (if singleTile then .deepTiled else .deepScanline)
                    else if singleTile then .tiled else .scanline)) :
    Parse.headerOfAttrs (headerAttrs h mp) singleTile deep = some h := by
  -- the typed field decoders
  have eDW : Parse.box2iOf (headerAttrs h mp) "dataWindow" = some h.dataWindow := by
    unfold Parse.box2iOf
    rw [findAttr_headerAttrs_dataWindow h mp, box2iOf_eq_encBox2i, Option.bind_some]
    exact TypedAttr.decodeBox2i_encode h.dataWindow
  have eDisp : Parse.box2iOf (headerAttrs h mp) "displayWindow" = some h.displayWindow := by
    unfold Parse.box2iOf
    rw [findAttr_headerAttrs_displayWindow h mp, box2iOf_eq_encBox2i, Option.bind_some]
    exact TypedAttr.decodeBox2i_encode h.displayWindow
  have eChans : Parse.channelsOf (headerAttrs h mp) = some h.channels := by
    unfold Parse.channelsOf
    rw [findAttr_headerAttrs_channels h mp, Option.bind_some,
        show (attr "channels" "chlist" (chlistOf h)).value = chlistOf h from rfl,
        chlistOf_eq_encChlist, decodeChlist_encChlist h.channels hChanOK, Option.map_some]
  have eComp : Parse.compressionOf (headerAttrs h mp) = some h.compression := by
    unfold Parse.compressionOf
    rw [findAttr_headerAttrs_compression h mp, Option.bind_some]
    exact TypedAttr.decodeCompression_encode h.compression
  have eLo : Parse.lineOrderOf (headerAttrs h mp) = some h.lineOrder := by
    unfold Parse.lineOrderOf
    rw [findAttr_headerAttrs_lineOrder h mp, Option.bind_some]
    exact TypedAttr.decodeLineOrder_encode h.lineOrder
  have ePAR : Parse.u32Of (headerAttrs h mp) "pixelAspectRatio" = some h.pixelAspectRatio := by
    unfold Parse.u32Of
    rw [findAttr_headerAttrs_pixelAspectRatio h mp, u32Bytes_eq_u32Words, Option.bind_some]
    exact TypedAttr.decodeFloatBits_encode h.pixelAspectRatio
  have eSWC : Parse.v2fOf (headerAttrs h mp) "screenWindowCenter"
      = some (h.screenWindowCenterX, h.screenWindowCenterY) := by
    unfold Parse.v2fOf
    rw [findAttr_headerAttrs_screenWindowCenter h mp, u32Bytes_append_eq_u32Words, Option.bind_some]
    exact TypedAttr.decodeV2f_encode (h.screenWindowCenterX, h.screenWindowCenterY)
  have eSWW : Parse.u32Of (headerAttrs h mp) "screenWindowWidth" = some h.screenWindowWidth := by
    unfold Parse.u32Of
    rw [findAttr_headerAttrs_screenWindowWidth h mp, u32Bytes_eq_u32Words, Option.bind_some]
    exact TypedAttr.decodeFloatBits_encode h.screenWindowWidth
  -- part type: from the type attribute, else the fallback
  have ePTome? : Parse.partTypeOf (headerAttrs h mp)
      (if deep then (if singleTile then .deepTiled else .deepScanline)
       else if singleTile then .tiled else .scanline) = some h.partType := by
    by_cases hc : mp || h.partType.isDeep
    · unfold Parse.partTypeOf
      rw [findAttr_headerAttrs_type_some h mp hc]
      show (match String.fromUTF8? (h.partType.wireName.toUTF8) with
            | some s => PartType.ofWireName s
            | none => none) = some h.partType
      rw [String.toUTF8_eq_toByteArray, String.fromUTF8?, dite_eq_left h.partType.wireName.isValidUTF8]
      rw [show String.fromUTF8 h.partType.wireName.toByteArray h.partType.wireName.isValidUTF8
            = h.partType.wireName from rfl]
      exact PartType.ofWireName_wireName h.partType
    · unfold Parse.partTypeOf
      rw [findAttr_headerAttrs_type_none h mp hc]
      exact congrArg some (hPart hc).symm
  -- chunk count / sample count / tile descriptor / name fields
  have eTiles : Parse.tileDescOf (headerAttrs h mp) = h.tileDesc := by
    cases ht : h.tileDesc with
    | none =>
      unfold Parse.tileDescOf
      rw [findAttr_headerAttrs_tiles_none h mp ht]
      rfl
    | some td =>
      unfold Parse.tileDescOf
      rw [findAttr_headerAttrs_tiles h mp td ht, Option.bind_some, tileBytes_eq_encTileDesc]
      obtain ⟨hx, hy⟩ := hTd td ht
      exact TypedAttr.decodeTileDesc_encode td hx hy
  have eName : Parse.bytesOf (headerAttrs h mp) "name" = h.name := by
    cases hn : h.name with
    | none =>
      unfold Parse.bytesOf
      rw [findAttr_headerAttrs_name_none h mp hn]
      rfl
    | some n =>
      unfold Parse.bytesOf
      rw [findAttr_headerAttrs_name h mp n hn, Option.map_some,
        show (attr "name" "string" n).value = n from rfl]
  -- The two option-typed integer fields also decode back.
  have eChunk : (match Parse.int32Of (headerAttrs h mp) "chunkCount" with
        | some v => if v.toInt ≥ 0 then some v.toInt.toNat else none
        | none => none) = h.chunkCount := by
    cases hc : h.chunkCount with
    | none => rw [int32Of_headerAttrs_chunkCount_none h mp hc]
    | some n =>
      rw [int32Of_headerAttrs_chunkCount h mp n hc]
      simp [Exr.Int32_ofNat_toInt n (hCC n hc)]
  have eMax : Parse.int32Of (headerAttrs h mp) "maxSamplesPerPixel" = h.maxSamplesPerPixel := by
    cases hm : h.maxSamplesPerPixel with
    | none => exact int32Of_headerAttrs_maxSamples_none h mp hm
    | some m => exact int32Of_headerAttrs_maxSamples h mp m hm (hMS m hm)
  -- unfold the do-block and substitute the field decodings
  unfold Parse.headerOfAttrs
  simp only [eDW, eDisp, eChans, eComp, eLo, ePAR, eSWC, eSWW, eTiles, eName, ePTome?,
    eMax]
  cases hc : h.chunkCount with
  | none =>
    rw [int32Of_headerAttrs_chunkCount_none h mp hc, ← hAttrs]
    cases h
    simp
    exact hc.symm
  | some n =>
    rw [int32Of_headerAttrs_chunkCount h mp n hc]
    simp only [Exr.Int32_ofNat_toInt n (hCC n hc)]
    rw [← hAttrs]
    cases h
    simp
    exact hc.symm


/-! ## Full-file round trip

The pieces below compose the attribute, header, offset-table and
magic/version inverses into `parseFile (filePrefix f ++ payload) = some f`.
The file is assumed to be in the canonical emitted form: every part header
is emitted by `headerAttrs`, every offset table has exactly one entry per
chunk, and `dataStart` is the end of the emitted structural prefix. -/

/-- The concatenation of the emitted part headers, in part order. -/
def emitParts (parts : List Header) : Bytes :=
  parts.foldr (fun h acc => headerBytes h.attrs ++ acc) ByteArray.empty

theorem emitParts_nil : emitParts [] = ByteArray.empty := rfl

theorem emitParts_cons (h : Header) (parts : List Header) :
    emitParts (h :: parts) = headerBytes h.attrs ++ emitParts parts := rfl

theorem emitParts_eq_foldl (parts : List Header) :
    parts.foldl (fun acc h => acc ++ headerBytes h.attrs) ByteArray.empty = emitParts parts := by
  unfold emitParts
  simpa using foldl_append_eq_foldr parts (fun h => headerBytes h.attrs) ByteArray.empty

theorem emitParts_size (parts : List Header) :
    (emitParts parts).size = (parts.map fun h => (headerBytes h.attrs).size).sum := by
  induction parts with
  | nil => rfl
  | cons h parts ih =>
    rw [emitParts_cons, ByteArray.size_append, ih]
    rfl

theorem emitParts_length_le (parts : List Header) :
    parts.length ≤ (emitParts parts).size := by
  rw [emitParts_size]
  induction parts with
  | nil => simp
  | cons h parts ih =>
    have hpos : 0 < (headerBytes h.attrs).size := by
      have h1 : 0 < (nulByte).size := by decide
      unfold headerBytes
      simp only [ByteArray.size_append]
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The canonical-encoder well-formedness obligations for one part.  These are
    exactly the hypotheses needed by `headerAttrs_emittable` and
    `headerOfAttrs_headerAttrs`, plus the canonical-attrs identity required
    when the emitted file is built from the `attrs` field. -/
structure HeaderEmitOK (multipart singleTile deep : Bool) (h : Header) : Prop where
  channelsOK : ∀ c ∈ h.channels, ChannelOK c
  channelsLength : h.channels.length ≤ 2 ^ 20
  channelsNameSize : ∀ c ∈ h.channels, c.name.size ≤ 255
  chunkCountSmall : ∀ n, h.chunkCount = some n → n < 2 ^ 31
  tileDescriptionSmall : ∀ td, h.tileDesc = some td → td.xSize < 2 ^ 32 ∧ td.ySize < 2 ^ 32
  maxSamplesPositive : ∀ m, h.maxSamplesPerPixel = some m → 1 ≤ m.toInt
  nameSize : ∀ n, h.name = some n → n.size ≤ 255
  attrsEq : h.attrs = headerAttrs h multipart
  deepEq : h.partType.isDeep = deep
  partEq :
    ¬ (multipart || h.partType.isDeep) →
      h.partType =
        if deep then (if singleTile then .deepTiled else .deepScanline)
        else if singleTile then .tiled else .scanline

/-- The canonical-emitted-file obligations for a whole structural file. -/
structure FileEmitOK (f : ParsedFile) : Prop where
  headersOK :
    ∀ h ∈ f.parts,
      HeaderEmitOK f.version.multipart f.version.singleTile f.version.nonImage h
  tablesOK :
    ∀ p ∈ f.parts.zip f.offsetTables,
      p.2.offsets.length = Parse.chunkCountOf p.1
  tablesCount : f.offsetTables.length = f.parts.length
  offsetsSmall : ∀ t ∈ f.offsetTables, ∀ o ∈ t.offsets, o < 2 ^ 64
  singlePartLength :
    f.version.multipart = false → f.parts.length = 1
  dataStart : f.dataStart = (filePrefix f).size

theorem headerAttrs_emittable_of_ok {h : Header} {multipart singleTile deep : Bool}
    (hok : HeaderEmitOK multipart singleTile deep h) :
    ∀ a ∈ headerAttrs h multipart, RawAttr.Emittable a RawAttr.maxShortName := by
  simpa [RawAttr.maxShortName] using
    headerAttrs_emittable h multipart hok.channelsLength hok.channelsNameSize hok.nameSize

theorem headerOfAttrs_of_ok {h : Header} {multipart singleTile deep : Bool}
    (hok : HeaderEmitOK multipart singleTile deep h) :
    Parse.headerOfAttrs (headerAttrs h multipart) singleTile deep = some h :=
  headerOfAttrs_headerAttrs h multipart singleTile deep hok.channelsOK hok.chunkCountSmall
    hok.tileDescriptionSmall hok.maxSamplesPositive hok.attrsEq hok.deepEq hok.partEq

theorem parseHeader_emit {h : Header} {multipart singleTile deep : Bool}
    (hok : HeaderEmitOK multipart singleTile deep h) (p rest : Bytes) (longNames : Bool)
    (fuel : Nat) (hf : (headerAttrs h multipart).length + 1 ≤ fuel) :
    RawAttr.parseAll
      (p ++ (RawAttr.wireAll (headerAttrs h multipart) ++ (nulByte ++ rest)))
      longNames p.size fuel
      = some (headerAttrs h multipart, p.size + (RawAttr.wireAll (headerAttrs h multipart)).size + 1) := by
  have h31 := headerAttrs_emittable_of_ok hok
  have hAll : ∀ a ∈ headerAttrs h multipart,
      RawAttr.Emittable a (if longNames then RawAttr.maxLongName else RawAttr.maxShortName) := by
    intro a ha
    by_cases hl : longNames
    · rw [ite_eq_left hl]
      exact RawAttr.Emittable.mono (h31 a ha) (by
        unfold RawAttr.maxShortName RawAttr.maxLongName
        omega)
    · rw [ite_eq_right hl]
      exact h31 a ha
  exact RawAttr.parseAll_emit (headerAttrs h multipart) p rest longNames fuel hAll hf

theorem headerBytes_of_ok {h : Header} {multipart singleTile deep : Bool}
    (hok : HeaderEmitOK multipart singleTile deep h) :
    headerBytes h.attrs
      = RawAttr.wireAll (headerAttrs h multipart) ++ nulByte := by
  rw [hok.attrsEq, headerBytes_eq_wireAll]


theorem baseAttrs_length (h : Header) : (baseAttrs h).length = 8 := rfl

theorem withTiles_length_le (h : Header) : (withTiles h).length ≤ 9 := by
  unfold withTiles
  cases td : h.tileDesc with
  | none => simp [baseAttrs_length]
  | some td => simp [List.length_append, baseAttrs_length]

theorem withChunkCount_length_le (h : Header) : (withChunkCount h).length ≤ 10 := by
  unfold withChunkCount
  cases hc : h.chunkCount with
  | none =>
    show (withTiles h).length ≤ 10
    exact Nat.le_trans (withTiles_length_le h) (by omega)
  | some n => simp [List.length_append, withTiles_length_le]

theorem withName_length_le (h : Header) : (withName h).length ≤ 11 := by
  unfold withName
  cases hn : h.name with
  | none =>
    show (withChunkCount h).length ≤ 11
    exact Nat.le_trans (withChunkCount_length_le h) (by omega)
  | some n => simp [List.length_append, withChunkCount_length_le]

theorem withVersion_length_le (h : Header) : (withVersion h).length ≤ 12 := by
  unfold withVersion
  by_cases hd : h.partType.isDeep
  · rw [ite_eq_left hd]
    simp [List.length_append, withName_length_le]
  · rw [ite_eq_right hd]
    exact Nat.le_trans (withName_length_le h) (by omega)

theorem withMaxSamples_length_le (h : Header) : (withMaxSamples h).length ≤ 13 := by
  unfold withMaxSamples
  cases hm : h.maxSamplesPerPixel with
  | none =>
    show (withVersion h).length ≤ 13
    exact Nat.le_trans (withVersion_length_le h) (by omega)
  | some m => simp [List.length_append, withVersion_length_le]

theorem headerAttrs_length_le (h : Header) (multipart : Bool) :
    (headerAttrs h multipart).length ≤ 14 := by
  unfold headerAttrs
  by_cases hc : multipart || h.partType.isDeep
  · rw [ite_eq_left hc]
    have h1 := withMaxSamples_length_le h
    simp [List.length_append]
    omega
  · rw [ite_eq_right hc]
    exact Nat.le_trans (withMaxSamples_length_le h) (by omega)



theorem emitParts_of_ok {parts : List Header} {multipart singleTile deep : Bool}
    (hOK : ∀ h ∈ parts, HeaderEmitOK multipart singleTile deep h) :
    emitParts parts
      = parts.foldr
          (fun h acc => (RawAttr.wireAll (headerAttrs h multipart) ++ nulByte) ++ acc)
          ByteArray.empty := by
  induction parts with
  | nil => rfl
  | cons h parts ih =>
    rw [emitParts_cons, headerBytes_of_ok (hOK h (by simp)), ih (fun t ht => hOK t (List.mem_cons_of_mem h ht))]
    rfl



theorem withTiles_length_ge (h : Header) : 8 ≤ (withTiles h).length := by
  unfold withTiles
  cases td : h.tileDesc with
  | none => simp [baseAttrs_length]
  | some td => simp [List.length_append, baseAttrs_length]

theorem withChunkCount_length_ge (h : Header) : 8 ≤ (withChunkCount h).length :=
  Nat.le_trans (withTiles_length_ge h) (by
    unfold withChunkCount
    split
    · simp
    · exact Nat.le_refl _)

theorem withName_length_ge (h : Header) : 8 ≤ (withName h).length :=
  Nat.le_trans (withChunkCount_length_ge h) (by
    unfold withName
    split
    · simp
    · exact Nat.le_refl _)

theorem withVersion_length_ge (h : Header) : 8 ≤ (withVersion h).length :=
  Nat.le_trans (withName_length_ge h) (by
    unfold withVersion
    split
    · simp
    · exact Nat.le_refl _)

theorem withMaxSamples_length_ge (h : Header) : 8 ≤ (withMaxSamples h).length :=
  Nat.le_trans (withVersion_length_ge h) (by
    unfold withMaxSamples
    split
    · simp
    · exact Nat.le_refl _)

theorem headerAttrs_length_ge (h : Header) (multipart : Bool) :
    8 ≤ (headerAttrs h multipart).length := by
  unfold headerAttrs
  split
  · have h1 := withMaxSamples_length_ge h
    simp [List.length_append]
    omega
  · exact withMaxSamples_length_ge h

theorem headerAttrs_ne_nil (h : Header) (multipart : Bool) :
    headerAttrs h multipart ≠ [] := by
  intro he
  have hge := headerAttrs_length_ge h multipart
  rw [he] at hge
  simp at hge

theorem parsePartHeaders_emit_multipart
    (parts : List Header) (p rest : Bytes) (longNames singleTile deep : Bool)
    (hOK : ∀ h ∈ parts, HeaderEmitOK true singleTile deep h)
    (fuel : Nat) (hf : parts.length * 15 + 2 ≤ fuel) :
    Parse.parsePartHeaders
      (p ++ (emitParts parts ++ (nulByte ++ rest)))
      longNames true deep singleTile p.size fuel
      = some (parts, p.size + (emitParts parts).size + 1) := by
  induction parts generalizing p fuel with
  | nil =>
    have hf1 : 2 ≤ fuel := by omega
    obtain ⟨N, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    unfold Parse.parsePartHeaders
    have hbytes : p ++ (emitParts ([] : List Header) ++ (nulByte ++ rest))
        = p ++ (RawAttr.wireAll ([] : List RawAttr) ++ (nulByte ++ rest)) := by
      simp [emitParts, RawAttr.wireAll]
    rw [hbytes]
    have hparse : RawAttr.parseAll (p ++ (RawAttr.wireAll ([] : List RawAttr) ++ (nulByte ++ rest))) longNames p.size N
        = some (([] : List RawAttr), p.size + (RawAttr.wireAll ([] : List RawAttr)).size + 1) :=
      RawAttr.parseAll_emit ([] : List RawAttr) p rest longNames N
        (fun a ha => (List.not_mem_nil (a := a) ha).elim) (by omega)
    rw [hparse]
    simp [emitParts, RawAttr.wireAll]
  | cons h parts ih =>
    have hOK' : ∀ t ∈ parts, HeaderEmitOK true singleTile deep t :=
      fun t ht => hOK t (List.mem_cons_of_mem h ht)
    have hh := hOK h List.mem_cons_self
    obtain ⟨N, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hN : parts.length * 15 + 16 ≤ N := by
      simp only [List.length_cons] at hf
      omega
    have hNrec : parts.length * 15 + 2 ≤ N := by omega
    unfold Parse.parsePartHeaders
    have hfirst : p ++ (emitParts ((h :: parts)) ++ (nulByte ++ rest))
        = p ++ (RawAttr.wireAll (headerAttrs h true) ++
            (nulByte ++ (emitParts parts ++ (nulByte ++ rest)))) := by
      rw [emitParts_cons, headerBytes_of_ok hh, emitParts_of_ok hOK']
      simp [ByteArray.append_assoc]
    rw [hfirst]
    have hlen : (headerAttrs h true).length + 1 ≤ N := by
      have hle := headerAttrs_length_le h true
      omega
    have hparse := parseHeader_emit hh p (emitParts parts ++ (nulByte ++ rest)) longNames N hlen
    rw [hparse]
    have hdec := headerOfAttrs_of_ok hh
    have hneBool : (headerAttrs h true).isEmpty = false := by
      simp [headerAttrs_ne_nil h true]
    simp only [hdec, hneBool, Bool.false_eq_true, ite_false, ite_true]
    have hrec := ih (p := p ++ (RawAttr.wireAll (headerAttrs h true) ++ nulByte))
      hOK' (fuel := N) hNrec
    rw [show p.size + (RawAttr.wireAll (headerAttrs h true)).size + 1
          = (p ++ (RawAttr.wireAll (headerAttrs h true) ++ nulByte)).size by
        simp only [ByteArray.size_append, nulByte_size_emit]
        exact Nat.add_assoc _ _ _]
    rw [show p ++ (RawAttr.wireAll (headerAttrs h true) ++
            (nulByte ++ (emitParts parts ++ (nulByte ++ rest))))
          = (p ++ (RawAttr.wireAll (headerAttrs h true) ++ nulByte)) ++
              (emitParts parts ++ (nulByte ++ rest)) by
        simp [ByteArray.append_assoc]]
    rw [hrec]
    have hnul : (nulByte).size = 1 := nulByte_size_emit
    have hprefix : (p ++ (RawAttr.wireAll (headerAttrs h true) ++ nulByte)).size
        = p.size + ((RawAttr.wireAll (headerAttrs h true)).size + 1) := by
      simp [ByteArray.size_append, nulByte_size_emit]
    have hnum : (p ++ (RawAttr.wireAll (headerAttrs h true) ++ nulByte)).size
          + (emitParts parts).size + 1
        = p.size + (emitParts (h :: parts)).size + 1 := by
      rw [hprefix, emitParts_cons, headerBytes_of_ok hh]
      simp only [ByteArray.size_append, nulByte_size_emit]
      omega
    rw [hnum]

theorem parsePartHeaders_emit_single
    (h : Header) (p rest : Bytes) (longNames singleTile deep : Bool)
    (hok : HeaderEmitOK false singleTile deep h)
    (fuel : Nat) (hf : 16 ≤ fuel) :
    Parse.parsePartHeaders
      (p ++ (emitParts [h] ++ rest))
      longNames false deep singleTile p.size fuel
      = some ([h], p.size + (emitParts [h]).size) := by
  obtain ⟨N, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold Parse.parsePartHeaders
  have hfirst : p ++ (emitParts [h] ++ rest)
      = p ++ (RawAttr.wireAll (headerAttrs h false) ++ (nulByte ++ rest)) := by
    rw [emitParts_cons, emitParts_nil, headerBytes_of_ok hok]
    simp [ByteArray.append_assoc]
  rw [hfirst]
  have hlen : (headerAttrs h false).length + 1 ≤ N := by
    have hle := headerAttrs_length_le h false
    omega
  have hparse := parseHeader_emit hok p rest longNames N hlen
  rw [hparse]
  have hneBool : (headerAttrs h false).isEmpty = false := by
    simp [headerAttrs_ne_nil h false]
  simp only [headerOfAttrs_of_ok hok, hneBool, Bool.false_eq_true, ite_false]
  have hempty : (ByteArray.empty : Bytes).size = 0 := rfl
  have hnum : p.size + (RawAttr.wireAll (headerAttrs h false)).size + 1
      = p.size + (emitParts [h]).size := by
    rw [emitParts_cons, emitParts_nil, headerBytes_of_ok hok]
    simp only [ByteArray.size_append, nulByte_size_emit, hempty, Nat.add_zero]
    exact Nat.add_assoc _ _ _
  rw [hnum]




/-! ## Offset tables, prefix reads, and the full-file round trip -/

theorem offsetTableBytes_cons (o : Nat) (os : List Nat) :
    offsetTableBytes (o :: os) = u64Bytes o ++ offsetTableBytes os := by
  unfold offsetTableBytes
  rw [List.foldl_cons, foldl_append_eq_foldr, ByteArray.empty_append,
    foldl_append_eq_foldr, ByteArray.empty_append]

theorem tablesBytes_cons (t : OffsetTable) (ts : List OffsetTable) :
    tablesBytes (t :: ts) = offsetTableBytes t.offsets ++ tablesBytes ts := by
  unfold tablesBytes
  rw [List.foldl_cons, foldl_append_eq_foldr, ByteArray.empty_append,
    foldl_append_eq_foldr, ByteArray.empty_append]

theorem u64Bytes_size_emit (o : Nat) : (u64Bytes o).size = 8 := by
  simp [u64Bytes, putU64LE]

theorem offsetTableBytes_size_emit (offsets : List Nat) :
    (offsetTableBytes offsets).size = 8 * offsets.length := by
  induction offsets with
  | nil => rfl
  | cons o os ih =>
    rw [offsetTableBytes_cons, ByteArray.size_append, u64Bytes_size_emit, ih,
      List.length_cons]
    omega

theorem parseOffsetTable_emit (offsets : List Nat) (p rest : Bytes)
    (hbig : ∀ o ∈ offsets, o < 2 ^ 64) :
    Parse.parseOffsetTable (p ++ (offsetTableBytes offsets ++ rest)) offsets.length p.size
      = some ({ offsets := offsets }, p.size + 8 * offsets.length) := by
  revert hbig
  induction offsets generalizing p rest with
  | nil => intro _; rfl
  | cons o os ih =>
    intro hbig
    have hbig' : ∀ x ∈ os, x < 2 ^ 64 := fun x hx => hbig x (List.mem_cons_of_mem o hx)
    have hbytes : p ++ (offsetTableBytes (o :: os) ++ rest)
        = p ++ (u64Bytes o ++ (offsetTableBytes os ++ rest)) := by
      rw [offsetTableBytes_cons]
      simp [ByteArray.append_assoc]
    have hoff : Parse.offsetOf (p ++ (offsetTableBytes (o :: os) ++ rest)) p.size = some o := by
      have hto : (UInt64.ofNat o).toNat = o := by
        simpa using Nat.mod_eq_of_lt (hbig o List.mem_cons_self)
      unfold Parse.offsetOf
      rw [hbytes]
      have h1 : getU64LE (p ++ (u64Bytes o ++ (offsetTableBytes os ++ rest))) (p.size + 0)
          = getU64LE (u64Bytes o ++ (offsetTableBytes os ++ rest)) 0 :=
        getU64LE_append_right' (a := p) (b := u64Bytes o ++ (offsetTableBytes os ++ rest)) 0
      rw [show p.size = p.size + 0 by omega, h1,
        getU64LE_append_left (a := u64Bytes o) (b := offsetTableBytes os ++ rest) (i := 0)
          (by rw [u64Bytes_size_emit])]
      show (getU64LE (putU64LE (UInt64.ofNat o) ByteArray.empty) 0).map UInt64.toNat = some o
      rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU64LE_putU64LE]
      simp [hto]
    have hsize : (p ++ u64Bytes o).size = p.size + 8 := by
      rw [ByteArray.size_append, u64Bytes_size_emit]
    have hrewrite : p ++ (offsetTableBytes (o :: os) ++ rest)
        = (p ++ u64Bytes o) ++ (offsetTableBytes os ++ rest) := by
      rw [offsetTableBytes_cons]
      simp [ByteArray.append_assoc]
    have hrec := ih (p := p ++ u64Bytes o) (rest := rest) (hbig := hbig')
    rw [List.length_cons]
    show ((match Parse.offsetOf (p ++ (offsetTableBytes (o :: os) ++ rest)) p.size with
        | none => none
        | some o' => match Parse.parseOffsetTable (p ++ (offsetTableBytes (o :: os) ++ rest))
            os.length (p.size + 8) with
            | none => none
            | some (rest, j) => some (({ offsets := o' :: rest.offsets } : OffsetTable), j))
        = some (({ offsets := o :: os } : OffsetTable), p.size + 8 * (os.length + 1)))
    rw [hoff, hrewrite, ← hsize, hrec, hsize]
    show some (({ offsets := o :: os } : OffsetTable), p.size + 8 + 8 * os.length)
        = some (({ offsets := o :: os } : OffsetTable), p.size + 8 * (os.length + 1))
    rw [show p.size + 8 * (os.length + 1) = p.size + 8 + 8 * os.length by omega]

theorem parseTables_emit (parts : List Header) (ts : List OffsetTable) (p rest : Bytes)
    (hlen : ts.length = parts.length)
    (hok : ∀ q ∈ parts.zip ts, q.2.offsets.length = Parse.chunkCountOf q.1)
    (hbig : ∀ t ∈ ts, ∀ o ∈ t.offsets, o < 2 ^ 64) :
    Parse.parseTables (p ++ (tablesBytes ts ++ rest)) parts p.size
      = some (ts, p.size + 8 * (parts.map Parse.chunkCountOf).sum) := by
  revert hlen hok hbig
  induction parts generalizing ts p rest with
  | nil =>
    intro hlen _ _
    cases ts with
    | nil => rfl
    | cons t ts => simp at hlen
  | cons h parts ih =>
    intro hlen hok hbig
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
      have hok' : ∀ q ∈ parts.zip ts, q.2.offsets.length = Parse.chunkCountOf q.1 :=
        fun q hq => hok q (List.mem_cons_of_mem (h, t) hq)
      have hlen' : ts.length = parts.length := by simpa using hlen
      have heq : t.offsets.length = Parse.chunkCountOf h :=
        hok (h, t) (List.mem_cons_self)
      have hbig' : ∀ x ∈ ts, ∀ o ∈ x.offsets, o < 2 ^ 64 :=
        fun x hx => hbig x (List.mem_cons_of_mem t hx)
      have hbytes : p ++ (tablesBytes (t :: ts) ++ rest)
          = p ++ (offsetTableBytes t.offsets ++ (tablesBytes ts ++ rest)) := by
        rw [tablesBytes_cons, ByteArray.append_assoc]
      rw [hbytes]
      simp only [Parse.parseTables]
      have ht := parseOffsetTable_emit t.offsets p (tablesBytes ts ++ rest)
        (fun o ho => hbig t List.mem_cons_self o ho)
      rw [heq] at ht
      rw [ht]
      have hsize : (p ++ offsetTableBytes t.offsets).size
          = p.size + 8 * t.offsets.length := by
        rw [ByteArray.size_append, offsetTableBytes_size_emit]
      have hbyte2 : p ++ (offsetTableBytes t.offsets ++ (tablesBytes ts ++ rest))
          = (p ++ offsetTableBytes t.offsets) ++ (tablesBytes ts ++ rest) := by
        simp [ByteArray.append_assoc]
      have hrec := ih (ts := ts) (p := p ++ offsetTableBytes t.offsets) (rest := rest)
        (hlen := hlen') (hok := hok') (hbig := hbig')
      show ((match Parse.parseTables
              (p ++ (offsetTableBytes t.offsets ++ (tablesBytes ts ++ rest))) parts
              (p.size + 8 * Parse.chunkCountOf h) with
            | none => none
            | some (ts', k) => some (t :: ts', k))
          = some (t :: ts, p.size + 8 * ((h :: parts).map Parse.chunkCountOf).sum))
      rw [← heq, hbyte2, ← hsize, hrec, hsize]
      show some (t :: ts, p.size + 8 * t.offsets.length + 8 * (parts.map Parse.chunkCountOf).sum)
          = some (t :: ts, p.size + 8 * ((h :: parts).map Parse.chunkCountOf).sum)
      rw [show p.size + 8 * ((h :: parts).map Parse.chunkCountOf).sum
          = p.size + 8 * t.offsets.length + 8 * (parts.map Parse.chunkCountOf).sum by
        simp only [List.map_cons, List.sum_cons]
        omega]

theorem sum_offsets_eq_sum_chunkCount (parts : List Header) (ts : List OffsetTable)
    (hlen : ts.length = parts.length)
    (hok : ∀ q ∈ parts.zip ts, q.2.offsets.length = Parse.chunkCountOf q.1) :
    (ts.map fun t => t.offsets.length).sum = (parts.map Parse.chunkCountOf).sum := by
  revert hlen hok
  induction parts generalizing ts with
  | nil =>
    intro hlen _
    cases ts with
    | nil => rfl
    | cons t ts => simp at hlen
  | cons h parts ih =>
    intro hlen hok
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
      have hok' : ∀ q ∈ parts.zip ts, q.2.offsets.length = Parse.chunkCountOf q.1 :=
        fun q hq => hok q (List.mem_cons_of_mem (h, t) hq)
      have hlen' : ts.length = parts.length := by simpa using hlen
      have heq : t.offsets.length = Parse.chunkCountOf h :=
        hok (h, t) (List.mem_cons_self)
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        ih (ts := ts) (hlen := hlen') (hok := hok'), heq]

theorem putU32LE_magic_size : (putU32LE magicUInt32LE ByteArray.empty).size = 4 := by
  simp [putU32LE]

theorem magicVersionBytes_size (v : Version) : (magicVersionBytes v).size = 8 := by
  unfold magicVersionBytes
  rw [ByteArray.size_append, putU32LE_magic_size, u32Bytes_size_emit]

theorem getU32LE_magicVersion (v : Version) (rest : Bytes) :
    getU32LE (magicVersionBytes v ++ rest) 0 = some magicUInt32LE := by
  unfold magicVersionBytes
  rw [ByteArray.append_assoc]
  rw [getU32LE_append_left
    (a := putU32LE magicUInt32LE ByteArray.empty)
    (b := u32Bytes v.toBits.toNat ++ rest) (i := 0) (by rw [putU32LE_magic_size])]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE]

theorem getU32LE_version (v : Version) (rest : Bytes) :
    getU32LE (magicVersionBytes v ++ rest) 4 = some v.toBits := by
  unfold magicVersionBytes
  rw [ByteArray.append_assoc]
  have h1 : getU32LE (putU32LE magicUInt32LE ByteArray.empty
      ++ (u32Bytes v.toBits.toNat ++ rest))
      ((putU32LE magicUInt32LE ByteArray.empty).size + 0)
      = getU32LE (u32Bytes v.toBits.toNat ++ rest) 0 :=
    getU32LE_append_right' (a := putU32LE magicUInt32LE ByteArray.empty)
      (b := u32Bytes v.toBits.toNat ++ rest) 0
  rw [show (4 : Nat) = (putU32LE magicUInt32LE ByteArray.empty).size + 0 by
    rw [putU32LE_magic_size], h1,
    getU32LE_append_left (a := u32Bytes v.toBits.toNat) (b := rest) (i := 0)
      (by rw [u32Bytes_size_emit])]
  show getU32LE (putU32LE (UInt32.ofNat v.toBits.toNat) ByteArray.empty) 0 = some v.toBits
  rw [show (0 : Nat) = ByteArray.empty.size from rfl, getU32LE_putU32LE]
  rw [show UInt32.ofNat v.toBits.toNat = v.toBits from UInt32.ofNat_toNat]

theorem wire_size_ge (a : RawAttr) : 6 ≤ (RawAttr.wire a).size := by
  rw [RawAttr.wire_size]
  omega

theorem wireAll_size_ge (as : List RawAttr) :
    6 * as.length ≤ (RawAttr.wireAll as).size := by
  rw [RawAttr.wireAll_size]
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hge := wire_size_ge a
    omega

theorem headerBytes_size_ge (attrs : List RawAttr) (hlen : 8 ≤ attrs.length) :
    49 ≤ (headerBytes attrs).size := by
  rw [headerBytes_eq_wireAll]
  simp only [ByteArray.size_append, nulByte_size_emit]
  have hge := wireAll_size_ge attrs
  omega

theorem headerBytes_canonical_size_ge (h : Header) (mp : Bool)
    (hEq : h.attrs = headerAttrs h mp) :
    49 ≤ (headerBytes h.attrs).size := by
  rw [hEq]
  exact headerBytes_size_ge _ (headerAttrs_length_ge h mp)

theorem emitParts_size_ge (parts : List Header) {multipart singleTile deep : Bool}
    (hOK : ∀ h ∈ parts, HeaderEmitOK multipart singleTile deep h) :
    49 * parts.length ≤ (emitParts parts).size := by
  induction parts with
  | nil => simp [emitParts]
  | cons h parts ih =>
    have hOK' : ∀ t ∈ parts, HeaderEmitOK multipart singleTile deep t :=
      fun t ht => hOK t (List.mem_cons_of_mem h ht)
    have hh := hOK h List.mem_cons_self
    rw [emitParts_cons, ByteArray.size_append]
    have hge := headerBytes_canonical_size_ge h multipart hh.attrsEq
    have hrec := ih hOK'
    simp only [List.length_cons]
    omega

theorem filePrefix_size (f : ParsedFile) :
    (filePrefix f).size
      = 8 + (emitParts f.parts).size
        + (if f.version.multipart then 1 else 0)
        + (tablesBytes f.offsetTables).size := by
  unfold filePrefix
  split_ifs with hcond
  · simp only [ByteArray.size_append, magicVersionBytes_size, emitParts_eq_foldl,
      show f.offsetTables.foldl (fun acc t => acc ++ offsetTableBytes t.offsets)
          ByteArray.empty = tablesBytes f.offsetTables from rfl,
      nulByte_size_emit]
    omega
  · simp only [ByteArray.size_append, magicVersionBytes_size, emitParts_eq_foldl,
      show f.offsetTables.foldl (fun acc t => acc ++ offsetTableBytes t.offsets)
          ByteArray.empty = tablesBytes f.offsetTables from rfl]
    omega

theorem parseFile_prefix (v : Version) (rest : Bytes) :
    Parse.parseFile (magicVersionBytes v ++ rest)
      = match Parse.parsePartHeaders (magicVersionBytes v ++ rest) v.longNames
          v.multipart v.nonImage v.singleTile 8
          ((magicVersionBytes v ++ rest).size + 1) with
        | none => none
        | some (parts, i) =>
            match Parse.parseTables (magicVersionBytes v ++ rest) parts i with
            | none => none
            | some (tables, j) => some { version := v, parts := parts,
                                          offsetTables := tables, dataStart := j } := by
  unfold Parse.parseFile
  rw [getU32LE_magicVersion, getU32LE_version]
  show ((match Version.ofBits v.toBits with
      | none => none
      | some v_1 => match Parse.parsePartHeaders (magicVersionBytes v ++ rest) v_1.longNames
          v_1.multipart v_1.nonImage v_1.singleTile 8
          ((magicVersionBytes v ++ rest).size + 1) with
        | none => none
        | some (parts, i) =>
            match Parse.parseTables (magicVersionBytes v ++ rest) parts i with
            | none => none
            | some (tables, j) => some ({ version := v_1, parts := parts,
                                          offsetTables := tables, dataStart := j } : ParsedFile))
      = match Parse.parsePartHeaders (magicVersionBytes v ++ rest) v.longNames
          v.multipart v.nonImage v.singleTile 8
          ((magicVersionBytes v ++ rest).size + 1) with
        | none => none
        | some (parts, i) =>
            match Parse.parseTables (magicVersionBytes v ++ rest) parts i with
            | none => none
            | some (tables, j) => some ({ version := v, parts := parts,
                                          offsetTables := tables, dataStart := j } : ParsedFile))
  rw [Version.ofBits_toBits]

theorem parsePartHeaders_emit_single_list (parts : List Header) (p rest : Bytes)
    (longNames singleTile deep : Bool)
    (hOK : ∀ h ∈ parts, HeaderEmitOK false singleTile deep h)
    (hlen : parts.length = 1)
    (fuel : Nat) (hf : 16 ≤ fuel) :
    Parse.parsePartHeaders (p ++ (emitParts parts ++ rest))
      longNames false deep singleTile p.size fuel
      = some (parts, p.size + (emitParts parts).size) := by
  cases parts with
  | nil => simp at hlen
  | cons h parts =>
    cases parts with
    | nil => exact parsePartHeaders_emit_single h p rest longNames singleTile deep (hOK h List.mem_cons_self) fuel hf
    | cons h' parts => simp at hlen

theorem parseFile_emit (f : ParsedFile) (payload : Bytes) (hok : FileEmitOK f) :
    Parse.parseFile (filePrefix f ++ payload) = some f := by
  have hsizeParts := emitParts_size_ge f.parts hok.headersOK
  have htablesSize := tablesBytes_size f.offsetTables
  have hsum := sum_offsets_eq_sum_chunkCount f.parts f.offsetTables
    hok.tablesCount hok.tablesOK
  by_cases hm : f.version.multipart
  · have hmp : f.version.multipart = true := hm
    have hdecomp : filePrefix f ++ payload
        = magicVersionBytes f.version
          ++ (emitParts f.parts ++ (nulByte ++ (tablesBytes f.offsetTables ++ payload))) := by
      unfold filePrefix
      simp only [ite_eq_left hm, emitParts_eq_foldl,
        show f.offsetTables.foldl (fun acc t => acc ++ offsetTableBytes t.offsets)
            ByteArray.empty = tablesBytes f.offsetTables from rfl,
        ByteArray.append_assoc]
    rw [hdecomp, parseFile_prefix, hmp]
    have hheaders := parsePartHeaders_emit_multipart f.parts (magicVersionBytes f.version)
      (tablesBytes f.offsetTables ++ payload) f.version.longNames
      f.version.singleTile f.version.nonImage
      (fun hh hmem => hmp ▸ hok.headersOK hh hmem)
      ((magicVersionBytes f.version
        ++ (emitParts f.parts ++ (nulByte ++ (tablesBytes f.offsetTables ++ payload)))).size + 1)
      (by
        simp only [ByteArray.size_append, magicVersionBytes_size, nulByte_size_emit]
        omega)
    rw [magicVersionBytes_size] at hheaders
    rw [hheaders]
    have htables : Parse.parseTables
        (magicVersionBytes f.version
          ++ (emitParts f.parts ++ (nulByte ++ (tablesBytes f.offsetTables ++ payload))))
        f.parts (8 + (emitParts f.parts).size + 1)
        = some (f.offsetTables, 8 + (emitParts f.parts).size + 1
            + 8 * (f.parts.map Parse.chunkCountOf).sum) := by
      have h := parseTables_emit f.parts f.offsetTables
        (magicVersionBytes f.version ++ emitParts f.parts ++ nulByte) payload
        hok.tablesCount hok.tablesOK
        (fun t ht o ho => hok.offsetsSmall t ht o ho)
      have hprefix : (magicVersionBytes f.version ++ emitParts f.parts ++ nulByte).size
          = 8 + (emitParts f.parts).size + 1 := by
        rw [ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_append,
          magicVersionBytes_size, nulByte_size_emit]
        omega
      rw [show (magicVersionBytes f.version ++ emitParts f.parts ++ nulByte)
            ++ (tablesBytes f.offsetTables ++ payload)
          = magicVersionBytes f.version
            ++ (emitParts f.parts ++ (nulByte ++ (tablesBytes f.offsetTables ++ payload))) by
        simp [ByteArray.append_assoc], hprefix] at h
      exact h
    simp only [htables]
    have hdata : 8 + (emitParts f.parts).size + 1
          + 8 * (f.parts.map Parse.chunkCountOf).sum = f.dataStart := by
      rw [hok.dataStart, filePrefix_size, ite_eq_left hm]
      omega
    rw [hdata]
  · have hmp : f.version.multipart = false := by
      cases h : f.version.multipart with
      | false => rfl
      | true => exact absurd h hm
    have hlen1 := hok.singlePartLength hmp
    have hdecomp : filePrefix f ++ payload
        = magicVersionBytes f.version
          ++ (emitParts f.parts ++ (tablesBytes f.offsetTables ++ payload)) := by
      unfold filePrefix
      simp only [ite_eq_right hm, emitParts_eq_foldl,
        show f.offsetTables.foldl (fun acc t => acc ++ offsetTableBytes t.offsets)
            ByteArray.empty = tablesBytes f.offsetTables from rfl,
        ByteArray.append_assoc]
    rw [hdecomp, parseFile_prefix, hmp]
    have hheaders := parsePartHeaders_emit_single_list f.parts (magicVersionBytes f.version)
      (tablesBytes f.offsetTables ++ payload) f.version.longNames
      f.version.singleTile f.version.nonImage
      (fun hh hmem => hmp ▸ hok.headersOK hh hmem) hlen1
      ((magicVersionBytes f.version
        ++ (emitParts f.parts ++ (tablesBytes f.offsetTables ++ payload))).size + 1)
      (by
        simp only [ByteArray.size_append, magicVersionBytes_size]
        omega)
    rw [magicVersionBytes_size] at hheaders
    rw [hheaders]
    have htables : Parse.parseTables
        (magicVersionBytes f.version
          ++ (emitParts f.parts ++ (tablesBytes f.offsetTables ++ payload)))
        f.parts (8 + (emitParts f.parts).size)
        = some (f.offsetTables, 8 + (emitParts f.parts).size
            + 8 * (f.parts.map Parse.chunkCountOf).sum) := by
      have h := parseTables_emit f.parts f.offsetTables
        (magicVersionBytes f.version ++ emitParts f.parts) payload
        hok.tablesCount hok.tablesOK
        (fun t ht o ho => hok.offsetsSmall t ht o ho)
      have hsize : (magicVersionBytes f.version ++ emitParts f.parts).size
          = 8 + (emitParts f.parts).size := by
        rw [ByteArray.size_append, magicVersionBytes_size]
      rw [show (magicVersionBytes f.version ++ emitParts f.parts)
            ++ (tablesBytes f.offsetTables ++ payload)
          = magicVersionBytes f.version
            ++ (emitParts f.parts ++ (tablesBytes f.offsetTables ++ payload)) by
        simp [ByteArray.append_assoc], hsize] at h
      exact h
    simp only [htables]
    have hdata : 8 + (emitParts f.parts).size
          + 8 * (f.parts.map Parse.chunkCountOf).sum = f.dataStart := by
      rw [hok.dataStart, filePrefix_size, ite_eq_right hm]
      omega
    rw [hdata]

end Emit
end Exr
