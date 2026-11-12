/-
  TinyEXR - DDS/KTX complete-file checker (C writers vs Lean model).

  Reads vectors emitted by `test/v3/dds_ktx_vectors.c`
  (`dds <w> <h> <dxgi> <block> | <full-file hex>`,
  `ktx <w> <h> <internal> <base> <payload> | <full-file hex>`,
  `astc <bx> <by> <w> <h> <v> <outsize> | <full-file hex or empty>` and
  verdict-only `E dds|ktx|astc ... <outsize> <v>` records, where v = 0 means
  TC_SUCCESS and v = 1 means TC_ERROR_INVALID_ARGUMENT) and compares
  the complete file — header *and* block payload — produced by the Lean
  model (`emitDdsFile` / `emitKtxFile` / `emitAstcFile`) with the C writers'
  output, plus the writer verdicts (`ddsWriteVerdict` / `ktxWriteVerdict` /
  `astcWriteFileVerdict`). The
  payload uses the deterministic pattern `(i * 37 + 11) & 0xFF` that both
  sides compute independently, so this checks the header layout, the
  derived payload size, and the header/payload join in one shot.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Container

open Texcomp

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def byteHex (b : UInt8) : String :=
  String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def bytesHex (b : ByteArray) : String :=
  String.join ((b.toList).map byteHex)

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

/-- The shared deterministic payload pattern. -/
def pat (i : Nat) : UInt8 := UInt8.ofNat ((i * 37 + 11) % 256)

def patBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.mk ((List.range n).map pat))

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "/tmp/opencode/dds_ktx_vectors.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun l => l != "")
  let mut bad := 0
  for (idx, line) in List.zip (List.range lines.length) lines do
    let sections := line.splitOn "|"
    let toks := fields (sections.getD 0 "")
    let want := (sections.getD 1 "").trimAscii.toString
    let kind := toks.getD 0 ""
    let got ←
      if kind == "dds" then
        let h : DdsHeader :=
          { width := UInt32.ofNat (decNat (toks.getD 1 ""))
            height := UInt32.ofNat (decNat (toks.getD 2 ""))
            dxgi := UInt32.ofNat (decNat (toks.getD 3 ""))
            blockBytes := UInt32.ofNat (decNat (toks.getD 4 "")) }
        pure (bytesHex (emitDdsFile ⟨h, patBytes (ddsPayloadSize h)⟩))
      else if kind == "ktx" then
        let h : KtxHeader :=
          { width := UInt32.ofNat (decNat (toks.getD 1 ""))
            height := UInt32.ofNat (decNat (toks.getD 2 ""))
            internalFormat := UInt32.ofNat (decNat (toks.getD 3 ""))
            baseFormat := UInt32.ofNat (decNat (toks.getD 4 ""))
            payloadSize := UInt32.ofNat (decNat (toks.getD 5 "")) }
        pure (bytesHex (emitKtxFile ⟨h, patBytes h.payloadSize.toNat⟩))
      else if kind == "astc" then
        let hdr : AstcFileHeader :=
          { blockX := decNat (toks.getD 1 "")
            blockY := decNat (toks.getD 2 "")
            width := decNat (toks.getD 3 "")
            height := decNat (toks.getD 4 "") }
        let v := decNat (toks.getD 5 "")
        let outSize := decNat (toks.getD 6 "")
        if v == 0 then
          pure (bytesHex (emitAstcFile ⟨hdr, patBytes (astcFilePayloadSize hdr)⟩))
        else if astcWriteFileVerdict hdr outSize then
          pure "VERDICT-MISMATCH"
        else
          pure ""
      else if kind == "E" then
        -- Verdict-only record: `E <sub> ... <outsize> <v>` with
        -- v = 0 (TC_SUCCESS) or 1 (TC_ERROR_INVALID_ARGUMENT). The model and
        -- the C writer must agree on the verdict.
        let sub := toks.getD 1 ""
        if sub == "dds" then
          let h : DdsHeader :=
            { width := UInt32.ofNat (decNat (toks.getD 2 ""))
              height := UInt32.ofNat (decNat (toks.getD 3 ""))
              dxgi := 0
              blockBytes := UInt32.ofNat (decNat (toks.getD 4 "")) }
          let ok := ddsWriteVerdict h (decNat (toks.getD 5 ""))
          let v := decNat (toks.getD 6 "")
          pure (if (ok && v == 0) || (!ok && v == 1) then "" else "VERDICT-MISMATCH")
        else if sub == "ktx" then
          let h : KtxHeader :=
            { width := UInt32.ofNat (decNat (toks.getD 2 ""))
              height := UInt32.ofNat (decNat (toks.getD 3 ""))
              internalFormat := 0
              baseFormat := 0
              payloadSize := UInt32.ofNat (decNat (toks.getD 4 "")) }
          let ok := ktxWriteVerdict h (decNat (toks.getD 5 ""))
          let v := decNat (toks.getD 6 "")
          pure (if (ok && v == 0) || (!ok && v == 1) then "" else "VERDICT-MISMATCH")
        else if sub == "astc" then
          let hdr : AstcFileHeader :=
            { blockX := decNat (toks.getD 2 "")
              blockY := decNat (toks.getD 3 "")
              width := decNat (toks.getD 4 "")
              height := decNat (toks.getD 5 "") }
          let ok := astcWriteFileVerdict hdr (decNat (toks.getD 6 ""))
          let v := decNat (toks.getD 7 "")
          pure (if (ok && v == 0) || (!ok && v == 1) then "" else "VERDICT-MISMATCH")
        else
          pure ""
      else
        pure ""
    if got != want then
      bad := bad + 1
      if bad <= 4 then
        IO.eprintln s!"line {idx + 1} {kind}: got  {got}\n            want {want}"
  IO.println s!"{lines.length} complete files checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "dds/ktx file layout mismatch")
