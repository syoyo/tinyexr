/-
  TinyEXR - DDS/KTX header byte-layout checker (C vs Lean).

  Reads vectors emitted by `test/v3/dds_ktx_vectors.c`
  (`dds <w> <h> <dxgi> <block> | <hex>` and
  `ktx <w> <h> <internal> <base> <payload> | <hex>`) and compares the
  bytes produced by the Lean model (`wordsConcat (ddsWords h)` /
  `wordsConcat (ktxWords h)`) with the C writers' output.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Texcomp.Container

open Texcomp

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def byteHex (b : UInt8) : String :=
  let v := b.toNat
  String.ofList [hexDigit (v / 16), hexDigit (v % 16)]

def bytesHex (b : ByteArray) : String :=
  String.join ((b.toList).map byteHex)

def decNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def fields (s : String) : List String :=
  (s.splitOn " ").filter (fun f => f != "")

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
        pure (bytesHex (emitDdsHeader h ByteArray.empty))
      else if kind == "ktx" then
        let h : KtxHeader :=
          { width := UInt32.ofNat (decNat (toks.getD 1 ""))
            height := UInt32.ofNat (decNat (toks.getD 2 ""))
            internalFormat := UInt32.ofNat (decNat (toks.getD 3 ""))
            baseFormat := UInt32.ofNat (decNat (toks.getD 4 ""))
            payloadSize := UInt32.ofNat (decNat (toks.getD 5 "")) }
        pure (bytesHex (emitKtxHeader h ByteArray.empty))
      else
        pure ""
    if got != want then
      bad := bad + 1
      if bad <= 6 then
        IO.eprintln s!"line {idx + 1} {kind}: got  {got}\n            want {want}"
  IO.println s!"{lines.length} headers checked, {bad} mismatches"
  if bad != 0 then
    throw (IO.userError "dds/ktx layout mismatch")
