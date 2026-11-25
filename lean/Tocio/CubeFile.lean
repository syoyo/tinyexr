/-
  TinyEXR - Lean 4 model of the Iridas `.cube` LUT reader
  (`load_cube` in `sandbox/tocio/src/toc_lutfile.c`).

  Total, fuel-bounded, and uses the same libm-free decimal float / int
  readers as `Tocio.SpiFile` (`toc_parse_float` / `toc_parse_int`).
  Allocation is guarded by `spiValuesFit` (`toc_values_fit`), so short
  buffers cannot reach the LUT kernels.

  Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
  SPDX-License-Identifier: BSD-3-Clause
-/
import Tocio.SpiFile

namespace Tocio

set_option linter.unusedVariables false

structure CubeContent where
  dim : Nat          -- 1 or 3
  size : Nat         -- 2..256
  domainMin : List Float32
  domainMax : List Float32
  data : List Float32
  deriving Repr

/-- State threaded by the `.cube` parse loop. -/
structure CubeState where
  dim : Nat := 0
  size : Nat := 0
  want : Nat := 0
  got : Nat := 0
  dmin : List Float32 := [0.0, 0.0, 0.0]
  dmax : List Float32 := [1.0, 1.0, 1.0]
  arr : List Float32 := []
  deriving Repr

def cubeSkipLine (cs : List Char) : List Char :=
  match cs.dropWhile (fun c => c != '\n') with
  | [] => []
  | _ :: rest => rest

def cubeSet3 (xs : List Float32) (c : Nat) (v : Float32) : List Float32 :=
  (xs.take c) ++ [v] ++ (xs.drop (c + 1))

def cubeSet3At (c : Nat) (v : Float32) (xs : List Float32) : List Float32 := cubeSet3 xs c v

/-- One parse step. Returns the advanced state and remainder on success. -/
def cubeStep (st : CubeState) (cs : List Char) : Option (CubeState × List Char) :=
  let cs := skipWs cs
  match cs with
  | [] => some (st, [])
  | _ =>
    if peekWord cs then
      let (w, rest) := readWord cs
      if w == "TITLE" then some (st, cubeSkipLine rest)
      else if w == "LUT_1D_SIZE" || w == "LUT_3D_SIZE" then do
        if st.arr.length != 0 || st.size != 0 then none
        let (n, rest') ← readInt rest
        if n < 2 || n > 256 then none
        let sz : Nat := n.toNat
        let want := if w == "LUT_1D_SIZE" then sz * 3 else sz * sz * sz * 3
        if !spiValuesFit want (rest'.length + 1) then none
        some ({ st with dim := if w == "LUT_1D_SIZE" then 1 else 3,
                         size := sz, want := want }, rest')
      else if w == "DOMAIN_MIN" || w == "DOMAIN_MAX" then do
        let (a, r1) ← readF32 rest
        let (b, r2) ← readF32 r1
        let (c, r3) ← readF32 r2
        let fld := if w == "DOMAIN_MIN" then cubeSet3 st.dmin else cubeSet3 st.dmax
        some ({ st with dmin := if w == "DOMAIN_MIN" then fld 0 a |> cubeSet3At 1 b |> cubeSet3At 2 c
                               else st.dmin,
                        dmax := if w == "DOMAIN_MAX" then fld 0 a |> cubeSet3At 1 b |> cubeSet3At 2 c
                               else st.dmax }, r3)
      else if w == "LUT_1D_INPUT_RANGE" || w == "LUT_3D_INPUT_RANGE" then do
        let (a, r1) ← readF32 rest
        let (b, r2) ← readF32 r1
        some ({ st with dmin := [a, a, a], dmax := [b, b, b] }, r2)
      else some (st, cubeSkipLine rest)
    else do
      if st.size == 0 then none
      let (r, r1) ← readF32 cs
      let (g, r2) ← readF32 r1
      let (b, r3) ← readF32 r2
      if st.got + 3 > st.want then none
      some ({ st with got := st.got + 3, arr := st.arr ++ [r, g, b] }, r3)

def cubeLoop : Nat → CubeState → List Char → Option (CubeState × List Char)
  | 0, st, cs => some (st, cs)
  | fuel + 1, st, cs =>
    match cubeStep st cs with
    | none => none
    | some (st', cs') =>
      if cs' == cs then some (st', cs')
      else cubeLoop fuel st' cs'

def loadCube (src : String) : Option CubeContent := do
  let (st, _) ← cubeLoop (src.length + 1) {} src.toList
  if st.size == 0 || st.arr.length != st.want then none
  some { dim := st.dim, size := st.size, domainMin := st.dmin,
         domainMax := st.dmax, data := st.arr }

theorem cubeFile_valuesFit_sound {want avail : Nat} (h : spiValuesFit want avail = true) :
    want ≤ avail / 2 + 1 := by
  simpa [spiValuesFit] using h

end Tocio
