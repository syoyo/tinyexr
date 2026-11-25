/-
   TinyEXR - output-size contracts for texcomp float decompression wrappers.

   Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
   SPDX-License-Identifier: BSD-3-Clause
-/

import Texcomp.FloatOutput
import Mathlib.Tactic

namespace Texcomp

set_option linter.unusedVariables false

theorem halfTriplesToRgbaF_length (hs : List UInt16) :
    (halfTriplesToRgbaF hs).length = (hs.length / 3) * 4 := by
  induction hs using halfTriplesToRgbaF.induct with
  | case1 => simp [halfTriplesToRgbaF]
  | case2 r g b rest ih =>
      simp only [halfTriplesToRgbaF, List.length_cons] at ih ⊢
      omega
  | case3 t hne hnot3 =>
      cases t with
      | nil => exact (hne rfl).elim
      | cons a t =>
          cases t with
          | nil => simp [halfTriplesToRgbaF]
          | cons b t =>
              cases t with
              | nil => simp [halfTriplesToRgbaF]
              | cons c t => exact (hnot3 a b c t rfl).elim

theorem map_foldr_append_length {α β : Type} (l : List α) (f : α → List β) (c : Nat)
    (hf : ∀ x ∈ l, (f x).length = c) :
    ((l.map f).foldr (· ++ ·) []).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := hf x (by simp)
      have hxs := ih (fun y hy => hf y (by simp [hy]))
      simp only [List.map_cons, List.foldr_cons, List.length_append, hx, hxs,
        List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem range_foldr_append_length {β : Type} (n : Nat) (f : Nat → List β) (c : Nat)
    (hf : ∀ k, (f k).length = c) :
    ((List.range n).foldr (fun k acc => f k ++ acc) []).length = n * c := by
  rw [← List.foldr_map]
  change (((List.range n).map f).foldr (fun a acc => a ++ acc) []).length = n * c
  rw [map_foldr_append_length (List.range n) f c (fun k _ => hf k), List.length_range]

theorem bc6hDecodeRgb16f_length (data : List UInt8) (w h : Nat) (sf : Bool)
    (out : List UInt16) (hout : bc6hDecodeRgb16f data w h sf = some out) :
    out.length = 3 * w * h := by
  by_cases hz : w == 0 || h == 0
  · simp [bc6hDecodeRgb16f, hz] at hout
    subst out
    simp only [List.length_nil]
    have hw : w = 0 ∨ h = 0 := by simpa using hz
    rcases hw with rfl | rfl <;> simp
  · simp only [Bool.or_eq_true, beq_iff_eq] at hz
    have hz' : (w == 0 || h == 0) = false := by simpa using hz
    by_cases hs : data.length < bc6hImageBytes2 w h
    · simp [bc6hDecodeRgb16f, hz', hs] at hout
    · simp [bc6hDecodeRgb16f, hz', hs, Option.some.injEq] at hout
      subst out
      have hlen := range_foldr_append_length (w * h)
        (fun k => let x := k % w
          let y := k / w
          let bi := (y / 4) * blocksX w 4 + x / 4
          let t := (y % 4) * 4 + x % 4
          let c := bc6hDecodeBlock (blockBytes data bi 16) sf ⟨t, by omega⟩
          [c.1, c.2.1, c.2.2]) 3 (by intro k; rfl)
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlen

theorem bc6hDecodeRgbaf_length (data : List UInt8) (w h : Nat) (sf : Bool)
    (out : List Float32) (hout : bc6hDecodeRgbaf data w h sf = some out) :
    out.length = 4 * w * h := by
  cases hh : bc6hDecodeRgb16f data w h sf with
  | none => simp [bc6hDecodeRgbaf, hh] at hout
  | some hs =>
      simp only [bc6hDecodeRgbaf, hh, Option.map_some, Option.some.injEq] at hout
      subst out
      have hlen := bc6hDecodeRgb16f_length data w h sf hs hh
      rw [halfTriplesToRgbaF_length, hlen, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
      ring

theorem bc7DecodeRgbaf_length (data : List UInt8) (w h : Nat)
    (out : List Float32) (hout : bc7DecodeRgbaf data w h = some out) :
    out.length = 4 * w * h := by
  cases hb : bc7DecodeImage2 data w h with
  | none => simp [bc7DecodeRgbaf, hb] at hout
  | some bs =>
      simp only [bc7DecodeRgbaf, hb, Option.map_some, Option.some.injEq] at hout
      subst out
      simp only [List.length_map]
      by_cases hz : w == 0 || h == 0
      · simp [bc7DecodeImage2, hz] at hb
        obtain ⟨_, hbs⟩ := hb
        subst bs
        simp
        have hw : w = 0 ∨ h = 0 := by simpa using hz
        rcases hw with rfl | rfl <;> simp
      · simp only [Bool.or_eq_true, beq_iff_eq] at hz
        have hz' : (w == 0 || h == 0) = false := by simpa using hz
        by_cases hs : data.length < bc7ImageBytes2 w h
        · simp [bc7DecodeImage2, hs] at hb
        · simp [bc7DecodeImage2, hs, hz', Option.some.injEq] at hb
          subst bs
          have hlen := range_foldr_append_length (w * h)
            (fun k => bc7Pixel data ((w + 3) / 4) k w) 4
            (fun k => bc7Pixel_length data ((w + 3) / 4) k w)
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlen

theorem astcHdrDecodeRgbaf_length (data : List UInt8) (w h bx byy : Nat)
    (out : List Float32) (hout : astcHdrDecodeRgbaf data w h bx byy = some out) :
    out.length = 4 * w * h := by
  by_cases hw : w == 0
  · simp at hw
    simp [astcHdrDecodeRgbaf, hw] at hout
    subst out
    simp [hw]
  by_cases hh : h == 0
  · simp at hh
    simp [astcHdrDecodeRgbaf, hw, hh] at hout
    subst out
    simp [hh]
  by_cases hbx : bx == 0
  · simp [astcHdrDecodeRgbaf, hw, hh, hbx] at hout
  by_cases hby : byy == 0
  · simp [astcHdrDecodeRgbaf, hw, hh, hbx, hby] at hout
  by_cases hr : bx > 12 || byy > 12
  · simp [astcHdrDecodeRgbaf, hw, hh, hbx, hby, hr] at hout
  · have hw' : (w == 0) = false := by simpa using hw
    have hh' : (h == 0) = false := by simpa using hh
    have hbx' : (bx == 0) = false := by simpa using hbx
    have hby' : (byy == 0) = false := by simpa using hby
    have hr' : (bx > 12 || byy > 12) = false := by simpa using hr
    by_cases hs : data.length < blocksX w bx * ((h + byy - 1) / byy) * 16
    · simp [astcHdrDecodeRgbaf, hw', hh', hbx', hby', hr', hs] at hout
    · simp [astcHdrDecodeRgbaf, hw', hh', hbx', hby', hr', hs, Option.some.injEq] at hout
      subst out
      have hbxp : 0 < bx := Nat.pos_of_ne_zero (by simpa using hbx')
      have hbyp : 0 < byy := Nat.pos_of_ne_zero (by simpa using hby')
      have hlen := range_foldr_append_length (w * h)
        (fun k => let x := k % w
          let y := k / w
          let bi := (y / byy) * blocksX w bx + x / bx
          let t := (y % byy) * bx + x % bx
          let raw : List Nat := (List.range 16).map
            (fun i => (data.getD (bi * 16 + i) 0).toNat)
          let c := astcDecodeBlockHdr raw bx byy
            ⟨t % (bx * byy), Nat.mod_lt _ (Nat.mul_pos hbxp hbyp)⟩
          [c.1, c.2.1, c.2.2.1, c.2.2.2]) 4 (by intro k; rfl)
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlen

end Texcomp
