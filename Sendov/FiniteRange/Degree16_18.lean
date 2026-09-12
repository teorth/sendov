/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge
import Sendov.Common.BernsteinCert

/-!
# The batch 16 to 18

`Sendov.R_le_batch` bounds every `R n α` for `16 ≤ n ≤ 18` by the elementary part and
moment at `n₀ = 16` together with the prefactor at `n₁ = 18`, so one moment and one
certificate serve all 3 degrees.  The certificate has degree 14, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B16_18

lemma M_lo : M 16 = 15 := by norm_num [M]

lemma M_hi : M 18 = 17 := by norm_num [M]

lemma A_lo (α : ℝ) : A 16 α = 1 - 2 * α / 15 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 18 α = 1 - 2 * α / 17 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 16 α = (90 + 9 * α - 2 * α ^ 2) / (30 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17 / 2) : 0 ≤ c 16 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 720720

def betac : ℤ := 9632409706279062743041

def tauc : ℤ := 65604308031184443540574573963916799164579355278379645304399696021576697292522316333712207898845459456442843781680661940474008113586613026045908148093916427474204047696513917860869931635574183554403391853205017812541311293282390174744915537500427122031507443987808875231567434632560187716182055857676129052451323844518845444325992588835078239595296506721823714704265478805643382244491222183969521021663658026171379394048234274188519553

/-- The moment numerator at `n₀ = 16`, `k = 6`. -/
def Nmomc : List ℤ :=
  [52612659000000, 170273696400000, 255339685800000, 239918448960000, 165235950648000, 99966121176960, 96500543870016, 8976458195712, 533837640960, 20291420160, 478172160, 6377472, 36864]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 16) (gg1 16) (gg2 16) 6)) α := by
  refine pev_wsum_eq_of_packed (gg0 16) (gg1 16) (gg2 16) 6 19 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 16) (gg1 16) (gg2 16) 6 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 16) (gg1 16) (gg2 16) 6 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 16) (gg1 16) (gg2 16) 3 (by simp) (by simp) (by simp) 6)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 16 α t ^ 6)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 16 * (3 + α)) ^ 6) :=
  integral_moment_packed 16 6 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-14 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 14 * P α` is a positive combination of `αʲ (17-α)^(14-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 17 / 2) :
    0 < 308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14 := by
  have hu : (0 : ℝ) ≤ 17 - 2 * α := by linarith
  have hid : (17 : ℝ) ^ 14 * (308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14) = 308547940078125 * (17 - 2 * α) ^ 14 + 20816010191643750 * α ^ 1 * (17 - 2 * α) ^ 13 + 631515530954221875 * α ^ 2 * (17 - 2 * α) ^ 12 + 11358598773482842500 * α ^ 3 * (17 - 2 * α) ^ 11 + 134099015737057493625 * α ^ 4 * (17 - 2 * α) ^ 10 + 1075072539293623306170 * α ^ 5 * (17 - 2 * α) ^ 9 + 5177641117293101872899 * α ^ 6 * (17 - 2 * α) ^ 8 + 13260545037504883513944 * α ^ 7 * (17 - 2 * α) ^ 7 + 13392270163441462237560 * α ^ 8 * (17 - 2 * α) ^ 6 + 934363054464939802080 * α ^ 9 * (17 - 2 * α) ^ 5 + 56141276222621229749280 * α ^ 10 * (17 - 2 * α) ^ 4 + 269593608305522330908544 * α ^ 11 * (17 - 2 * α) ^ 3 + 451523429099140347738624 * α ^ 12 * (17 - 2 * α) ^ 2 + 320966535936278232000000 * α ^ 13 * (17 - 2 * α) ^ 1 + 72913603873782672000000 * α ^ 14 := by
    ring
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (17 - 2 * α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `16 ≤ n ≤ 18`.** -/
theorem finite_range {n : ℕ} (h0 : 16 ≤ n) (h1 : n ≤ 18) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (18 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (18 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 16) (n := n) (n₁ := 18) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((16 : ℕ) : ℝ) - 4 = 12 by norm_num] at hb
  rw [show (12 : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 15) + 1 / (4 * 15 * (3 + α))
      + (1 - 2 * α / 17) ^ 2 * 18 * 17 * (18 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 15 * (3 + α)) ^ 6))
      = 1 - (308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14) / (215371406250 * (3 + α) ^ 7) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  exact hb.trans_lt (sub_lt_self _ (div_pos hP (by positivity)))

end B16_18

end Sendov
