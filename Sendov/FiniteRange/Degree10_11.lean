/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge

/-!
# The batch 10 to 11

`Sendov.R_le_batch` bounds every `R n α` for `10 ≤ n ≤ 11` by the elementary part and
moment at `n₀ = 10` together with the prefactor at `n₁ = 11`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 8, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B10_11

lemma M_lo : M 10 = 9 := by norm_num [M]

lemma M_hi : M 11 = 10 := by norm_num [M]

lemma A_lo (α : ℝ) : A 10 α = 1 - 2 * α / 9 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 11 α = 1 - 2 * α / 10 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 10 α = (54 + 3 * α - 2 * α ^ 2) / (18 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5) : 0 ≤ c 10 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 2520

def betac : ℤ := 82590802561

def tauc : ℤ := 484002949944962611058313401081496854475499965300896802417388157646295122586173254149900368313668004057389423899346929

/-- The moment numerator at `n₀ = 10`, `k = 3`. -/
def Nmomc : List ℤ :=
  [472392, 1312200, 1971216, 3407184, 294192, 12096, 192]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 10) (gg1 10) (gg2 10) 3)) α := by
  refine pev_wsum_eq_of_packed (gg0 10) (gg1 10) (gg2 10) 3 10 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 10) (gg1 10) (gg2 10) 3 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 10) (gg1 10) (gg2 10) 3 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 10) (gg1 10) (gg2 10) 3 (by simp) (by simp) (by simp) 3)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 10 α t ^ 3)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 10 * (3 + α)) ^ 3) :=
  integral_moment_packed 10 3 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-8 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 8 * P α` is a positive combination of `αʲ (17-α)^(8-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5) :
    0 < 32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8 := by
  have hu : (0 : ℝ) ≤ 5 - α := by linarith
  have hid : (5 : ℝ) ^ 8 * (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) = 32349375 * (5 - α) ^ 8 + 454695525 * α ^ 1 * (5 - α) ^ 7 + 2529253350 * α ^ 2 * (5 - α) ^ 6 + 4382737200 * α ^ 3 * (5 - α) ^ 5 + 5044170375 * α ^ 4 * (5 - α) ^ 4 + 11732079375 * α ^ 5 * (5 - α) ^ 3 + 18187642400 * α ^ 6 * (5 - α) ^ 2 + 11329113600 * α ^ 7 * (5 - α) ^ 1 + 2070835200 * α ^ 8 := by
    ring
  -- All coefficients are checked by positivity. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  apply (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < (5 : ℝ) ^ 8)).mp
  rw [hid]
  rcases lt_or_eq_of_le hα with hpos | hzero
  · positivity
  · have hu_pos : (0 : ℝ) < 5 - α := by linarith
    positivity

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `10 ≤ n ≤ 11`.** -/
theorem finite_range {n : ℕ} (h0 : 10 ≤ n) (h1 : n ≤ 11) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 5 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (11 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (11 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 10) (n := n) (n₁ := 11) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((10 : ℕ) : ℝ) - 4 = 6 by norm_num] at hb
  rw [show (6 : ℝ) / 2 = ((3 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 9) + 1 / (4 * 9 * (3 + α))
      + (1 - 2 * α / 10) ^ 2 * 11 * 10 * (11 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 9 * (3 + α)) ^ 3))
      = 1 - (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) / (680400 * (3 + α) ^ 4) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) / (680400 * (3 + α) ^ 4) := div_pos hP (by positivity)
  linarith

end B10_11

end Sendov
