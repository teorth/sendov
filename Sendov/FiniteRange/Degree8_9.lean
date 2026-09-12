/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge

/-!
# The batch 8 to 9

`Sendov.R_le_batch` bounds every `R n α` for `8 ≤ n ≤ 9` by the elementary part and
moment at `n₀ = 8` together with the prefactor at `n₁ = 9`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 6, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B8_9

lemma M_lo : M 8 = 7 := by norm_num [M]

lemma M_hi : M 9 = 8 := by norm_num [M]

lemma A_lo (α : ℝ) : A 8 α = 1 - 2 * α / 7 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 9 α = 1 - 2 * α / 8 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 8 α = (42 + 1 * α - 2 * α ^ 2) / (14 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 4) : 0 ≤ c 8 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 840

def betac : ℤ := 63228481

def tauc : ℤ := 304104393583393026770083796931785379693060776623910754345993

/-- The moment numerator at `n₀ = 8`, `k = 2`. -/
def Nmomc : List ℤ :=
  [5292, 15960, 40620, 3056, 80]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 8) (gg1 8) (gg2 8) 2)) α := by
  refine pev_wsum_eq_of_packed (gg0 8) (gg1 8) (gg2 8) 2 7 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 8) (gg1 8) (gg2 8) 2 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 8) (gg1 8) (gg2 8) 2 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 8) (gg1 8) (gg2 8) 3 (by simp) (by simp) (by simp) 2)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 8 α t ^ 2)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 8 * (3 + α)) ^ 2) :=
  integral_moment_packed 8 2 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-6 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 6 * P α` is a positive combination of `αʲ (17-α)^(6-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) :
    0 < 656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6 := by
  have hu : (0 : ℝ) ≤ 4 - α := by linarith
  have hid : (4 : ℝ) ^ 6 * (656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6) = 656208 * (4 - α) ^ 6 + 5568192 * α ^ 1 * (4 - α) ^ 5 + 3952608 * α ^ 2 * (4 - α) ^ 4 + 13001408 * α ^ 3 * (4 - α) ^ 3 + 51075024 * α ^ 4 * (4 - α) ^ 2 + 49486080 * α ^ 5 * (4 - α) ^ 1 + 11634560 * α ^ 6 := by
    ring
  -- The Bernstein summands are nonnegative. If α > 0 the last one is positive;
  -- at α = 0 the first one is positive. No per-coefficient hypotheses are needed.
  apply (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 6)).mp
  rw [hid]
  rcases lt_or_eq_of_le hα with hpos | hzero
  · positivity
  · have hu_pos : (0 : ℝ) < 4 - α := by linarith
    positivity

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `8 ≤ n ≤ 9`.** -/
theorem finite_range {n : ℕ} (h0 : 8 ≤ n) (h1 : n ≤ 9) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 4 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (9 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 8) (n := n) (n₁ := 9) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((8 : ℕ) : ℝ) - 4 = 4 by norm_num] at hb
  rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 7) + 1 / (4 * 7 * (3 + α))
      + (1 - 2 * α / 8) ^ 2 * 9 * 8 * (9 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 7 * (3 + α)) ^ 2))
      = 1 - (656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6) / (47040 * (3 + α) ^ 3) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6) / (47040 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith

end B8_9

end Sendov
