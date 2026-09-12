/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.FiniteRange.Batch
import Sendov.FiniteRange.PackBridge
import Sendov.Common.BernsteinCert

/-!
# The batch 14 to 15

`Sendov.R_le_batch` bounds every `R n α` for `14 ≤ n ≤ 15` by the elementary part and
moment at `n₀ = 14` together with the prefactor at `n₁ = 15`, so one moment and one
certificate serve all 2 degrees.  The certificate has degree 12, set by `n₀` rather
than `n₁`.

Feasibility at `n₀` is proved rather than assumed: for `n ≥ 36` it follows from
`0 ≤ α ≤ 17`, since `A - c²` increases with `n`.  This matters because feasibility propagates
*upward* in `n`, so it could not be inherited from the hypothesis at `n`.
-/

-- Generated numerals cannot be wrapped, so the long-line linter is off in this file.
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace Sendov

namespace B14_15

lemma M_lo : M 14 = 13 := by norm_num [M]

lemma M_hi : M 15 = 14 := by norm_num [M]

lemma A_lo (α : ℝ) : A 14 α = 1 - 2 * α / 13 := by rw [A, M]; push_cast; ring

lemma A_hi (α : ℝ) : A 15 α = 1 - 2 * α / 14 := by rw [A, M]; push_cast; ring

lemma c_lo {α : ℝ} (hα : 0 ≤ α) : c 14 α = (78 + 7 * α - 2 * α ^ 2) / (26 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c, M]
  push_cast
  field_simp
  ring

/-- `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
which for `n₀ < 36` does not follow from `α ≤ 17`. -/
lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 7) : 0 ≤ c 14 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

def Lc : ℤ := 360360

def betac : ℤ := 5273811281588129281

def tauc : ℤ := 5240604256749137818001775409217258559398270598665938104246888891334041344492138378350247489747112270657502763060533670335383336131627922353242397074581977699087266735169689253384888787652968648421800644465440084079049341105429958677566179709215175220574978194512241977108241372511737172688952893630525928871748289

/-- The moment numerator at `n₀ = 14`, `k = 5`. -/
def Nmomc : List ℤ :=
  [259845693120, 782498283840, 1107091851840, 1019339156160, 768295987680, 853275774240, 79511527040, 4444832000, 147210240, 2670080, 20480]

theorem pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 14) (gg1 14) (gg2 14) 5)) α := by
  refine pev_wsum_eq_of_packed (gg0 14) (gg1 14) (gg2 14) 5 16 Lc betac
    tauc Nmomc (by norm_num [betac]) (by norm_num [tauc]) ?_ ?_ ?_ ?_ ?_ ?_ α
  · refine rowZ_bound (gg0 14) (gg1 14) (gg2 14) 5 3 betac tauc
      (by norm_num [betac]) (by simp) (by simp) (by simp) ?_
    norm_num [gg0, gg1, gg2, l1, betac, tauc]
  · decide
  · refine wsum_bound (gg0 14) (gg1 14) (gg2 14) 5 Lc betac
      (by norm_num [Lc]) ?_
    norm_num [gg0, gg1, gg2, l1, Lc, betac]
  · decide
  · exact wsum_length_le Lc _ 0
      (qrow_entry_length_le (gg0 14) (gg1 14) (gg2 14) 3 (by simp) (by simp) (by simp) 5)
  · rfl

theorem integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 14 α t ^ 5)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 14 * (3 + α)) ^ 5) :=
  integral_moment_packed 14 5 (by norm_num) α hα Lc (by norm_num [Lc]) Nmomc
    (by decide) (pev_Nmomc α)

set_option maxHeartbeats 2000000 in
-- the degree-12 Bernstein identity exceeds the default budget
/-- The certificate: `17 ^ 12 * P α` is a positive combination of `αʲ (17-α)^(12-j)`. -/
lemma P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 7) :
    0 < 4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12 := by
  have hu : (0 : ℝ) ≤ 7 - α := by linarith
  have hid : (7 : ℝ) ^ 12 * (4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12) = 4540012290450 * (7 - α) ^ 12 + 117485542519254 * α ^ 1 * (7 - α) ^ 11 + 1346380586202834 * α ^ 2 * (7 - α) ^ 10 + 8957703596562630 * α ^ 3 * (7 - α) ^ 9 + 37714860895632375 * α ^ 4 * (7 - α) ^ 8 + 91053479724275985 * α ^ 5 * (7 - α) ^ 7 + 128817765797828254 * α ^ 6 * (7 - α) ^ 6 + 133833540832996984 * α ^ 7 * (7 - α) ^ 5 + 161773229978174745 * α ^ 8 * (7 - α) ^ 4 + 197834312331965435 * α ^ 9 * (7 - α) ^ 3 + 152113356071582990 * α ^ 10 * (7 - α) ^ 2 + 57359456154000000 * α ^ 11 * (7 - α) ^ 1 + 7376986416800000 * α ^ 12 := by
    ring
  -- The certificate checks coefficient signs. The last summand is positive for α > 0;
  -- at α = 0 the first summand is positive. The identity above checks every coefficient.
  bernstein_cert α (7 - α) using hid

set_option maxHeartbeats 2000000 in
-- clearing denominators across the batch identity exceeds the default budget
/-- **The batch `14 ≤ n ≤ 15`.** -/
theorem finite_range {n : ℕ} (h0 : 14 ≤ n) (h1 : n ≤ 15) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 7 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (15 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (15 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 14) (n := n) (n₁ := 15) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((14 : ℕ) : ℝ) - 4 = 10 by norm_num] at hb
  rw [show (10 : ℝ) / 2 = ((5 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 13) + 1 / (4 * 13 * (3 + α))
      + (1 - 2 * α / 14) ^ 2 * 15 * 14 * (15 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 13 * (3 + α)) ^ 5))
      = 1 - (4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12) / (9606092496 * (3 + α) ^ 6) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  exact hb.trans_lt (sub_lt_self _ (div_pos hP (by positivity)))

end B14_15

end Sendov
