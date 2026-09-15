/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Rpow

/-!
# The actual quadratic

`QQ c A t = 1 - 2ct + At²` supports actual polar/origin coordinates and scalar kernels.
The letters `c` and `A` here are independent real parameters, not an obsolete substitution.
-/

namespace Sendov

/-- The quadratic `1 - 2ct + At²`. -/
noncomputable def QQ (c A t : ℝ) : ℝ := 1 - 2 * c * t + A * t ^ 2

variable {c A t : ℝ}

/-- `QQ` as a sum of squares. -/
lemma QQ_eq (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by
  simp only [QQ]; ring

lemma QQ_one (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by simp [QQ]

/-- Feasibility `c² ≤ A` says exactly that `QQ` is a sum of squares. -/
lemma QQ_nonneg (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by
  rw [QQ_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.2 hfeas) (sq_nonneg _))

/-- Below the vertex, `QQ` lies under the chord `1 - ct`. -/
lemma QQ_le_chord (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]

/-- Above the vertex, `QQ` is increasing, so it is at most its value at `t = 1`. -/
lemma QQ_le_at_one (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by
  have hkey : 0 ≤ A * (1 + t) - 2 * c := by nlinarith [ht, hA, ht1]
  simp only [QQ]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]

/-- `t ^ k * QQ ^ e` is continuous, hence interval integrable: needed wherever an integral of
this shape is split or compared. -/
lemma continuous_pow_mul_QQ (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by
  have hQ : Continuous fun t : ℝ => QQ c A t := by simp only [QQ]; fun_prop
  have hk : Continuous fun t : ℝ => t ^ k := by fun_prop
  exact hk.mul ((continuous_rpow_const he).comp hQ)

end Sendov
