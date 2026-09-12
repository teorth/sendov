/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Sendov.Common.Basic
import Sendov.FiniteRange.Moments

/-!
# The finite-range claim in degree six

The first even degree, and the prototype for the general even-degree argument: the exponent
`(n - 4) / 2` is the natural number `1`, so `Sendov.R 6 α` is an explicit rational function
of `α` and the claim reduces to positivity of a quartic.

Concretely, with `M 6 = 5`, `A 6 α = 1 - 2α/5` and `c 6 α = (30 - α - 2α²)/(10(3+α))`:

* `∫ t in 0..1, t³ Q(t) dt = 1/4 - 2c/5 + A/6` (`Sendov.integral_six`);
* `1 - R 6 α = P α / (375 (3+α)²)` with
  `P α = -24α⁴ - 342α³ + 2345α² - 900α + 1575` (`Sendov.one_sub_R_six`);
* feasibility enters only through `Sendov.alpha_le_half_M`, which gives `α ≤ 5/2`.

`P` is positive up to `α = 4.856`, so there is ample room.  The exact feasible range is
`α ≤ 2.194`, cut out by the quartic `-4α⁴ - 44α³ - 21α² + 300α ≥ 0`, but that finer
information is not needed.  Note also that the hypothesis `α ≤ 17` of
`Sendov.finite_range` is unused in this degree, since feasibility already bounds `α`.
-/

namespace Sendov

open MeasureTheory

variable {α : ℝ}

lemma M_six : M 6 = 5 := by norm_num [M]

lemma A_six (α : ℝ) : A 6 α = 1 - 2 * α / 5 := by norm_num [A, M]

lemma c_six (α : ℝ) : c 6 α = 1 - α / 5 - α / (2 * (3 + α)) := by norm_num [c, M]

lemma c_six' (hα : 0 ≤ α) : c 6 α = (30 - α - 2 * α ^ 2) / (10 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_six]
  field_simp
  ring

/-- In degree six the exponent `(n - 4) / 2` is `1`, so the integral is elementary. -/
lemma integral_six (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = 1 / 4 - 2 * c 6 α / 5 + A 6 α / 6 := by
  have hfun : (fun t : ℝ => t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = fun t : ℝ => 1 * t ^ 3 + (-2 * c 6 α) * t ^ 4 + A 6 α * t ^ 5 + 0 * t ^ 6
          + 0 * t ^ 7 := by
    funext t
    rw [show ((((6 : ℕ) : ℝ) - 4) / 2) = 1 by norm_num, Real.rpow_one, Q]
    ring
  rw [hfun, integral_poly7]
  ring

/-- The cleared form of `1 - R 6 α`: the numerator is the quartic `P` and the denominator is
manifestly positive. -/
lemma one_sub_R_six (hα : 0 ≤ α) :
    1 - R 6 α
      = (-24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575) / (375 * (3 + α) ^ 2) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [R, integral_six, A_six, c_six, M_six]
  push_cast
  field_simp
  ring

/-- **The finite-range claim in degree six.**  Note that no upper bound on `α` is assumed:
the feasibility constraint supplies one. -/
theorem finite_range_six (hα : 0 ≤ α) (hfeas : c 6 α ^ 2 ≤ A 6 α) : R 6 α < 1 := by
  have hle : α ≤ 3 := by
    have h := alpha_le_half_M (n := 6) (by norm_num) hfeas
    rw [M_six] at h
    linarith
  have hP : 0 < -24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575 := by
    nlinarith only [hα, mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 2) (sub_nonneg.2 hle), sq_nonneg (1103 * α - 450)]
  apply sub_pos.mp
  rw [one_sub_R_six hα]
  exact div_pos hP (by positivity)

end Sendov
