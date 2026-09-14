import Sendov.Analytic.PaperTwoEnd

/-! Regression tests for the actual two-endpoint integral estimates. -/
namespace Sendov.PaperTwoEnd.Tests

open MeasureTheory

-- The interface is valid for real m, not only odd integers.
theorem real_degree_left :
    (15 / 2 : ℝ) * (∫ u in (0 : ℝ)..min (1 / 2) (3 / 4),
      u * Q (3 / 4) u ^ (((15 / 2 : ℝ) - 1) / 2)) <
      4 / ((15 / 2 : ℝ) * (3 / 4) ^ 2) := by
  exact left_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Equality at the vertex belongs to the left/separated branch.
theorem vertex_boundary :
    PaperTaylor.budget 7 (1 / 2) (1 / 2) < 4 / ((7 : ℝ) * (1 / 2) ^ 2) +
      6 * PaperTaylor.beta (1 / 2) (1 / 2) 1 ^ ((7 : ℝ) / 2) := by
  apply budget_lt_separated (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  · norm_num [PaperTaylor.chord]
  · exact Or.inl le_rfl

-- Equality at 3*x/2 belongs to the separated branch; no gap at the seam.
theorem separated_boundary :
    PaperTaylor.budget 256 (3 / 4) (1 / 2) < 4 / ((256 : ℝ) * (1 / 2) ^ 2) +
      6 * PaperTaylor.beta (3 / 4) (1 / 2) 1 ^ ((256 : ℝ) / 2) := by
  apply budget_lt_separated (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  · norm_num [PaperTaylor.chord]
  · right; norm_num

-- m=7 retains the original exponent rather than silently replacing it by -m*x²/3.
theorem middle_seven :
    PaperTaylor.budget 7 (5 / 8) (1 / 2) < 4 / ((7 : ℝ) * (1 / 2) ^ 2) +
      (1 + 5 * (7 : ℝ) * (1 / 2) ^ 2 / 8) *
        Real.exp (-3 * ((7 : ℝ) - 1) * (1 / 2) ^ 2 / 8) := by
  exact budget_lt_middle (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- m=8 exercises a nonintegral real exponent.
theorem middle_eight :
    PaperTaylor.budget 8 (5 / 8) (1 / 2) < 4 / ((8 : ℝ) * (1 / 2) ^ 2) +
      (1 + 5 * (8 : ℝ) * (1 / 2) ^ 2 / 8) *
        Real.exp (-3 * ((8 : ℝ) - 1) * (1 / 2) ^ 2 / 8) := by
  exact budget_lt_middle (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Closed x-boundary and the vanishing quadratic minimum cause no singular derivative.
theorem closed_x_boundary :
    total 7 (1 / 2) 1 < 4 / ((7 : ℝ) * 1 ^ 2) + endpoint 7 (1 / 2) 1 := by
  exact total_lt_left_endpoint (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem zero_minimum_primitive :
    (∫ u in (1 : ℝ)..(3 / 2), (u - 1) * Q 1 u ^ (7 / 2 : ℝ)) =
      (Q 1 (3 / 2) ^ ((7 / 2 : ℝ) + 1) - Q 1 1 ^ ((7 / 2 : ℝ) + 1)) /
        (2 * ((7 / 2 : ℝ) + 1)) := by
  exact integral_right_weight (by norm_num)

-- The change of variables includes both powers of a, not just the Jacobian.
theorem affine_link (m : ℝ) : total m (2 / 3) (3 / 4) =
    PaperTaylor.budget m (2 / 3) (3 / 4) := total_eq_budget (by norm_num)

-- Geometry-only coverage is exhaustive, with no assumed integral estimates.
theorem exhaustive (m a x : ℝ) (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) (hc : 0 < PaperTaylor.chord a x) :
    (PaperTaylor.budget m a x < 4 / (m * x ^ 2) +
      6 * PaperTaylor.beta a x 1 ^ (m / 2)) ∨
    (PaperTaylor.budget m a x < 4 / (m * x ^ 2) +
      (1 + 5 * m * x ^ 2 / 8) * Real.exp (-3 * (m - 1) * x ^ 2 / 8)) := by
  by_cases hleft : a ≤ x
  · exact Or.inl (budget_lt_separated hm ha ha1 hx hx1 hc (Or.inl hleft))
  by_cases hright : 3 * x / 2 ≤ a
  · exact Or.inl (budget_lt_separated hm ha ha1 hx hx1 hc (Or.inr hright))
  exact Or.inr (budget_lt_middle hm ha ha1 hx hx1 (lt_of_not_ge hleft) (lt_of_not_ge hright))

#print axioms Sendov.PaperTwoEnd.total_eq_budget
#print axioms Sendov.PaperTwoEnd.left_le
#print axioms Sendov.PaperTwoEnd.left_lt
#print axioms Sendov.PaperTwoEnd.integral_right_weight
#print axioms Sendov.PaperTwoEnd.integral_affine_power
#print axioms Sendov.PaperTwoEnd.integral_right_unweighted
#print axioms Sendov.PaperTwoEnd.right_le_five_endpoint
#print axioms Sendov.PaperTwoEnd.budget_lt_separated
#print axioms Sendov.PaperTwoEnd.budget_lt_middle
#print axioms Sendov.PaperTwoEnd.Tests.exhaustive

end Sendov.PaperTwoEnd.Tests
