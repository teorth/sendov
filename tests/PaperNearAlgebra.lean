import Sendov.Analytic.PaperNearAlgebra

open Sendov.PaperNear

-- Generic API checks, including the paper's strictly positive input domain.
example (τ ℓ : ℝ) (hτ : 0 < τ) (hτ7 : τ ≤ 1 / 7)
    (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2 / 5) :
    (1 / 1000 : ℝ) < 1 / (1 + τ) - (f τ ℓ + g τ ℓ) - 1 / 80 :=
  rational_remainder_gt τ ℓ hτ.le hτ7 hℓ.le hℓ2

example (τ : ℝ) (hτ : 0 < τ) (hτ7 : τ ≤ 1 / 7) :
    StrictMonoOn (fun ℓ => f τ ℓ + g τ ℓ) (Set.Icc 0 (2 / 5)) :=
  fg_strictMonoOn τ hτ.le hτ7

example : (1 / 1000 : ℝ) < G (1 / 7) :=
  G_gt_one_thousandth (1 / 7) (by norm_num) le_rfl

example : (1 / 1000 : ℝ) < G 0 :=
  G_gt_one_thousandth 0 le_rfl (by norm_num)

#print axioms Sendov.PaperNear.quartic_bernstein
#print axioms Sendov.PaperNear.quartic_lower
#print axioms Sendov.PaperNear.denominator_bounds
#print axioms Sendov.PaperNear.denominator_mul_G
#print axioms Sendov.PaperNear.G_lower
#print axioms Sendov.PaperNear.G_gt_one_thousandth
#print axioms Sendov.PaperNear.P_lower
#print axioms Sendov.PaperNear.Q_bounds
#print axioms Sendov.PaperNear.f_difference_lower
#print axioms Sendov.PaperNear.g_difference_lower
#print axioms Sendov.PaperNear.fg_difference_lower
#print axioms Sendov.PaperNear.fg_strictMonoOn
#print axioms Sendov.PaperNear.fg_le_endpoint
#print axioms Sendov.PaperNear.quartic_pos
#print axioms Sendov.PaperNear.G_eq_endpoint
#print axioms Sendov.PaperNear.rational_remainder_gt
