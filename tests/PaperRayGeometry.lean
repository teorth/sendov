import Sendov.Analytic.PaperRayGeometry

/-! Tests consume only raw polar and domain hypotheses.  Every finite-ray seam
is checked at the base degree, and the continuous interval coverage is explicit.
The lambda=1/5 test concerns geometry only: the first budget is [2/5,1]. -/
namespace Sendov.PaperRayGeometry.Tests

open PaperPolar

variable {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
include hx0 hx1

-- The original paper's lower endpoint still has the requested geometry.
theorem geometry_at_one_fifth (hraw : RawPolar 256 (1279 / 1280) x) : 5 / 6 < x := by
  exact geometry_one (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda])

-- The altered lower seam is closed, in agreement with the near-D overlap.
theorem budget_at_two_fifths (hraw : RawPolar 256 (639 / 640) x) :
    1 + 18 / (256 : ℝ) < (256 : ℝ) * x ^ 2 * B 256 (639 / 640) := by
  exact budget_lower_one (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda]) (by norm_num [lambda])

-- Both adjacent budget interfaces include lambda=1.
theorem budget_at_one (hraw : RawPolar 256 (255 / 256) x) :
    (1 + 18 / (256 : ℝ) < (256 : ℝ) * x ^ 2 * B 256 (255 / 256)) ∧
    (1 + 33 / (256 : ℝ) < (256 : ℝ) * x ^ 2 * B 256 (255 / 256)) := by
  constructor
  · exact budget_lower_one (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])
  · exact budget_lower_ten (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])

-- The internal rational-product split is also closed at 2.
theorem product_at_two (hraw : RawPolar 256 (127 / 128) x) :
    6 / 5 ≤ (lambda 256 (127 / 128) + 1) * x ^ 2 := by
  exact product_lower_five (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda]) (by norm_num [lambda])

theorem budget_at_five (hraw : RawPolar 256 (251 / 256) x) :
    1 + 33 / (256 : ℝ) < (256 : ℝ) * x ^ 2 * B 256 (251 / 256) := by
  exact budget_lower_five (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda]) (by norm_num [lambda])

theorem budgets_at_ten (hraw : RawPolar 256 (123 / 128) x) :
    (1 + 33 / (256 : ℝ) < (256 : ℝ) * x ^ 2 * B 256 (123 / 128)) ∧
    (1 + 51 / (256 : ℝ) + 1 / 4 < (256 : ℝ) * x ^ 2 * B 256 (123 / 128)) := by
  constructor
  · exact budget_lower_ten (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])
  · exact budget_lower_twentyfive (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])

theorem budgets_at_twentyfive (hraw : RawPolar 256 (231 / 256) x) :
    (1 + 51 / (256 : ℝ) + 1 / 4 < (256 : ℝ) * x ^ 2 * B 256 (231 / 256)) ∧
    (1 + 62 / (256 : ℝ) + 2 < (256 : ℝ) * x ^ 2 * B 256 (231 / 256)) := by
  constructor
  · exact budget_lower_twentyfive (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])
  · exact budget_lower_fortynine (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])

theorem endpoint_at_fortynine (hraw : RawPolar 256 (207 / 256) x) :
    b (207 / 256) x < 23 / 25 ∧
      beta (207 / 256) x (x / (2 * (207 / 256))) < 23 / 25 := by
  exact laplace_endpoints_fortynine (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda])

theorem budget_at_fortynine (hraw : RawPolar 256 (207 / 256) x) :
    1 + 62 / (256 : ℝ) + 2 < (256 : ℝ) * x ^ 2 * B 256 (207 / 256) := by
  exact budget_lower_fortynine (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
    (by norm_num [lambda]) (by norm_num [lambda])

-- Odd degree uses a genuinely nonintegral raw exponent; no parity assumption.
theorem odd_degree (hraw : RawPolar 257 (208 / 257) x) :
    b (208 / 257) x < 23 / 25 ∧
    1 + 62 / (257 : ℝ) + 2 < (257 : ℝ) * x ^ 2 * B 257 (208 / 257) := by
  constructor
  · exact (geometry_fortynine (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda])).1
  · exact budget_lower_fortynine (by norm_num) (by norm_num) (by norm_num) hx0 hx1 hraw
      (by norm_num [lambda]) (by norm_num [lambda])

-- This is a continuous four-region cover, not a finite check of sample lambdas.
theorem exhaustive {m : ℕ} {a : ℝ} (hm : 256 ≤ m) (ha0 : 0 < a) (ha1 : a < 1)
    (hraw : RawPolar m a x) (hl0 : 2 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 49) :
    (lambda m a ≤ 1 ∧ 5 / 6 < x ∧
      1 + 18 / (m : ℝ) < (m : ℝ) * x ^ 2 * B m a) ∨
    (1 ≤ lambda m a ∧ lambda m a ≤ 10 ∧ b a x < 4 / 5 ∧ 7 / 12 < x ∧
      1 + 33 / (m : ℝ) < (m : ℝ) * x ^ 2 * B m a) ∨
    (10 ≤ lambda m a ∧ lambda m a ≤ 25 ∧ b a x < 9 / 10 ∧
      1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) * x ^ 2 * B m a) ∨
    (25 ≤ lambda m a ∧ b a x < 23 / 25 ∧
      1 + 62 / (m : ℝ) + 2 < (m : ℝ) * x ^ 2 * B m a) := by
  by_cases h1 : lambda m a ≤ 1
  · exact Or.inl ⟨h1, geometry_one hm ha0 ha1 hx0 hx1 hraw h1,
      budget_lower_one hm ha0 ha1 hx0 hx1 hraw hl0 h1⟩
  right
  by_cases h10 : lambda m a ≤ 10
  · obtain ⟨hb, hx⟩ := geometry_ten hm ha0 ha1 hx0 hx1 hraw h10
    exact Or.inl ⟨by linarith, h10, hb, hx,
      budget_lower_ten hm ha0 ha1 hx0 hx1 hraw (by linarith) h10⟩
  right
  by_cases h25 : lambda m a ≤ 25
  · exact Or.inl ⟨by linarith, h25, (geometry_twentyfive hm ha0 ha1 hx0 hx1 hraw h25).1,
      budget_lower_twentyfive hm ha0 ha1 hx0 hx1 hraw (by linarith) h25⟩
  exact Or.inr ⟨by linarith, (geometry_fortynine hm ha0 ha1 hx0 hx1 hraw hl1).1,
    budget_lower_fortynine hm ha0 ha1 hx0 hx1 hraw (by linarith) hl1⟩

#print axioms Sendov.PaperRayGeometry.geometry_one
#print axioms Sendov.PaperRayGeometry.geometry_ten
#print axioms Sendov.PaperRayGeometry.geometry_twentyfive
#print axioms Sendov.PaperRayGeometry.integral_exp_lt_one_of_fixed
#print axioms Sendov.PaperRayGeometry.exp_fixed_49
#print axioms Sendov.PaperRayGeometry.geometry_fortynine
#print axioms Sendov.PaperRayGeometry.budget_lower_one
#print axioms Sendov.PaperRayGeometry.budget_lower_ten
#print axioms Sendov.PaperRayGeometry.budget_lower_twentyfive
#print axioms Sendov.PaperRayGeometry.budget_lower_fortynine
#print axioms Sendov.PaperRayGeometry.laplace_endpoints_fortynine
#print axioms Sendov.PaperRayGeometry.Tests.exhaustive

end Sendov.PaperRayGeometry.Tests
