import Sendov.Analytic.PaperNear

open MeasureTheory

namespace Sendov.PaperNearAcceptance

/-- Acceptance at the public API, with no endpoint or error assumptions. -/
theorem exact_signature (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 2 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 1000 :=
  PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw hnear

/-- Both integrals expanded: this is the actual D conclusion, not a scalar wrapper. -/
theorem expanded_integrals (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hnear : (m : ℝ) * (1 - a) ≤ 2 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) -
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        ∫ t in (0 : ℝ)..1,
          t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) >
      (1 - a) / 1000 := by
  change PaperPolar.RawPolar m a x at hraw
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw hnear

#print axioms PaperNearClosure.half_power_le
#print axioms PaperNearClosure.geometric_endpoint
#print axioms PaperNearClosure.endpoint_term_lt
#print axioms PaperNearClosure.first_error_le
#print axioms PaperNearClosure.second_error_le
#print axioms PaperNearClosure.parameter_errors
#print axioms PaperNearClosure.near_endpoint_D
#print axioms exact_signature
#print axioms expanded_integrals

end Sendov.PaperNearAcceptance
