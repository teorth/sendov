import Sendov.Analytic.PaperNearMargins

open MeasureTheory

namespace Sendov.PaperNearMarginsAcceptance

/-- Literal raw-polar signature and historical strict margin. -/
theorem exact_one_fiftieth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 50) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 3 := by
  -- The larger-domain, weaker-margin theorem cannot discharge this goal.
  fail_if_success
    exact PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw (by linarith)
  exact PaperNearMargins.near_endpoint_one_fiftieth hm ha0 ha1 hx0 hx1 hraw hnear

/-- Expand both raw polar and T: no abstract scalar surrogate is accepted. -/
theorem expanded_one_fiftieth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hnear : (m : ℝ) * (1 - a) ≤ 1 / 50) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) -
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        ∫ t in (0 : ℝ)..1,
          t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) >
      (1 - a) / 3 := by
  change PaperPolar.RawPolar m a x at hraw
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperNearMargins.near_endpoint_one_fiftieth hm ha0 ha1 hx0 hx1 hraw hnear

#print axioms PaperNearMargins.near_endpoint_one_fiftieth
#print axioms exact_one_fiftieth
#print axioms expanded_one_fiftieth

/-- Literal raw-polar signature and historical strict margin. -/
theorem exact_one_tenth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 10) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 5 := by
  -- The larger-domain, weaker-margin theorem cannot discharge this goal.
  fail_if_success
    exact PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw (by linarith)
  exact PaperNearMargins.near_endpoint_one_tenth hm ha0 ha1 hx0 hx1 hraw hnear

/-- Expand both raw polar and T: no abstract scalar surrogate is accepted. -/
theorem expanded_one_tenth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hnear : (m : ℝ) * (1 - a) ≤ 1 / 10) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) -
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        ∫ t in (0 : ℝ)..1,
          t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) >
      (1 - a) / 5 := by
  change PaperPolar.RawPolar m a x at hraw
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperNearMargins.near_endpoint_one_tenth hm ha0 ha1 hx0 hx1 hraw hnear

#print axioms PaperNearMargins.near_endpoint_one_tenth
#print axioms exact_one_tenth
#print axioms expanded_one_tenth

/-- Literal raw-polar signature and historical strict margin. -/
theorem exact_one_fifth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 80 := by
  -- The larger-domain, weaker-margin theorem cannot discharge this goal.
  fail_if_success
    exact PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw (by linarith)
  exact PaperNearMargins.near_endpoint_one_fifth hm ha0 ha1 hx0 hx1 hraw hnear

/-- Expand both raw polar and T: no abstract scalar surrogate is accepted. -/
theorem expanded_one_fifth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hnear : (m : ℝ) * (1 - a) ≤ 1 / 5) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) -
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        ∫ t in (0 : ℝ)..1,
          t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) >
      (1 - a) / 80 := by
  change PaperPolar.RawPolar m a x at hraw
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperNearMargins.near_endpoint_one_fifth hm ha0 ha1 hx0 hx1 hraw hnear

#print axioms PaperNearMargins.near_endpoint_one_fifth
#print axioms exact_one_fifth
#print axioms expanded_one_fifth

/-- Literal raw-polar signature and historical strict margin. -/
theorem exact_one_hundredth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : PaperPolar.RawPolar m a x) (hnear : (m : ℝ) * (1 - a) ≤ 1 / 100) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) - PaperTaylor.budget (m : ℝ) a x >
      (1 - a) / 3 := by
  -- The larger-domain, weaker-margin theorem cannot discharge this goal.
  fail_if_success
    exact PaperNearClosure.near_endpoint_D hm ha0 ha1 hx0 hx1 hraw (by linarith)
  exact PaperNearMargins.near_endpoint_one_hundredth hm ha0 ha1 hx0 hx1 hraw hnear

/-- Expand both raw polar and T: no abstract scalar surrogate is accepted. -/
theorem expanded_one_hundredth (m : ℕ) (a x : ℝ) (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2))
    (hnear : (m : ℝ) * (1 - a) ≤ 1 / 100) :
    1 - (m : ℝ) * a / ((m : ℝ) + 1) -
      ((1 - 2 * a * x + a ^ 2) ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
        ∫ t in (0 : ℝ)..1,
          t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) >
      (1 - a) / 3 := by
  change PaperPolar.RawPolar m a x at hraw
  simpa only [PaperTaylor.budget, PaperTaylor.beta, mul_one, one_pow] using
    PaperNearMargins.near_endpoint_one_hundredth hm ha0 ha1 hx0 hx1 hraw hnear

#print axioms PaperNearMargins.near_endpoint_one_hundredth
#print axioms exact_one_hundredth
#print axioms expanded_one_hundredth

#print axioms PaperNearMargins.f_le_cutoff_bound
#print axioms PaperNearMargins.g_le_cutoff_bound
#print axioms PaperNearMargins.rational_remainder_gt
#print axioms PaperNearMargins.margin_of_rational
#print axioms PaperNearMargins.margin_of_cutoff

end Sendov.PaperNearMarginsAcceptance
