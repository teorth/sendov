import Sendov.Analytic.PaperPolar

/-! Direct-import regression: the hypothesis is the literal raw integral,
not the exponential inequality or the rational endpoint bound. -/
namespace Sendov.PaperPolar.Tests

open MeasureTheory

theorem literal_raw_consequences {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : 1 ≤ ∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) :
    (1 - 2 * a * x + a ^ 2 ≤
      ((m : ℝ) * (1 - a ^ 2) / 2) / (3 + (m : ℝ) * (1 - a ^ 2) / 2)) ∧
    (((m : ℝ) * (1 - a ^ 2) / 2) / (3 + (m : ℝ) * (1 - a ^ 2) / 2) ≤
      ((m : ℝ) * (1 - a)) / (3 + (m : ℝ) * (1 - a))) ∧
    a / 2 < x ∧ 0 < 1 - (1 - 2 * a * x + a ^ 2) := by
  have he := endpoint_bounds hm ha0 ha1 hx0 hx1 hraw
  have hg := geometry hm ha0 ha1 hx0 hx1 hraw
  exact ⟨he.1, he.2, hg.1, hg.2⟩

theorem literal_integral_domination {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    (∫ t in (0 : ℝ)..1,
      (a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2) ^
        ((m : ℝ) / 2)) ≤
    ∫ t in (0 : ℝ)..1,
      Real.exp (((m : ℝ) * (1 - a ^ 2) / 2) *
        (-1 + (2 - (1 - 2 * a * x + a ^ 2)) * t)) := by
  simpa only [raw_kernel_eq, alpha, b] using
    (integral_le_exp (by omega : 0 < m) (a := a) hx0 hx1)

#print axioms Sendov.PaperPolar.rpow_le_exp
#print axioms Sendov.PaperPolar.integral_le_exp
#print axioms Sendov.PaperPolar.one_le_integral_exp
#print axioms Sendov.PaperPolar.b_le_alpha
#print axioms Sendov.PaperPolar.endpoint_bounds
#print axioms Sendov.PaperPolar.geometry
#print axioms Sendov.PaperPolar.c_lower_bound
#print axioms Sendov.PaperPolar.beta_le_chord
#print axioms Sendov.PaperPolar.beta_pos
#print axioms literal_raw_consequences
#print axioms literal_integral_domination

end Sendov.PaperPolar.Tests
