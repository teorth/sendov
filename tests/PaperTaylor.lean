import Sendov.Analytic.PaperTaylor

open MeasureTheory Sendov.PaperTaylor

-- Check the exact requested inequality with a natural degree and expanded quadratic.
example (m : ℕ) (a x : ℝ) (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hx : x ≤ 1) (hc : 0 < 1 - (1 - 2 * a * x + a ^ 2)) :
    let b := 1 - 2 * a * x + a ^ 2
    let c := 1 - b
    let d := 2 * a * (1 - x)
    b ^ ((m : ℝ) / 2) + (m : ℝ) * a ^ 2 *
      (∫ t in (0 : ℝ)..1, t * (1 - 2 * a * x * t + a ^ 2 * t ^ 2) ^ (((m : ℝ) - 1) / 2)) ≤
      1 / ((m : ℝ) + 1) + b ^ ((m : ℝ) / 2) + d / (a * ((m : ℝ) - 2)) +
        12 * (m : ℝ) * a ^ 2 * d ^ 2 / (c ^ 4 * ((m : ℝ) + 1) * ((m : ℝ) + 3)) := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  simpa [beta] using finite_taylor_budget hm' ha ha1 hx (by simpa [beta] using hc)

#print axioms Sendov.PaperTaylor.rpow_taylor_le
#print axioms Sendov.PaperTaylor.integral_beta_taylor
#print axioms Sendov.PaperTaylor.budget_le
#print axioms Sendov.PaperTaylor.finite_taylor_budget
