import Sendov.Analytic.PaperLaplace

open MeasureTheory Sendov.PaperTaylor Sendov.PaperLaplace

-- Exact finite-endpoint moments (not an assumed improper-integral evaluation).
example : (∫ t in (0 : ℝ)..1, t * Real.exp (-2 * t)) =
    1 / 4 - 3 / 4 * Real.exp (-2) := by
  have h := integral_mul_exp (s := 2) (by norm_num) 1
  norm_num at h ⊢
  exact h

example : (∫ t in (0 : ℝ)..1, t ^ 3 * Real.exp (-t)) =
    6 - 16 * Real.exp (-1) := by
  have h := integral_cube_mul_exp (s := 1) (by norm_num) 1
  norm_num at h ⊢
  exact h

example {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, t ^ 3 * Real.exp (-s * t)) ≤ 6 / s ^ 4 :=
  integral_cube_mul_exp_le hs hz

-- The actual split identity at x=1, with its strict interval membership.
example : (1 : ℝ) / (2 * (3 / 4)) ∈ Set.Ioo (0 : ℝ) 1 :=
  split_mem (by norm_num) (by norm_num) (by norm_num)

example : beta (3 / 4) 1 (1 / (2 * (3 / 4))) = 1 / 4 := by
  rw [beta_split (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  norm_num

-- Real, nonintegral degree: the analytic theorem does not need degree integrality.
example : (3 / 2 : ℝ) * (1 : ℝ) ^ 2 * budget (3 / 2) (3 / 4) 1 ≤
    (3 / 2 : ℝ) ^ 2 / (3 / 2 - 1) ^ 2 +
    (256 / 27 : ℝ) * (3 / 2) ^ 2 / ((3 / 2 - 1) ^ 3 * (1 : ℝ) ^ 2) +
    ((3 / 2 : ℝ) ^ 2 / 2 + 3 / 2) * (1 / 4 : ℝ) ^ (((3 / 2 : ℝ) - 1) / 2) := by
  apply Sendov.PaperLaplace.budget_le <;> norm_num [beta]

-- The headline conclusion contains precisely the original endpoint plus integral.
example {m a x r : ℝ} (hm : 1 < m) (ha : 0 < a) (ha1 : a < 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hxa : x < 2 * a)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : beta a x 1 ≤ r) (hr1 : r ≤ 1) :
    m * x ^ 2 * (beta a x 1 ^ (m / 2) + m * a ^ 2 *
      ∫ t in (0 : ℝ)..1, t * beta a x t ^ ((m - 1) / 2)) ≤
      m ^ 2 / (m - 1) ^ 2 + (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      (m ^ 2 / 2 + m) * r ^ ((m - 1) / 2) :=
  Sendov.PaperLaplace.budget_le hm ha ha1 hx0 hx1 hxa hr0 hrb hr1

-- Round4 geometry: no assumed integral/exponential comparison and no r ≤ 1 input.
example {m : ℕ} {a x r : ℝ} (hm : 512 ≤ m)
    (ha : 7 / 8 ≤ a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : Sendov.PaperPolar.RawPolar m a x)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : Sendov.PaperPolar.b a x ≤ r) :
    (m : ℝ) * x ^ 2 * budget m a x ≤
      (m : ℝ) ^ 2 / (m - 1) ^ 2 +
      (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      ((m : ℝ) ^ 2 / 2 + m) * r ^ (((m : ℝ) - 1) / 2) :=
  sharp_laplace (by omega) (by linarith) ha1 hx0 hx1 hraw hr0 hrb

-- Round5 geometry uses the same theorem, not a downward extrapolation of m ≥ 512.
example {m : ℕ} {a x r : ℝ} (hm : 256 ≤ m)
    (ha : 4 / 5 ≤ a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : Sendov.PaperPolar.RawPolar m a x)
    (hr0 : 1 - 3 * x ^ 2 / 4 ≤ r) (hrb : Sendov.PaperPolar.b a x ≤ r) :
    (m : ℝ) * x ^ 2 * budget m a x ≤
      (m : ℝ) ^ 2 / (m - 1) ^ 2 +
      (256 / 27 : ℝ) * m ^ 2 / ((m - 1) ^ 3 * x ^ 2) +
      ((m : ℝ) ^ 2 / 2 + m) * r ^ (((m : ℝ) - 1) / 2) :=
  sharp_laplace (by omega) (by linarith) ha1 hx0 hx1 hraw hr0 hrb

#print axioms Sendov.PaperLaplace.exp_le_one_add_mul_exp
#print axioms Sendov.PaperLaplace.rpow_le_exp_taylor
#print axioms Sendov.PaperLaplace.beta_rpow_le_exp
#print axioms Sendov.PaperLaplace.integral_mul_exp
#print axioms Sendov.PaperLaplace.integral_cube_mul_exp
#print axioms Sendov.PaperLaplace.integral_left_le
#print axioms Sendov.PaperLaplace.integral_right_le
#print axioms Sendov.PaperLaplace.budget_le_of_beta_le_one
#print axioms Sendov.PaperLaplace.budget_le
#print axioms Sendov.PaperLaplace.sharp_laplace
