import Sendov.Analytic.PaperPolar
import Sendov.Analytic.PaperRayAlgebra
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-ray geometry and the actual budget, from raw polar

All geometric conclusions below consume the raw integral, not assumed endpoint
ceilings.  The rational polar bound suffices through lambda=25.  The ceiling
23/25 uses convexity of the exponential chord and a fixed endpoint at 49.
The first budget interval is deliberately [2/5,1], not the paper's [1/5,1]:
`PaperNearClosure.near_endpoint_D` covers the omitted near-endpoint region.
No upper-tail estimate is asserted in this module.
-/
namespace Sendov.PaperRayGeometry

open MeasureTheory PaperPolar

/-- The true available budget B (not the origin expression T). -/
noncomputable def B (m : ℕ) (a : ℝ) : ℝ := 1 - (m : ℝ) * a / ((m : ℝ) + 1)

lemma scaled_budget_eq (m : ℕ) (a x : ℝ) :
    (m : ℝ) * x ^ 2 * B m a =
      (m : ℝ) / ((m : ℝ) + 1) * ((lambda m a + 1) * x ^ 2) := by
  unfold B lambda
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma a_lower {m : ℕ} {a L : ℝ} (hm : 256 ≤ m) (ha1 : a < 1)
    (hl : lambda m a ≤ L) : 1 - L / 256 ≤ a := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hh := mul_nonneg (sub_nonneg.mpr hm') (show 0 ≤ 1 - a by linarith)
  unfold lambda at hl
  nlinarith

lemma b_le_lambda {m : ℕ} {a x : ℝ} (hm : 7 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) : b a x ≤ lambda m a / (3 + lambda m a) := by
  obtain ⟨h₁, h₂⟩ := endpoint_bounds hm ha0 ha1 hx0 hx1 hraw
  exact h₁.trans h₂

/-- The exact conversion loses only b/(2a), not an unweighted 2h. -/
lemma x_lower_of_b {a x q : ℝ} (ha : 0 < a) (hb : b a x ≤ q) :
    1 - q / (2 * a) ≤ x := by
  have hden : 0 < 2 * a := by positivity
  have hh : q / (2 * a) * (2 * a) = q := div_mul_cancel₀ _ hden.ne'
  unfold b at hb
  nlinarith [sq_nonneg (1 - a)]

lemma x_lower_constant {a x A q : ℝ} (hA : 0 < A) (ha : A ≤ a)
    (hq : 0 ≤ q) (hb : b a x ≤ q) : 1 - q / (2 * A) ≤ x := by
  have ha0 : 0 < a := hA.trans_le ha
  have hx := x_lower_of_b ha0 hb
  have hdiv : q / (2 * a) ≤ q / (2 * A) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  linarith

variable {m : ℕ} {a x : ℝ}

/-- All m>=256, lambda<=10: both endpoint and vertex geometry. -/
theorem geometry_ten (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 10) :
    b a x < 4 / 5 ∧ 7 / 12 < x := by
  have hlpos := lambda_pos (by omega : 0 < m) ha1
  have hb := (b_le_lambda (by omega) ha0 ha1 hx0 hx1 hraw).trans
    (rational_mono hlpos.le hl)
  norm_num at hb
  have ha := a_lower hm ha1 hl
  norm_num at ha
  have hx := x_lower_constant (by norm_num : (0 : ℝ) < 123 / 128) ha
    (by norm_num : (0 : ℝ) ≤ 10 / 13) hb
  constructor <;> norm_num at * <;> linarith

theorem geometry_one (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 1) : 5 / 6 < x := by
  have hlpos := lambda_pos (by omega : 0 < m) ha1
  have hb := (b_le_lambda (by omega) ha0 ha1 hx0 hx1 hraw).trans
    (rational_mono hlpos.le hl)
  norm_num at hb
  have ha := a_lower hm ha1 hl
  norm_num at ha
  have hx := x_lower_constant (by norm_num : (0 : ℝ) < 255 / 256) ha
    (by norm_num : (0 : ℝ) ≤ 1 / 4) hb
  norm_num at hx
  linarith

theorem geometry_twentyfive (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 25) :
    b a x < 9 / 10 ∧ 231 / 512 < x := by
  have hlpos := lambda_pos (by omega : 0 < m) ha1
  have hb := (b_le_lambda (by omega) ha0 ha1 hx0 hx1 hraw).trans
    (rational_mono hlpos.le hl)
  have ha := a_lower hm ha1 hl
  have hx := (geometry (by omega) ha0 ha1 hx0 hx1 hraw).1
  constructor <;> norm_num at * <;> linarith

/-- Convexity in the ray parameter, integrated on the full interval.
The strictly positive alpha rules out the equality at the zero endpoint. -/
lemma integral_exp_lt_one_of_fixed {α L q : ℝ} (hα : 0 < α) (hαL : α ≤ L)
    (hfixed : (∫ t in (0 : ℝ)..1, Real.exp (L * (-1 + (2 - q) * t))) < 1) :
    (∫ t in (0 : ℝ)..1, Real.exp (α * (-1 + (2 - q) * t))) < 1 := by
  have hL : 0 < L := hα.trans_le hαL
  have hw : 0 < α / L := div_pos hα hL
  have hw1 : α / L ≤ 1 := (div_le_one hL).2 hαL
  have hpt (t : ℝ) : Real.exp (α * (-1 + (2 - q) * t)) ≤
      (1 - α / L) + α / L * Real.exp (L * (-1 + (2 - q) * t)) := by
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (L * (-1 + (2 - q) * t)))
      (show 0 ≤ 1 - α / L by linarith) hw.le (by ring : 1 - α / L + α / L = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    rw [← mul_assoc, div_mul_cancel₀ _ hL.ne'] at hc
    exact hc
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (α * (-1 + (2 - q) * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ =>
      (1 - α / L) + α / L * Real.exp (L * (-1 + (2 - q) * t))).intervalIntegrable _ _)
    (fun t _ => hpt t)
  rw [intervalIntegral.integral_add
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 - α / L) volume 0 1)
    ((by fun_prop : Continuous fun t : ℝ =>
      α / L * Real.exp (L * (-1 + (2 - q) * t))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hi
  have hstrict := mul_pos hw (sub_pos.mpr hfixed)
  nlinarith

/-- A reusable fixed-endpoint obstruction to raw polar. -/
lemma b_lt_of_fixed (hm : 0 < m) (ha0 : 0 < a) (ha1 : a < 1)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hraw : RawPolar m a x)
    {L q : ℝ} (hL : lambda m a ≤ L)
    (hfixed : (∫ t in (0 : ℝ)..1, Real.exp (L * (-1 + (2 - q) * t))) < 1) :
    b a x < q := by
  by_contra hn
  have hq : q ≤ b a x := le_of_not_gt hn
  have hα := PaperPolar.alpha_pos hm ha0 ha1
  have hi := one_le_integral_exp hm hx0 hx1 hraw
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (alpha m a * (-1 + (2 - b a x) * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (alpha m a * (-1 + (2 - q) * t))).intervalIntegrable _ _) (fun t ht => by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_nonneg hα.le ht.1) (sub_nonneg.mpr hq)])
  exact (not_lt_of_ge (hi.trans hmono))
    (integral_exp_lt_one_of_fixed hα ((alpha_le_lambda m a).trans hL) hfixed)

lemma exp_fixed_49 : Real.exp (98 / 25 : ℝ) < 1323 / 25 := by
  have he : Real.exp (1 : ℝ) < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hp : Real.exp (98 / 25 : ℝ) ^ 25 < (1323 / 25 : ℝ) ^ 25 := by
    calc
      Real.exp (98 / 25 : ℝ) ^ 25 = Real.exp (1 : ℝ) ^ 98 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        norm_num
      _ ≤ (11 / 4 : ℝ) ^ 98 := pow_le_pow_left₀ (Real.exp_nonneg _) he.le _
      _ < (1323 / 25 : ℝ) ^ 25 := by norm_num
  exact (pow_lt_pow_iff_left₀ (Real.exp_nonneg _) (by norm_num)
    (by norm_num : (25 : ℕ) ≠ 0)).mp hp

lemma fixed_49_integral_lt_one :
    (∫ t in (0 : ℝ)..1, Real.exp (49 * (-1 + (2 - 23 / 25) * t))) < 1 := by
  rw [Sendov.integral_exp_eq' (by norm_num : (0 : ℝ) < 49)
    (by norm_num : (23 / 25 : ℝ) < 2)]
  norm_num
  have he := exp_fixed_49
  have hp := Real.exp_pos (-49 : ℝ)
  linarith

theorem geometry_fortynine (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 49) :
    b a x < 23 / 25 ∧ 207 / 512 < x := by
  refine ⟨b_lt_of_fixed (by omega) ha0 ha1 hx0 hx1 hraw hl fixed_49_integral_lt_one, ?_⟩
  have ha := a_lower hm ha1 hl
  have hx := (geometry (by omega) ha0 ha1 hx0 hx1 hraw).1
  norm_num at ha
  linarith

/-- Scaling a lower bound for (lambda+1)x² gives a lower bound for the true B. -/
lemma scaled_budget_lower {C : ℝ} (hp : C ≤ (lambda m a + 1) * x ^ 2) :
    (m : ℝ) / ((m : ℝ) + 1) * C ≤ (m : ℝ) * x ^ 2 * B m a := by
  rw [scaled_budget_eq]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

lemma scaled_budget_lower_of_x {l s : ℝ} (hl : l ≤ lambda m a) (hl0 : 0 ≤ l + 1)
    (hs : 0 ≤ s) (hx : s ≤ x) :
    (m : ℝ) / ((m : ℝ) + 1) * ((l + 1) * s ^ 2) ≤
      (m : ℝ) * x ^ 2 * B m a := by
  apply scaled_budget_lower
  have hx2 : s ^ 2 ≤ x ^ 2 := by nlinarith
  have h₁ := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hl)
  have h₂ := mul_nonneg hl0 (sub_nonneg.mpr hx2)
  nlinarith

/-- A rational replacement for the sinh-root budget argument, on the altered
region [2/5,1].  Its uniform product lower bound is 11/10. -/
lemma product_lower_one (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 2 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    11 / 10 ≤ (lambda m a + 1) * x ^ 2 := by
  have hlpos : 0 ≤ lambda m a := by linarith
  have hb := b_le_lambda (by omega) ha0 ha1 hx0 hx1 hraw
  have hrat : lambda m a / (3 + lambda m a) ≤ lambda m a / 3 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [sq_nonneg (lambda m a)]
  have ha := a_lower hm ha1 hl1
  norm_num at ha
  have hx := x_lower_constant (by norm_num : (0 : ℝ) < 255 / 256) ha
    (show 0 ≤ lambda m a / 3 by positivity) (hb.trans hrat)
  have hxlin : 1 - 128 / 765 * lambda m a ≤ x := by
    convert hx using 1
    ring
  have hx2 : 1 - 256 / 765 * lambda m a ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have hmul := mul_nonneg (show 0 ≤ lambda m a + 1 by positivity)
    (sub_nonneg.mpr hx2)
  have hquad := mul_nonneg hlpos (sub_nonneg.mpr hl1)
  nlinarith

/-- Actual lower budget on [2/5,1]; this intentionally does not claim [1/5,1]. -/
theorem budget_lower_one (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 2 / 5 ≤ lambda m a) (hl1 : lambda m a ≤ 1) :
    1 + 18 / (m : ℝ) < (m : ℝ) * x ^ 2 * B m a := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hc := PaperRay.compare_from_base (M := 256) (C := 11 / 10) (E := 0)
    (K := 18) (z := 0) (by norm_num) hm' (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [zero_div, sub_zero, add_zero] at hc
  exact hc.trans_le (scaled_budget_lower
    (product_lower_one hm ha0 ha1 hx0 hx1 hraw hl0 hl1))

/-- The rational endpoint bound gives a product >=6/5 on [1,5].
The split at 2 uses constant rational lower bounds for x, not a grid in m. -/
lemma product_lower_five (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 5) :
    6 / 5 ≤ (lambda m a + 1) * x ^ 2 := by
  have hlpos : 0 ≤ lambda m a := by linarith
  have hb := b_le_lambda (by omega) ha0 ha1 hx0 hx1 hraw
  have ha := a_lower hm ha1 hl1
  norm_num at ha
  by_cases hl2 : lambda m a ≤ 2
  · have hb2 := hb.trans (rational_mono hlpos hl2)
    norm_num at hb2
    have hx := x_lower_constant (by norm_num : (0 : ℝ) < 251 / 256) ha
      (by norm_num : (0 : ℝ) ≤ 2 / 5) hb2
    have hxs : 79 / 100 ≤ x := by norm_num at hx; linarith
    have hx2 : (79 / 100 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg x) (show 0 ≤ lambda m a - 1 by linarith)
    nlinarith
  · have hb5 := hb.trans (rational_mono hlpos hl1)
    norm_num at hb5
    have hx := x_lower_constant (by norm_num : (0 : ℝ) < 251 / 256) ha
      (by norm_num : (0 : ℝ) ≤ 5 / 8) hb5
    have hxs : 17 / 25 ≤ x := by norm_num at hx; linarith
    have hx2 : (17 / 25 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hmul := mul_nonneg (sq_nonneg x) (show 0 ≤ lambda m a - 2 by linarith)
    nlinarith

theorem budget_lower_five (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 5) :
    1 + 33 / (m : ℝ) < (m : ℝ) * x ^ 2 * B m a := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hc := PaperRay.compare_from_base (M := 256) (C := 6 / 5) (E := 0)
    (K := 33) (z := 0) (by norm_num) hm' (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [zero_div, sub_zero, add_zero] at hc
  exact hc.trans_le (scaled_budget_lower
    (product_lower_five hm ha0 ha1 hx0 hx1 hraw hl0 hl1))

/-- The whole middle ray, including both seams 1 and 10. -/
theorem budget_lower_ten (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 1 ≤ lambda m a) (hl1 : lambda m a ≤ 10) :
    1 + 33 / (m : ℝ) < (m : ℝ) * x ^ 2 * B m a := by
  by_cases hl5 : lambda m a ≤ 5
  · exact budget_lower_five hm ha0 ha1 hx0 hx1 hraw hl0 hl5
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hx := (geometry_ten hm ha0 ha1 hx0 hx1 hraw hl1).2
  refine (PaperRay.ray_three hm').trans_le ?_
  simpa only [show (5 : ℝ) + 1 = 6 by norm_num] using
    scaled_budget_lower_of_x (by linarith : 5 ≤ lambda m a) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 7 / 12) hx.le

theorem budget_lower_twentyfive (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 10 ≤ lambda m a) (hl1 : lambda m a ≤ 25) :
    1 + 51 / (m : ℝ) + 1 / 4 < (m : ℝ) * x ^ 2 * B m a := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hx := (geometry_twentyfive hm ha0 ha1 hx0 hx1 hraw hl1).2
  refine (PaperRay.ray_four hm').trans_le ?_
  simpa only [show (10 : ℝ) + 1 = 11 by norm_num] using
    scaled_budget_lower_of_x hl0 (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 231 / 512) hx.le

theorem budget_lower_fortynine (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl0 : 25 ≤ lambda m a) (hl1 : lambda m a ≤ 49) :
    1 + 62 / (m : ℝ) + 2 < (m : ℝ) * x ^ 2 * B m a := by
  have hm' : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hx := (geometry_fortynine hm ha0 ha1 hx0 hx1 hraw hl1).2
  refine (PaperRay.ray_five hm').trans_le ?_
  simpa only [show (25 : ℝ) + 1 = 26 by norm_num] using
    scaled_budget_lower_of_x hl0 (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 207 / 512) hx.le

/-- The actual Laplace splitting point is inside the integration interval. -/
theorem halfpoint_mem (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 49) :
    x / (2 * a) ∈ Set.Ioo (0 : ℝ) 1 := by
  have ha := a_lower hm ha1 hl
  have hx := (geometry (by omega) ha0 ha1 hx0 hx1 hraw).1
  constructor
  · exact div_pos (by linarith) (by positivity)
  · apply (div_lt_one (by positivity : 0 < 2 * a)).2
    linarith

lemma beta_halfpoint (ha0 : 0 < a) :
    beta a x (x / (2 * a)) = 1 - 3 * x ^ 2 / 4 := by
  unfold beta
  field_simp
  ring

/-- Both endpoints needed for the Laplace remainder; no integral bound is assumed. -/
theorem laplace_endpoints_ten (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 10) :
    b a x < 4 / 5 ∧ beta a x (x / (2 * a)) < 4 / 5 := by
  obtain ⟨hb, hx⟩ := geometry_ten hm ha0 ha1 hx0 hx1 hraw hl
  refine ⟨hb, ?_⟩
  rw [beta_halfpoint ha0]
  have hx2 : (7 / 12 : ℝ) ^ 2 < x ^ 2 := by nlinarith
  nlinarith

/-- Both endpoints needed for the Laplace remainder; no integral bound is assumed. -/
theorem laplace_endpoints_twentyfive (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 25) :
    b a x < 9 / 10 ∧ beta a x (x / (2 * a)) < 9 / 10 := by
  obtain ⟨hb, hx⟩ := geometry_twentyfive hm ha0 ha1 hx0 hx1 hraw hl
  refine ⟨hb, ?_⟩
  rw [beta_halfpoint ha0]
  have hx2 : (231 / 512 : ℝ) ^ 2 < x ^ 2 := by nlinarith
  nlinarith

/-- Both endpoints needed for the Laplace remainder; no integral bound is assumed. -/
theorem laplace_endpoints_fortynine (hm : 256 ≤ m)
    (ha0 : 0 < a) (ha1 : a < 1) (hx0 : -1 ≤ x) (hx1 : x ≤ 1)
    (hraw : RawPolar m a x) (hl : lambda m a ≤ 49) :
    b a x < 23 / 25 ∧ beta a x (x / (2 * a)) < 23 / 25 := by
  obtain ⟨hb, hx⟩ := geometry_fortynine hm ha0 ha1 hx0 hx1 hraw hl
  refine ⟨hb, ?_⟩
  rw [beta_halfpoint ha0]
  have hx2 : (207 / 512 : ℝ) ^ 2 < x ^ 2 := by nlinarith
  nlinarith

/-- Cancellation interface for any separately proved upper bound on T. -/
lemma lt_B_of_scaled_lt {T : ℝ} (hm : 0 < m) (hx : 0 < x)
    (h : (m : ℝ) * x ^ 2 * T < (m : ℝ) * x ^ 2 * B m a) : T < B m a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact (mul_lt_mul_iff_right₀ (show 0 < (m : ℝ) * x ^ 2 by positivity)).mp h

end Sendov.PaperRayGeometry
