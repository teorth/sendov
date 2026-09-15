import Sendov.Analytic.FirstOriginMargins
import Sendov.Analytic.Polar
import Sendov.Counterexample.Identities

/-! Literal interfaces for first-origin report FO02--FO04. All integrals below
are the actual complex product/residual integrals, not abstract error budgets. -/

namespace Sendov.PaperOriginCorollaries
open MeasureTheory Polynomial

/-- The signed complex residual appearing with a plus sign in FO02. -/
noncomputable def residual (a : ℝ) (q : Multiset ℂ) : ℂ :=
  (a : ℂ) ^ 2 * ∫ t in (0 : ℝ)..1,
    (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
      (fun v => 1 - (a : ℂ) * (t : ℂ) * v)

/-- FO02: the exact derivative decomposition. -/
theorem derivative_decomposition (a t : ℝ) (q : Multiset ℂ) :
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * q.sum * Fprod a q t - (a : ℂ) ^ 2 * (t : ℂ) *
        sumEraseProdC q (fun v => v ^ 2) (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  apply (hasDerivAt_Fprod a t q).congr_deriv
  rw [sumEraseProdC_id_eq]
  ring

private theorem residual_eq (a : ℝ) (q : Multiset ℂ) (c : ℂ)
    (hc : c = (a : ℂ) * q.sum) :
    residual a q = -(∫ t in (0 : ℝ)..1,
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
        + c * Fprod a q t)) := by
  have he : ∀ t : ℝ,
      -(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
        + c * Fprod a q t =
      -((a : ℂ) ^ 2 * ((t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
        (fun v => 1 - (a : ℂ) * (t : ℂ) * v))) := by
    intro t
    rw [sumEraseProdC_id_eq, hc]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, neg_neg]
  rfl

/-- FO02: FTC with the actual complex residual and its correct sign. -/
theorem integrated_residual_sum (a : ℝ) (q : Multiset ℂ) :
    (1 : ℂ) = Fprod a q 1 + (a : ℂ) * q.sum *
      (∫ t in (0 : ℝ)..1, Fprod a q t) + residual a q := by
  let D : ℝ → ℂ := fun t => -(a : ℂ) *
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
  have hDint : IntervalIntegrable D volume 0 1 :=
    (continuous_const.mul (continuous_sumEraseProdC a id q)).intervalIntegrable _ _
  have hFint := (continuous_Fprod a q).intervalIntegrable (μ := volume) 0 1
  have hFTC : ∫ t in (0 : ℝ)..1, D t = Fprod a q 1 - Fprod a q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_Fprod a t q) hDint
  rw [residual_eq a q ((a : ℂ) * q.sum) rfl]
  change (1 : ℂ) = Fprod a q 1 + (a : ℂ) * q.sum *
    (∫ t in (0 : ℝ)..1, Fprod a q t) +
    -(∫ t in (0 : ℝ)..1, (D t + (a : ℂ) * q.sum * Fprod a q t))
  rw [intervalIntegral.integral_add hDint (hFint.const_mul _),
    hFTC, Fprod_zero, intervalIntegral.integral_const_mul]
  ring

/-- FO02 in the paper's `m, μ, I` notation (`q.sum = m μ`). -/
theorem integrated_residual {m : ℕ} {μ : ℂ} (a : ℝ) (q : Multiset ℂ)
    (hsum : q.sum = (m : ℂ) * μ) :
    (1 : ℂ) = Fprod a q 1 + (m : ℂ) * (a : ℂ) * μ *
      (∫ t in (0 : ℝ)..1, Fprod a q t) + residual a q := by
  have h := integrated_residual_sum a q
  rw [hsum] at h
  convert h using 1; ring

/-- FO03: the norm of the actual residual, not merely a surrogate inequality. -/
theorem residual_norm_bound {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (ha0 : 0 ≤ a)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖residual a q‖ ≤ a ^ 2 * ((n : ℝ) - 1) *
      ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hqcard
    omega
  set c : ℂ := ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) with hc
  set D : ℝ → ℂ := fun t => -(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
    with hDdef
  have hDcont : Continuous D := by
    rw [hDdef]
    exact continuous_const.mul (continuous_sumEraseProdC a id q)
  have hFcont : Continuous (Fprod a q) := continuous_Fprod a q
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 1 := hDcont.intervalIntegrable _ _
  have hFint : IntervalIntegrable (Fprod a q) MeasureTheory.volume 0 1 :=
    hFcont.intervalIntegrable _ _
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hRcont : Continuous fun t : ℝ =>
      a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
    continuous_const.mul (continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hexp)
  have hGnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t + c * Fprod a q t‖
      ≤ a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    intro t ht
    have h := norm_deriv_add_le hn hqcard hq0 hq1 ha0 ht.1 hx hsum (t := t) (y := y)
    rw [hDdef, hc]
    calc ‖-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
            + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
        ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := h
      _ = a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by ring
  have hint : ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖
      ≤ a ^ 2 * ((n : ℝ) - 1)
          * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    have hni : IntervalIntegrable (fun t : ℝ => ‖D t + c * Fprod a q t‖)
        MeasureTheory.volume 0 1 :=
      (hDcont.add (continuous_const.mul hFcont)).norm.intervalIntegrable _ _
    have hri : IntervalIntegrable (fun t : ℝ =>
        a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)))
        MeasureTheory.volume 0 1 := hRcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hni hri hGnorm
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    simp
  have hc' : c = (a : ℂ) * q.sum := by rw [hc, hsum]; ring
  rw [residual_eq a q c hc', norm_neg]
  exact hint

/-- FO03 endpoint norm majorant. -/
theorem endpoint_norm_bound {n : ℕ} (hn : 2 ≤ n) {a x : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hβ : 0 ≤ QQ (a * x) (a ^ 2) 1) :
    ‖Fprod a q 1‖ ≤ QQ (a * x) (a ^ 2) 1 ^ (((n : ℝ) - 1) / 2) :=
  FirstOriginSmall.norm_Fprod_le hn hqcard hq1 hx hβ

/-- FO03 retains the actual J=(m+1)I. No first-origin upper bound is assumed. -/
theorem norm_budget {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ FirstOriginMargins.T (m : ℝ) a x + (m : ℝ) * a / ((m : ℝ) + 1) *
      ‖((m : ℂ) + 1) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  have hβ : 0 ≤ QQ (a * x) (a ^ 2) 1 := by
    unfold QQ
    nlinarith [sq_nonneg (1 - a), mul_nonneg ha (sub_nonneg.mpr hx1)]
  have h := FirstOriginMargins.lower_budget_norm (n := m + 1) (by omega) ha
    (by simpa using hqcard) hq1 (by simpa using hx) (by simpa using hsum) hβ
  simpa [Nat.cast_add, Nat.cast_one, mul_comm a] using h

/-- FO03 first-origin consumer, with the hypothesis on the actual J integral. -/
theorem first_origin_budget {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hfirst : ‖((m : ℂ) + 1) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ ≤ 1) :
    1 ≤ FirstOriginMargins.T (m : ℝ) a x + (m : ℝ) * a / ((m : ℝ) + 1) := by
  have h := norm_budget hm ha hx1 hqcard hq1 hx hsum
  have hcoef : 0 ≤ (m : ℝ) * a / ((m : ℝ) + 1) := by positivity
  have hb := mul_le_mul_of_nonneg_left hfirst hcoef
  linarith

/-- FO02 with the actual mean `q.sum / m`, rather than a supplied mean. -/
theorem integrated_residual_mean {m : ℕ} (hm : 1 ≤ m) (a : ℝ) (q : Multiset ℂ)
    (hqcard : q.card = m) :
    (1 : ℂ) = Fprod a q 1 + (m : ℂ) * (a : ℂ) * (q.sum / (m : ℂ)) *
      (∫ t in (0 : ℝ)..1, Fprod a q t) + residual a q := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  apply integrated_residual
  field_simp

/-- FO03 in literal m-notation: residual and endpoint bounds together. -/
theorem norm_majorants {m : ℕ} (hm : 1 ≤ m) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a) (hx1 : x ≤ 1)
    (hqcard : q.card = m) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = (m : ℝ) * x)
    (hsum : q.sum = (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    (‖residual a q‖ ≤ (m : ℝ) * a ^ 2 *
      ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((m : ℝ) - 1) / 2)) ∧
    (‖Fprod a q 1‖ ≤ QQ (a * x) (a ^ 2) 1 ^ ((m : ℝ) / 2)) := by
  have hβ : 0 ≤ QQ (a * x) (a ^ 2) 1 := by
    unfold QQ
    nlinarith [sq_nonneg (1 - a), mul_nonneg ha (sub_nonneg.mpr hx1)]
  constructor
  · have h := residual_norm_bound (n := m + 1) (by omega)
      (by simpa using hqcard) hq1 ha (by simpa using hx) (by simpa using hsum)
    have he : (m : ℝ) + 1 - 2 = (m : ℝ) - 1 := by ring
    simpa [Nat.cast_add, Nat.cast_one, he, mul_comm (a ^ 2)] using h
  · simpa using endpoint_norm_bound (n := m + 1) (by omega)
      (by simpa using hqcard) hq1 (by simpa using hx) hβ

/-- FO04: the entire hierarchy from the actual polar and denominator identities.
In particular `1 ≤ ‖K‖` is proved, never required as a premise. -/
theorem polar_hierarchy {n : ℕ} (hn : 2 ≤ n) {a x : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    (1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖) ∧
    (‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ ≤
      ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ∧
    ((∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ≤
      ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- the Möbius estimate, multiplied over the multiset
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  -- take norms in the two identities
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  -- so the integral has norm at least one
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    exact (mul_le_mul_iff_right₀ hnpos).mp (by simpa only [mul_one] using hstep)
  refine ⟨h3, ?_, ?_⟩
  · refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
    exact intervalIntegral.integral_congr (fun t _ => norm_prod_map q _)
  · have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_prod_norm a q).intervalIntegrable _ _)
      (((continuous_rpow_const he).comp (continuous_Ppolar a x)).intervalIntegrable _ _)
    intro t _
    exact prod_norm_le_Ppolar hn hqcard hq1 hx

/-- FO04 from polynomial root/derivative factorizations: both exact identities
and all three inequalities. No polar inequality is an input. -/
theorem polar_factorization_hierarchy {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    (ha : |a| ≤ 1) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    {c : ℂ} {p : ℂ[X]} {z q : Multiset ℂ}
    (hc0 : c ≠ 0) (hzcard : z.card = n - 1)
    (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hpz : p = C c * ((X - C (a : ℂ)) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p = C ((n : ℂ) * c) *
      ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod) :
    (q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) ∧
    (q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod =
      (n : ℂ) * ∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod) ∧
    (1 ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖) ∧
    (‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ ≤
      ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ∧
    ((∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) ≤
      ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) := by
  have ha0C : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  have ha2C : (a : ℂ) ^ 2 ≠ 1 := by exact_mod_cast ha2
  have hpa : p.eval (a : ℂ) = 0 := by simp [hpz]
  have hdenom := prod_sub_mul_prod hc0 hq0 hpz hpq
  have hpolar := polar_identity hc0 ha0C ha2C hzcard hqcard hq0 hpa hpz hpq
  exact ⟨hdenom, hpolar, polar_hierarchy hn ha hz hqcard hq1 hx hpolar hdenom⟩

end Sendov.PaperOriginCorollaries
