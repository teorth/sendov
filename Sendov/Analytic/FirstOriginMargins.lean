import Sendov.Analytic.FirstOriginSmall

/-!
# Quantitative first-origin margins for m = 5, 6

The hypotheses concern only the pointwise closed disk and the polar integral.
In particular, no first-origin factorization or upper bound on the integral is
assumed. The conclusion is a direct lower bound on its norm, not a contradiction.
The polynomial constants and the actual (not surrogate) T budgets are exposed.
-/
namespace Sendov.FirstOriginMargins

open FirstOriginSmall

noncomputable def A5 (a : ℝ) : ℝ :=
  7 / 6 - (7 / 3) * a + a ^ 2 + (7 / 12) * a ^ 3 + (1 / 12) * a ^ 4

noncomputable def A6 (a : ℝ) : ℝ :=
  15 / 7 - (27 / 7) * a + (15 / 7) * a ^ 2 + (65 / 112) * a ^ 3 -
    (229 / 112) * a ^ 4 + (23 / 14) * a ^ 5

/-- Explicit nonnegative Bernstein remainder after subtracting 1/16. -/
lemma A5_remainder (a : ℝ) :
    A5 a - 1 / 16 = (53 / 48) * (1 - a) ^ 4 + (25 / 12) * a * (1 - a) ^ 3 +
      (5 / 8) * a ^ 2 * (1 - a) ^ 2 + (7 / 16) * a ^ 4 := by
  unfold A5
  ring

/-- Explicit nonnegative Bernstein remainder after subtracting 93/560. -/
lemma A6_remainder (a : ℝ) :
    A6 a - 93 / 560 = (1107 / 560) * (1 - a) ^ 5 +
      (675 / 112) * a * (1 - a) ^ 4 + (363 / 56) * a ^ 2 * (1 - a) ^ 3 +
      (407 / 112) * a ^ 3 * (1 - a) ^ 2 + (247 / 560) * a ^ 5 := by
  unfold A6
  ring

lemma A5_lower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 1 / 16 ≤ A5 a := by
  have hh : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hp : 0 ≤ A5 a - 1 / 16 := by rw [A5_remainder]; positivity
  linarith

lemma A6_lower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 93 / 560 ≤ A6 a := by
  have hh : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hp : 0 ≤ A6 a - 93 / 560 := by rw [A6_remainder]; positivity
  linarith

lemma upper_five_gap_identity (a : ℝ) :
    1 - 5 * a / 6 - ((1 - a) ^ 2 +
      5 * a ^ 2 * (∫ t in (0 : ℝ)..1, t * B a t ^ 2)) = a * (1 - a) * A5 a := by
  have he : (fun t => B a t) =
      (fun t => 1 + (-a * (1 + a)) * t + a ^ 2 * t ^ 2) := by
    funext t; unfold B; ring
  simp_rw [he]
  rw [integral_t_quadratic_sq]
  unfold A5
  ring

lemma upper_six_gap_identity (a : ℝ) :
    1 - 6 * a / 7 - ((1 - a) ^ 3 + 6 * a ^ 2 *
      ((∫ t in (0 : ℝ)..1, t * (1 - a * t) ^ 5) +
        (5 / 2 : ℝ) * a * (1 - a) *
          (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - a * t) ^ 3) +
        (15 / 32 : ℝ) * a ^ 2 * (1 - a) ^ 2)) = a * (1 - a) * A6 a := by
  rw [integral_t_linear_fifth, integral_sq_linear_cube]
  unfold A6
  ring

/-- The actual direct budget, with real exponents and the original QQ integrand. -/
noncomputable def T (m a x : ℝ) : ℝ :=
  QQ (a * x) (a ^ 2) 1 ^ (m / 2) +
    m * a ^ 2 * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ ((m - 1) / 2))

lemma T_five_gap {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    T 5 a x ≤ 1 - 5 * a / 6 - a * (1 - a) / 16 := by
  have hend := beta_B_bounds ha0.le ha1.le hx hx1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  have heB : B a 1 = 1 - a := by unfold B; ring
  have he := Real.rpow_le_rpow hend.1 hend.2.1 (by norm_num : (0 : ℝ) ≤ 5 / 2)
  rw [heB] at he
  have he2 := Real.rpow_le_rpow_of_exponent_ge (by linarith : 0 < 1 - a)
    (by linarith : 1 - a ≤ 1) (by norm_num : (2 : ℝ) ≤ 5 / 2)
  norm_num [Real.rpow_natCast] at he2
  have hi : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (2 : ℕ)) ≤
      ∫ t in (0 : ℝ)..1, t * (B a t) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by unfold QQ; fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold B; fun_prop) _ _)
    intro t ht
    have hb := beta_B_bounds ha0.le ha1.le hx hx1 ht.1 ht.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 hb.2.1 2) ht.1
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 5 * a ^ 2)
  have hg := upper_five_gap_identity a
  have hl := mul_le_mul_of_nonneg_left (A5_lower ha0.le ha1.le)
    (by positivity : 0 ≤ a * (1 - a))
  norm_num [T, Real.rpow_natCast]
  linarith

lemma T_six_gap {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hx : (1 + a) / 2 ≤ x) (hx1 : x ≤ 1) :
    T 6 a x ≤ 1 - 6 * a / 7 - (93 / 560) * a * (1 - a) := by
  have hend := beta_B_bounds ha0.le ha1.le hx hx1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  have heB : B a 1 = 1 - a := by unfold B; ring
  have he := pow_le_pow_left₀ hend.1 hend.2.1 3
  rw [heB] at he
  have hi : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (5 / 2 : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (t * (1 - a * t) ^ 5 +
        ((5 / 2 : ℝ) * a * (1 - a)) * (t ^ 2 * (1 - a * t) ^ 3) +
        ((15 / 8 : ℝ) * a ^ 2 * (1 - a) ^ 2) * t ^ 3) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by simpa only [pow_one] using
        (continuous_pow_mul_QQ (a * x) (a ^ 2) 1
          (by norm_num : (0 : ℝ) ≤ 5 / 2)).intervalIntegrable 0 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    have hb := beta_B_bounds ha0.le ha1.le hx hx1 ht.1 ht.2
    have hp := (Real.rpow_le_rpow hb.1 hb.2.1 (by norm_num : (0 : ℝ) ≤ 5 / 2)).trans
      (B_five_halves ha0.le ha1.le ht.1 ht.2)
    have hm := mul_le_mul_of_nonneg_left hp ht.1
    calc
      _ ≤ t * ((1 - a * t) ^ 5 + (5 / 2 : ℝ) * a * (1 - a) * t *
          (1 - a * t) ^ 3 + (15 / 8 : ℝ) * a ^ 2 * (1 - a) ^ 2 * t ^ 2) := hm
      _ = _ := by ring
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _)
    only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow] at hi
  norm_num at hi
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 6 * a ^ 2)
  have hg := upper_six_gap_identity a
  have hl := mul_le_mul_of_nonneg_left (A6_lower ha0.le ha1.le)
    (by positivity : 0 ≤ a * (1 - a))
  norm_num [T, Real.rpow_natCast]
  nlinarith only [he, hmul, hg, hl]

/-- General lower budget retaining the actual norm of J, without assuming it ≤ 1.
The explicit beta nonnegativity hypothesis permits reuse beyond the small degrees. -/
theorem lower_budget_norm {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 ≤ a)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I))
    (hβ : 0 ≤ QQ (a * x) (a ^ 2) 1) :
    1 ≤ T ((n : ℝ) - 1) a x + a * ((n : ℝ) - 1) / (n : ℝ) *
      ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hc : (q.card : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hqcard
    omega
  have hsumle := norm_sum_le_card q hq1
  rw [hc] at hsumle
  have ht := one_le_tri hn hqcard hq0 hq1 ha hx hsum
  have hf := norm_Fprod_le hn hqcard hq1 hx hβ
  have hcoef : ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) =
      (a : ℂ) * q.sum := by rw [hsum]; ring
  rw [hcoef] at ht
  have hi : ‖(a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ ≤
      a * ((n : ℝ) - 1) / (n : ℝ) *
        ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
      Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumle ha)
      (norm_nonneg (∫ t in (0 : ℝ)..1, Fprod a q t))
    have he : a * ((n : ℝ) - 1) / (n : ℝ) *
        ((n : ℝ) * ‖∫ t in (0 : ℝ)..1, Fprod a q t‖) =
        a * ((n : ℝ) - 1) * ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ := by
      field_simp
    rw [he]
    exact hm
  have htri := norm_add_le (Fprod a q 1)
    ((a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t))
  have hexp : (n : ℝ) - 1 - 1 = (n : ℝ) - 2 := by ring
  simp only [T, hexp]
  nlinarith only [ht, hf, hi, htri]

/-- Solved form of the general norm budget. No polar or first-origin upper bound
is needed; those hypotheses are not hidden in the beta nonnegativity proof. -/
theorem norm_J_lower {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (ha : 0 < a) (hx1 : x ≤ 1)
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ((1 - T ((n : ℝ) - 1) a x) * (n : ℝ)) / (a * ((n : ℝ) - 1)) ≤
      ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : 0 < (n : ℝ) - 1 := by linarith
  have hβ : 0 ≤ QQ (a * x) (a ^ 2) 1 := by
    have he : QQ (a * x) (a ^ 2) 1 = (1 - a) ^ 2 + 2 * a * (1 - x) := by
      unfold QQ; ring
    rw [he]
    have : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    positivity
  have hl := lower_budget_norm hn ha.le hqcard hq1 hx hsum hβ
  have hs : 1 - T ((n : ℝ) - 1) a x ≤ a * ((n : ℝ) - 1) / (n : ℝ) *
      ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by linarith
  have hmul := mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ n)
  have he : a * ((n : ℝ) - 1) / (n : ℝ) *
      ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ * (n : ℝ) =
      ‖(n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ * (a * ((n : ℝ) - 1)) := by
    field_simp
  rw [he] at hmul
  exact (div_le_iff₀ (mul_pos ha hm0)).mpr hmul

/-- The finite mean coordinates, proved solely from the pointwise closed disk. -/
lemma mean_coordinates {n : ℕ} (hn : 2 ≤ n) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    ∃ x y : ℝ, -1 ≤ x ∧ x ≤ 1 ∧
      (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x ∧
      q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 < (n : ℝ) - 1 := by linarith
  have hmC : (n : ℂ) - 1 ≠ 0 := by exact_mod_cast (ne_of_gt hm0)
  have hc : (q.card : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  let μ : ℂ := q.sum / ((n : ℂ) - 1)
  have hsum : q.sum = ((n : ℂ) - 1) * ((μ.re : ℂ) + (μ.im : ℂ) * Complex.I) := by
    rw [Complex.re_add_im]
    dsimp [μ]
    field_simp
  have hnc : ‖(n : ℂ) - 1‖ = (n : ℝ) - 1 := by
    have he : (n : ℂ) - 1 = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  have hqsum := norm_sum_le_card q hq1
  rw [hc] at hqsum
  have hμ : ‖μ‖ ≤ 1 := by
    dsimp [μ]
    rw [norm_div, hnc, div_le_iff₀ hm0]
    simpa using hqsum
  have hx0 : -1 ≤ μ.re := by
    have h := Complex.abs_re_le_norm μ
    exact (abs_le.mp (h.trans hμ)).1
  have hx1 : μ.re ≤ 1 := (Complex.re_le_norm μ).trans hμ
  have hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * μ.re := by
    have hre : (q.map (fun v => v.re)).sum = q.sum.re :=
      (map_multiset_sum Complex.reAddGroupHom q).symm
    rw [hre, hsum]
    simp
  exact ⟨μ.re, μ.im, hx0, hx1, hx, hsum⟩

/-- n = 6: a quantitative lower norm bound from pointwise disk plus polar alone. -/
theorem norm_J_six {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = 6 - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 + (3 / 40 : ℝ) * (1 - a) ≤
      ‖(6 : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  obtain ⟨x, y, hx0, hx1, hx, hsum⟩ := mean_coordinates (by norm_num : 2 ≤ 6) hqcard hq1
  have hpolar := one_le_integral_Ppolar (by norm_num : 2 ≤ 6) hqcard hq1 hx hstar
  have hxhalf := polar_mean_gt_half_add_one (Or.inl rfl : 6 = 6 ∨ 6 = 7) ha0 ha1 hx0 hpolar
  have hβ := (beta_B_bounds ha0.le ha1.le hxhalf.le hx1
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl).1
  have hl := lower_budget_norm (by norm_num : 2 ≤ 6) ha0.le hqcard hq1 hx hsum hβ
  have hg := T_five_gap ha0 ha1 hxhalf.le hx1
  norm_num at hl
  have hm : a * (1 + (3 / 40 : ℝ) * (1 - a)) ≤
      a * ‖(6 : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
    norm_num
    nlinarith only [hl, hg]
  exact (mul_le_mul_iff_right₀ ha0).mp hm

/-- n = 7: a quantitative lower norm bound from pointwise disk plus polar alone. -/
theorem norm_J_seven {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = 7 - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 + (31 / 160 : ℝ) * (1 - a) ≤
      ‖(7 : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
  obtain ⟨x, y, hx0, hx1, hx, hsum⟩ := mean_coordinates (by norm_num : 2 ≤ 7) hqcard hq1
  have hpolar := one_le_integral_Ppolar (by norm_num : 2 ≤ 7) hqcard hq1 hx hstar
  have hxhalf := polar_mean_gt_half_add_one (Or.inr rfl : 7 = 6 ∨ 7 = 7) ha0 ha1 hx0 hpolar
  have hβ := (beta_B_bounds ha0.le ha1.le hxhalf.le hx1
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl).1
  have hl := lower_budget_norm (by norm_num : 2 ≤ 7) ha0.le hqcard hq1 hx hsum hβ
  have hg := T_six_gap ha0 ha1 hxhalf.le hx1
  norm_num at hl
  have hm : a * (1 + (31 / 160 : ℝ) * (1 - a)) ≤
      a * ‖(7 : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ := by
    norm_num
    nlinarith only [hl, hg]
  exact (mul_le_mul_iff_right₀ ha0).mp hm

end Sendov.FirstOriginMargins
