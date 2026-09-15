import Sendov.Analytic.FirstOriginBounds

/-! Actual Fprod and first-origin consumers for n = 6 or n = 7.
All root norm hypotheses are closed (at most one). -/

namespace Sendov.FirstOriginSmall

lemma norm_sum_le_card (q : Multiset ℂ) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    ‖q.sum‖ ≤ (q.card : ℝ) := by
  refine (norm_multiset_sum_le q).trans ?_
  simpa using Multiset.sum_map_le_sum_map (fun v : ℂ => ‖v‖) (fun _ => (1 : ℝ)) hq1

lemma norm_Fprod_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hb : 0 ≤ QQ (a * x) (a ^ 2) t) :
    ‖Fprod a q t‖ ≤ QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 1) / 2) := by
  have hc : (q.card : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcpos : (0 : ℝ) < q.card := by rw [hc]; linarith
  let f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖
  have hsum := sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx (t := t) (a := a)
  have ham := Multiset.prod_le_mean_pow (q.map (fun v => (f v) ^ 2)) (by
    intro y hy
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq] at ham
  have hmean : (q.map (fun v => (f v) ^ 2)).sum / (q.card : ℝ) ≤ QQ (a * x) (a ^ 2) t := by
    rw [div_le_iff₀ hcpos, hc]
    simpa only [f, mul_comm] using hsum
  have hmean0 : 0 ≤ (q.map (fun v => (f v) ^ 2)).sum / (q.card : ℝ) := by
    apply div_nonneg _ hcpos.le
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg _
  have hprod := ham.trans (pow_le_pow_left₀ hmean0 hmean q.card)
  have heq : (QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 1) / 2)) ^ 2 = QQ (a * x) (a ^ 2) t ^ q.card := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb, ← Real.rpow_natCast _ q.card, hc]
    congr 1
    norm_num
  have hf : ‖Fprod a q t‖ = (q.map f).prod := norm_prod_map q _
  rw [hf]
  apply (sq_le_sq₀ (prod_map_norm_nonneg q _) (Real.rpow_nonneg hb _)).mp
  rw [heq]
  exact hprod

lemma norm_integral_Fprod_le_of_first_origin {n : ℕ} (hn : 0 < n)
    {a : ℝ} {q z : Multiset ℂ}
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hz1 : ∀ v ∈ z, ‖v‖ ≤ 1)
    (hfirst : (n : ℂ) * (∫ t in (0 : ℝ)..1, Fprod a q t) =
      (-1) ^ (n - 1) * q.prod * z.prod) :
    ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpq : ‖q.prod‖ ≤ 1 := by
    rw [norm_multiset_prod]
    exact prod_norm_le_one q hq1
  have hpz : ‖z.prod‖ ≤ 1 := by
    rw [norm_multiset_prod]
    exact prod_norm_le_one z hz1
  have hnorm := congrArg norm hfirst
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at hnorm
  rw [le_div_iff₀ hnR]
  have hp := mul_le_mul hpq hpz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith only [hnorm, hp]

lemma first_origin_polar_six_seven_core
    {n : ℕ} (hn : n = 6 ∨ n = 7) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod)
    (hfirst_bound : ‖∫ t in (0 : ℝ)..1, Sendov.Fprod a q t‖ ≤ 1 / (n : ℝ)) :
    False := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hm0 : 0 < (n : ℝ) - 1 := by linarith
  have hmC : (n : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt hm0)
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
  have hpolar := one_le_integral_Ppolar hn2 hqcard hq1 hx hstar
  have hxhalf := polar_mean_gt_half_add_one hn ha0 ha1 hx0 hpolar
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hqcard
    omega
  have ht := one_le_tri hn2 hqcard hq0 hq1 ha0.le hx hsum
  have hβ := (beta_B_bounds ha0.le ha1.le hxhalf.le hx1
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl).1
  have hf := norm_Fprod_le hn2 hqcard hq1 hx hβ
  have hcoef : ((n : ℂ) - 1) * (a : ℂ) * ((μ.re : ℂ) + (μ.im : ℂ) * Complex.I) = (a : ℂ) * q.sum := by
    rw [hsum]; ring
  rw [hcoef] at ht
  have hi : ‖(a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t)‖ ≤
      a * ((n : ℝ) - 1) / (n : ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hqsum ha0.le) hfirst_bound
      (norm_nonneg _) (by positivity : 0 ≤ a * ((n : ℝ) - 1))
    simpa only [mul_one_div] using hmul
  have htri := norm_add_le (Fprod a q 1) ((a : ℂ) * q.sum * (∫ t in (0 : ℝ)..1, Fprod a q t))
  rcases hn with rfl | rfl
  · have hb := direct_budget_five ha0 ha1 hxhalf.le hx1
    norm_num [Real.rpow_natCast] at ht hf hi htri
    linarith
  · have hb := direct_budget_six ha0 ha1 hxhalf.le hx1
    norm_num [Real.rpow_natCast] at ht hf hi htri
    linarith

theorem first_origin_polar_six_seven
    {n : ℕ} (hn : n = 6 ∨ n = 7) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod)
    (hfirst_bound : ‖∫ t in (0 : ℝ)..1, Sendov.Fprod a q t‖ ≤ 1 / (n : ℝ)) :
    False := by
  exact first_origin_polar_six_seven_core hn ha0 ha1 hqcard hq1 hstar hfirst_bound

theorem norm_integral_Fprod_le_of_factorization
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : a ≠ 0)
    {c : ℂ} (hc0 : c ≠ 0) {p : Polynomial ℂ} {q z : Multiset ℂ}
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hz1 : ∀ v ∈ z, ‖v‖ ≤ 1)
    (hpa : p.eval (a : ℂ) = 0)
    (hpz : p = Polynomial.C c * ((Polynomial.X - Polynomial.C (a : ℂ)) * (z.map (fun w => Polynomial.X - Polynomial.C w)).prod))
    (hpq : Polynomial.derivative p = Polynomial.C ((n : ℂ) * c) * ((q.map (fun v => (a : ℂ) - v⁻¹)).map
        (fun w => Polynomial.X - Polynomial.C w)).prod) :
    ‖∫ t in (0 : ℝ)..1, Fprod a q t‖ ≤ 1 / (n : ℝ) := by
  apply norm_integral_Fprod_le_of_first_origin hn hq1 hz1
  exact first_origin_identity hc0 (Complex.ofReal_ne_zero.mpr ha0) hzcard hq0 hpa hpz hpq


end Sendov.FirstOriginSmall
