import Sendov.Analytic.PaperTaylor
import Sendov.Analytic.PaperPolar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Conjugate-pair full polar and a finite split bound for the actual T integral.
No centered budget or numerical quadrature is used. -/
namespace Sendov.PaperLegacy
open MeasureTheory
open scoped BigOperators

noncomputable def pair (x : ℝ) (j : Fin 2) : ℂ :=
  ⟨x, if j.val = 0 then Real.sqrt (1 - x ^ 2) else -Real.sqrt (1 - x ^ 2)⟩
noncomputable def q (n : ℕ) (x : ℝ) (j : Fin n × Fin 2) : ℂ := pair x j.2
noncomputable def P (a x t : ℝ) :=
  a ^ 2 + 2 * a * (1 - a ^ 2) * x * t + (1 - a ^ 2) ^ 2 * t ^ 2
noncomputable def R (n : ℕ) (a x : ℝ) := ∫ t in (0 : ℝ)..1, P a x t ^ n
noncomputable def K (n : ℕ) (a x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ∏ j : Fin n × Fin 2,
    ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q n x j)

lemma pair_norm {x : ℝ} (hx : x ^ 2 ≤ 1) (j : Fin 2) : ‖pair x j‖ = 1 := by
  have hy := Real.sq_sqrt (sub_nonneg.mpr hx)
  have h : ‖pair x j‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    fin_cases j <;> simp [pair] <;> nlinarith
  nlinarith [norm_nonneg (pair x j)]

theorem norm_q {n : ℕ} {x : ℝ} (hx : x ^ 2 ≤ 1) (j : Fin n × Fin 2) :
    ‖q n x j‖ = 1 := pair_norm hx j.2

/-- The scalar parameter is exactly the real part of the family's mean. -/
theorem mean_re {n : ℕ} (hn : 0 < n) (x : ℝ) :
    ((∑ j : Fin n × Fin 2, q n x j) / (2 * n : ℂ)).re = x := by
  have hpair : (∑ j : Fin 2, pair x j) = 2 * (x : ℂ) := by
    apply Complex.ext <;> simp [Fin.sum_univ_succ, pair] <;> ring
  rw [Fintype.sum_prod_type]
  simp only [q, hpair, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (n : ℂ) * (2 * x) / (2 * n) = x := by field_simp
  rw [he, Complex.ofReal_re]

lemma pair_product {x : ℝ} (hx : x ^ 2 ≤ 1) (s r : ℝ) :
    (∏ j : Fin 2, ((s : ℂ) + r * pair x j)) =
      ((s ^ 2 + 2 * s * r * x + r ^ 2 : ℝ) : ℂ) := by
  have hy := Real.sq_sqrt (sub_nonneg.mpr hx)
  simp only [Fin.prod_univ_succ]
  apply Complex.ext <;> simp [pair, pow_two]
  · simp only [pow_two] at hy
    nlinarith [congrArg (fun z : ℝ => r ^ 2 * z) hy]
  · ring

lemma product_eq {x : ℝ} (hx : x ^ 2 ≤ 1) (n : ℕ) (a t : ℝ) :
    (∏ j : Fin n × Fin 2, ((a : ℂ) + ((1 - a ^ 2) * t : ℝ) * q n x j)) =
      ((P a x t ^ n : ℝ) : ℂ) := by
  rw [Fintype.prod_prod_type]
  simp only [q, pair_product hx]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  congr 1
  unfold P
  push_cast
  ring

/-- Literal full complex K equals the real polynomial integral for all pair counts. -/
theorem K_eq_R {x : ℝ} (hx : x ^ 2 ≤ 1) (n : ℕ) (a : ℝ) : K n a x = (R n a x : ℂ) := by
  unfold K R
  simp_rw [product_eq hx]
  rw [intervalIntegral.integral_ofReal]

lemma norm_K_eq {x : ℝ} (hx : x ^ 2 ≤ 1) (n : ℕ) (a : ℝ)
    (hr : 0 ≤ R n a x) : ‖K n a x‖ = R n a x := by
  rw [K_eq_R hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

lemma raw_even (n : ℕ) (a x : ℝ) : PaperPolar.RawPolar (2 * n) a x ↔ 1 ≤ R n a x := by
  unfold PaperPolar.RawPolar R P
  push_cast
  rw [show (2 * (n : ℝ)) / 2 = n by ring]
  simp only [Real.rpow_natCast]

/-- Finite polynomial integral from an explicitly verified coefficient identity. -/
lemma integral_coefficients (N : ℕ) (c : Fin N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ k : Fin N, c k * t ^ k.val) :
    (∫ t in (0 : ℝ)..1, f t) = ∑ k : Fin N, c k / (k.val + 1) := by
  simp_rw [hf]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  · intro k hk
    exact (continuous_const.mul (continuous_pow k.val)).intervalIntegrable _ _

/-- A finite split, a left chord extended only to its zero, and a bounded right tail.
The natural exponent on the tail rounds DOWN the actual half-integer exponent. -/
lemma budget_split_le {m a x s c r : ℝ} {n : ℕ}
    (hm : 7 ≤ m) (ha : 0 < a) (ha1 : a < 1) (hx : x ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hsc : s ≤ 1 / c)
    (hr : 0 < r) (hr1 : r ≤ 1) (hn : (n : ℝ) ≤ (m - 1) / 2)
    (hl : ∀ t ∈ Set.Icc (0 : ℝ) s, PaperTaylor.beta a x t ≤ 1 - c * t)
    (htail : ∀ t ∈ Set.Icc s 1, PaperTaylor.beta a x t ≤ r) :
    PaperTaylor.budget m a x ≤ PaperTaylor.beta a x 1 ^ (m / 2) + m * a ^ 2 *
      (1 / (c ^ 2 * (((m - 1) / 2 + 1) * ((m - 1) / 2 + 2))) +
        r ^ n * ((1 - s ^ 2) / 2)) := by
  let p := (m - 1) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  have hf : Continuous (fun t : ℝ => t * PaperTaylor.beta a x t ^ p) :=
    continuous_id.mul ((continuous_rpow_const hp.le).comp (by unfold PaperTaylor.beta; fun_prop))
  have hg : Continuous (fun t : ℝ => t * (1 - c * t) ^ p) :=
    continuous_id.mul ((continuous_rpow_const hp.le).comp (by fun_prop))
  have hleft : (∫ t in (0 : ℝ)..s, t * PaperTaylor.beta a x t ^ p) ≤
      1 / (c ^ 2 * ((p + 1) * (p + 2))) := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hs (hf.intervalIntegrable 0 s)
      (hg.intervalIntegrable 0 s) (fun t ht =>
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (PaperTaylor.beta_pos ha ha1 hx ⟨ht.1, ht.2.trans hs1⟩).le (hl t ht) hp.le) ht.1)
    have hrest : 0 ≤ ∫ t in s..1 / c, t * (1 - c * t) ^ p := by
      apply intervalIntegral.integral_nonneg hsc
      intro t ht
      have := (le_div_iff₀ hc).mp ht.2
      exact mul_nonneg (hs.trans ht.1) (Real.rpow_nonneg (by nlinarith) _)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hg.intervalIntegrable 0 s) (hg.intervalIntegrable s (1 / c))
    rw [integral_chord_lin hp hc] at hadd
    linarith
  have hright : (∫ t in s..1, t * PaperTaylor.beta a x t ^ p) ≤
      r ^ n * ((1 - s ^ 2) / 2) := by
    have hpow : r ^ p ≤ r ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hn
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hs1 (hf.intervalIntegrable s 1)
      ((by fun_prop : Continuous (fun t : ℝ => r ^ n * t)).intervalIntegrable s 1)
      (fun t ht => by
        have ht0 := hs.trans ht.1
        have h := (Real.rpow_le_rpow (PaperTaylor.beta_pos ha ha1 hx ⟨ht0, ht.2⟩).le
          (htail t ht) hp.le).trans hpow
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left h ht0)
    rw [intervalIntegral.integral_const_mul, integral_id] at hmono
    simpa using hmono
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s 1)
  have hi : (∫ t in (0 : ℝ)..1, t * PaperTaylor.beta a x t ^ p) ≤
      1 / (c ^ 2 * ((p + 1) * (p + 2))) + r ^ n * ((1 - s ^ 2) / 2) := by
    rw [← hadd]
    exact add_le_add hleft hright
  have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ m * a ^ 2 by positivity)
  exact add_le_add le_rfl h

end Sendov.PaperLegacy
