import CoefficientBound
import Sendov.Analytic.PaperFactorialTail
import Sendov.Analytic.PaperCenteredTail
import Sendov.Analytic.CenteredNearChord
import Sendov.Analytic.CenteredNearEndpoint

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredActualTail
open PaperCentered PaperCenteredBound

/-- The original square-root majorant tail, with all actual finite endpoints. -/
def majorantTail (r : Multiset ℂ) (μ z : ℂ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (r.card+1),
    C r.card k (variance r) / ((r.card.choose k : ℝ)*‖μ‖^k) * ‖H r.card k z‖

lemma sqrt_nat_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x^n) = (Real.sqrt x)^n := by
  apply (Real.sqrt_eq_iff_mul_self_eq (pow_nonneg hx _) (pow_nonneg (Real.sqrt_nonneg _) _)).2
  rw [← mul_pow, Real.mul_self_sqrt hx]

/-- Actual-moment coupling before taking any scalar quadratic bound. -/
theorem norm_sq_add_variance_le_beta (r : Multiset ℂ) (μ : ℂ) (a t : ℝ)
    (hv : variance r ≤ 1 - ‖μ‖^2) :
    ‖1-(a : ℂ)*μ*t‖^2 + variance r * (a*t)^2 ≤ PaperPolar.beta a μ.re t := by
  have hid : ‖1-(a : ℂ)*μ*t‖^2 = 1-2*a*μ.re*t+a^2*t^2*‖μ‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    ring
  rw [hid]
  unfold PaperPolar.beta
  nlinarith only [mul_le_mul_of_nonneg_right hv (sq_nonneg (a*t))]

/-- Fully discharged coefficient hypothesis: the whole pointwise tail is
bounded using the variance of r, not an external coefficient table. -/
theorem pointwise_tail3 (r : Multiset ℂ) (hm : 3 ≤ r.card) (μ : ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hv : variance r ≤ 1 - ‖μ‖^2) :
    (∑ k ∈ Finset.Ico 3 (r.card+1),
      C r.card k (variance r) * (a*t)^k * ‖1-(a : ℂ)*μ*t‖^(r.card-k)) ≤
    (Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ)) * a^3 * Real.sqrt ((variance r)^3)) *
      (t^3 * (Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
  have hv0 : 0 ≤ variance r := PaperCoefficient.variance_nonneg _
  have h := PaperFactorialTail.coefficient_tail3_le r.card hm
    (fun k => C r.card k (variance r)) (variance r) (a*t) ‖1-(a : ℂ)*μ*t‖
    hv0 (mul_nonneg ha ht) (fun k _ => PaperBinomialMode.C_sq_le_binomial _ _ _ hv0)
  have hquad := norm_sq_add_variance_le_beta r μ a t hv
  have hA0 : 0 ≤ ‖1-(a : ℂ)*μ*t‖^2 + variance r*(a*t)^2 := by positivity
  have hb0 : 0 ≤ PaperPolar.beta a μ.re t := hA0.trans hquad
  have hs := Real.sqrt_le_sqrt (pow_le_pow_left₀ hA0 hquad (r.card-3))
  rw [sqrt_nat_pow _ hb0] at hs
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ)) * (a*t*Real.sqrt (variance r))^3 by positivity)
  calc
    _ ≤ _ := h
    _ ≤ _ := hmul
    _ = _ := by rw [sqrt_nat_pow _ hv0]; ring

/-- The normalized H tail is bounded by one finite-product integral before
any pointwise coefficient estimates are applied. -/
theorem majorantTail_le_integral (r : Multiset ℂ) (μ : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hμ : μ ≠ 0) :
    majorantTail r μ ((a : ℂ)*μ) ≤ ((r.card : ℝ)+1)*a*‖μ‖ *
      (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.Ico 3 (r.card+1),
        C r.card k (variance r)*(a*|t|)^k*‖1-(a : ℂ)*μ*t‖^(r.card-k)) := by
  have h := PaperCenteredTail.majorant_block_le_integral r 3 (a : ℂ) μ hμ
  change majorantTail r μ ((a : ℂ)*μ) ≤ _ at h
  apply h.trans_eq
  symm
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have he : (fun t : ℝ => C r.card k (variance r)*(a*|t|)^k*‖1-(a : ℂ)*μ*t‖^(r.card-k)) =
        (fun t : ℝ => (C r.card k (variance r)*a^k) * (|t|^k*‖1-(a : ℂ)*μ*t‖^(r.card-k))) := by
      funext t
      rw [mul_pow]
      ring
    rw [he, intervalIntegral.integral_const_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, pow_succ]
    ring
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop

/-- The actual square-root-C tail obeys the uniform cubic weighted integral
bound. There is no remaining coefficient-bound hypothesis. -/
theorem majorantTail_le_cubicIntegral (r : Multiset ℂ) (hm : 3 ≤ r.card) (μ : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hμ : μ ≠ 0) (hv : variance r ≤ 1 - ‖μ‖^2) :
    majorantTail r μ ((a : ℂ)*μ) ≤
      (((r.card : ℝ)+1)*a^4*‖μ‖*Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ))*
        Real.sqrt ((variance r)^3)) *
      (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
  let K := Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ))*a^3*Real.sqrt ((variance r)^3)
  have hi : (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.Ico 3 (r.card+1),
        C r.card k (variance r)*(a*|t|)^k*‖1-(a : ℂ)*μ*t‖^(r.card-k)) ≤
      ∫ t in (0 : ℝ)..1, K*(t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
    intro t ht
    rw [abs_of_nonneg ht.1]
    exact pointwise_tail3 r hm μ a t ha ht.1 hv
  rw [intervalIntegral.integral_const_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ ((r.card : ℝ)+1)*a*‖μ‖)
  calc
    _ ≤ _ := majorantTail_le_integral r μ a ha hμ
    _ ≤ _ := hscaled
    _ = _ := by dsimp [K]; ring

/-- The analytic tail is bounded by the explicit scalar used in near closure. -/
theorem majorantTail_le_tailScalar (r : Multiset ℂ) (hm : 7 ≤ r.card) (μ : ℂ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hμ : μ ≠ 0) (hu : ‖μ‖ ≤ 1)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hv : variance r ≤ 1 - ‖μ‖^2)
    (hb : PaperPolar.b a μ.re ≤ CenteredNearScalar.rho^2) :
    majorantTail r μ ((a : ℂ)*μ) ≤ CenteredNearScalar.tailScalar r.card (variance r) := by
  let M : ℝ := r.card
  let D : ℝ := M*(M-1)*(M-2)
  let I : ℝ := ∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)
  have hM : 7 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM2 : 0 < M-2 := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hI0 : 0 ≤ I := by
    apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    intro t ht
    exact mul_nonneg (pow_nonneg ht.1 _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hc : (r.card.descFactorial 3 : ℝ) = D :=
    PaperFactorialTail.cast_descFactorial_three r.card (by omega)
  have hs : Real.sqrt ((9/4)*(r.card.descFactorial 3 : ℝ)) = (3/2)*Real.sqrt D := by
    have hroot : Real.sqrt (9/4 : ℝ) = 3/2 :=
      (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
    rw [hc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9/4), hroot]
  have htail := majorantTail_le_cubicIntegral r (by omega) μ a ha0 hμ hv
  rw [hs] at htail
  have hau : a^4*‖μ‖ ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ ha0 ha1) (norm_nonneg _) hu
  have hscale := mul_le_mul_of_nonneg_right hau
    (show 0 ≤ (M+1)*(3/2)*Real.sqrt D*Real.sqrt ((variance r)^3)*I by positivity)
  have ht : majorantTail r μ ((a : ℂ)*μ) ≤
      ((M+1)*(3/2)*Real.sqrt D*Real.sqrt ((variance r)^3))*I := by
    change majorantTail r μ ((a : ℂ)*μ) ≤
      ((M+1)*a^4*‖μ‖*((3/2)*Real.sqrt D)*Real.sqrt ((variance r)^3))*I at htail
    nlinarith only [htail, hscale]
  have hib := CenteredNearScalar.cubic_beta_integral r.card hm a μ.re ha0 ha1 hx0 hx1 hb
  have hden : 0 < (M+1)*D*(9/11 : ℝ)^4 := by positivity
  have hi : I ≤ 6 / ((M+1)*D*(9/11 : ℝ)^4) := by
    apply (le_div_iff₀ hden).2
    change (M+1)*M*(M-1)*(M-2)*(9/11 : ℝ)^4*I ≤ 6 at hib
    dsimp [D]
    nlinarith only [hib]
  have hmul := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (M+1)*(3/2)*Real.sqrt D*Real.sqrt ((variance r)^3) by positivity)
  apply ht.trans
  apply hmul.trans_eq
  unfold CenteredNearScalar.tailScalar
  change ((M+1)*(3/2)*Real.sqrt D*Real.sqrt ((variance r)^3)) *
    (6 / ((M+1)*D*(9/11 : ℝ)^4)) = 9*Real.sqrt ((variance r)^3/D)/(9/11 : ℝ)^4
  rw [Real.sqrt_div' _ hD0.le]
  have hsn : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
  have hmn : M+1 ≠ 0 := by positivity
  field_simp
  have he := Real.sq_sqrt hD0.le
  nlinarith only [congrArg (fun x : ℝ => x*Real.sqrt ((variance r)^3)) he]

end Sendov.CenteredActualTail
