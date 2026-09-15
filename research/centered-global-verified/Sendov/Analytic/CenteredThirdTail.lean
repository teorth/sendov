import Sendov.Analytic.CenteredChordGeneral
import Sendov.Analytic.CenteredQuarterTheorem

noncomputable section
open scoped BigOperators
namespace Sendov.CenteredThird
open PaperCentered PaperCenteredBound CenteredActualTail

/-- Exact reciprocal-factorial weight sum, not its infinite upper bound. -/
def weightSum (m : ℕ) : ℝ :=
  9/4 - 2/((m:ℝ)-1) - 1/(2*(m:ℝ)*((m:ℝ)-1))

def eta (m : ℕ) : ℝ := (2/3)*Real.sqrt (weightSum m)

lemma weightSum_nonneg (m : ℕ) (hm : 3 ≤ m) : 0 ≤ weightSum m := by
  rw [weightSum, ← PaperFactorialTail.weight3_sum m hm]
  apply Finset.sum_nonneg
  intro k hk
  positivity

lemma eta_nonneg (m : ℕ) : 0 ≤ eta m := by unfold eta; positivity

/-- Fully discharged coefficient hypothesis: the whole pointwise tail is
bounded using the variance of r, not an external coefficient table. -/
theorem pointwise_tail3_finite (r : Multiset ℂ) (hm : 3 ≤ r.card) (μ : ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hv : variance r ≤ 1 - ‖μ‖^2) :
    (∑ k ∈ Finset.Ico 3 (r.card+1),
      C r.card k (variance r) * (a*t)^k * ‖1-(a : ℂ)*μ*t‖^(r.card-k)) ≤
    (Real.sqrt (weightSum r.card*(r.card.descFactorial 3 : ℝ)) * a^3 * Real.sqrt ((variance r)^3)) *
      (t^3 * (Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
  have hv0 : 0 ≤ variance r := PaperCoefficient.variance_nonneg _
  have h := PaperFactorialTail.coefficient_tail_le r.card 3 hm
    (fun k => C r.card k (variance r)) (variance r) (a*t) ‖1-(a : ℂ)*μ*t‖
    (weightSum r.card) hv0 (mul_nonneg ha ht) (weightSum_nonneg r.card hm)
    (fun k _ => PaperBinomialMode.C_sq_le_binomial _ _ _ hv0)
    (le_of_eq (PaperFactorialTail.weight3_sum r.card hm))
  have hquad := norm_sq_add_variance_le_beta r μ a t hv
  have hA0 : 0 ≤ ‖1-(a : ℂ)*μ*t‖^2 + variance r*(a*t)^2 := by positivity
  have hb0 : 0 ≤ PaperPolar.beta a μ.re t := hA0.trans hquad
  have hs := Real.sqrt_le_sqrt (pow_le_pow_left₀ hA0 hquad (r.card-3))
  rw [sqrt_nat_pow _ hb0] at hs
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Real.sqrt (weightSum r.card*(r.card.descFactorial 3 : ℝ)) * (a*t*Real.sqrt (variance r))^3 by positivity)
  calc
    _ ≤ _ := h
    _ ≤ _ := hmul
    _ = _ := by rw [sqrt_nat_pow _ hv0]; ring

/-- The actual square-root-C tail obeys the exact finite-weight cubic integral
bound. There is no remaining coefficient-bound hypothesis. -/
theorem majorantTail_le_cubicIntegral_finite (r : Multiset ℂ) (hm : 3 ≤ r.card) (μ : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hμ : μ ≠ 0) (hv : variance r ≤ 1 - ‖μ‖^2) :
    majorantTail r μ ((a : ℂ)*μ) ≤
      (((r.card : ℝ)+1)*a^4*‖μ‖*Real.sqrt (weightSum r.card*(r.card.descFactorial 3 : ℝ))*
        Real.sqrt ((variance r)^3)) *
      (∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
  let K := Real.sqrt (weightSum r.card*(r.card.descFactorial 3 : ℝ))*a^3*Real.sqrt ((variance r)^3)
  have hi : (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.Ico 3 (r.card+1),
        C r.card k (variance r)*(a*|t|)^k*‖1-(a : ℂ)*μ*t‖^(r.card-k)) ≤
      ∫ t in (0 : ℝ)..1, K*(t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by unfold PaperPolar.beta; fun_prop) _ _)
    intro t ht
    rw [abs_of_nonneg ht.1]
    exact pointwise_tail3_finite r hm μ a t ha ht.1 hv
  rw [intervalIntegral.integral_const_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ ((r.card : ℝ)+1)*a*‖μ‖)
  calc
    _ ≤ _ := majorantTail_le_integral r μ a ha hμ
    _ ≤ _ := hscaled
    _ = _ := by dsimp [K]; ring

/-- A uniform, all-degree closed chord bound for the original majorant tail.
It retains a^4 and the actual norm of the mean. -/
theorem majorantTail_le_finiteChord (r : Multiset ℂ) (hm : 7 ≤ r.card) (μ : ℂ) (a c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hμ : μ ≠ 0)
    (hx0 : -1 ≤ μ.re) (hx1 : μ.re ≤ 1) (hv : variance r ≤ 1 - ‖μ‖^2)
    (hc : 0 < c) (hc1 : c ≤ 1) (hb : PaperPolar.b a μ.re ≤ (1-c)^2) :
    majorantTail r μ ((a : ℂ)*μ) ≤
      9*eta r.card*a^4*‖μ‖*Real.sqrt ((variance r)^3) /
        (c^4*Real.sqrt ((r.card : ℝ)*((r.card : ℝ)-1)*((r.card : ℝ)-2))) := by
  let M : ℝ := r.card
  let D : ℝ := M*(M-1)*(M-2)
  let I : ℝ := ∫ t in (0 : ℝ)..1, t^3*(Real.sqrt (PaperPolar.beta a μ.re t))^(r.card-3)
  have hM : 7 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM2 : 0 < M-2 := by linarith
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hdesc : (r.card.descFactorial 3 : ℝ) = D :=
    PaperFactorialTail.cast_descFactorial_three r.card (by omega)
  have hs : Real.sqrt (weightSum r.card*(r.card.descFactorial 3 : ℝ)) = ((3/2)*eta r.card)*Real.sqrt D := by
    rw [hdesc, Real.sqrt_mul (weightSum_nonneg r.card (by omega))]
    unfold eta
    ring
  have heta := eta_nonneg r.card
  have ht := majorantTail_le_cubicIntegral_finite r (by omega) μ a ha0 hμ hv
  rw [hs] at ht
  have hib := CenteredChordGeneral.cubic_beta_integral r.card hm a μ.re c ha0 ha1 hx0 hx1 hc hc1 hb
  have hden : 0 < (M+1)*D*c^4 := by positivity
  have hi : I ≤ 6/((M+1)*D*c^4) := by
    apply (le_div_iff₀ hden).2
    change (M+1)*M*(M-1)*(M-2)*c^4*I ≤ 6 at hib
    dsimp [D]
    nlinarith only [hib]
  have hmul := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (M+1)*a^4*‖μ‖*(((3/2)*eta r.card)*Real.sqrt D)*Real.sqrt ((variance r)^3) by positivity)
  apply ht.trans
  apply hmul.trans_eq
  change ((M+1)*a^4*‖μ‖*(((3/2)*eta r.card)*Real.sqrt D)*Real.sqrt ((variance r)^3)) *
      (6/((M+1)*D*c^4)) = 9*eta r.card*a^4*‖μ‖*Real.sqrt ((variance r)^3)/(c^4*Real.sqrt D)
  have hsn : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
  have hmn : M+1 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt hD0.le]
  ring


end Sendov.CenteredThird
